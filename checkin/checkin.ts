import { Plugin, type PanelSettingsAdapter, type PanelSettingField } from "@utils/pluginBase";
import { getGlobalClient } from "@utils/runtimeManager";
import { getPrefixes } from "@utils/pluginManager";
import { createDirectoryInAssets } from "@utils/pathHelpers";
import { htmlEscape as escape } from "@utils/htmlEscape";
import { Api, TelegramClient } from "teleproto";
import * as fs from "fs";
import * as path from "path";
import * as https from "https";

interface SignTarget {
  id: string;
  name: string;
  target: string;
  command: string;
  callbackData?: string;
  buttonText?: string;
  enabled: boolean;
}

interface CheckInConfig {
  runTime: string;
  runTimeEnd?: string;
  randomDelay: number;
  logChat: string;
  botToken: string;
  pushChatId: string;
  /** 最近一次执行的窗口日期 YYYY-MM-DD（上海时间） */
  lastRunDate: string;
  /** 下一次计划执行的时间戳与其窗口日期 */
  nextRunAt?: number;
  nextRunDate?: string;
  targets: SignTarget[];
}

interface PendingAdd {
  promptMsgId: number;
  senderId: string;
  expiresAt: number;
  target: Omit<SignTarget, "command" | "enabled">;
}

type SignResult = { success: boolean; message: string };
type Matcher = Pick<SignTarget, "callbackData" | "buttonText">;

const DEFAULT_CONFIG: CheckInConfig = {
  runTime: "10:00",
  runTimeEnd: "11:30",
  randomDelay: 0,
  logChat: "",
  botToken: "",
  pushChatId: "",
  lastRunDate: "",
  targets: [],
};

const PREFIX = getPrefixes()[0] || ".";
const SH_TZ = "Asia/Shanghai";
const MAX_DELAY = 60;
const PENDING_TTL = 10 * 60_000;
const REPLY_TIMEOUT = 10_000;
const MAX_TEXT = 3800;

// #region schedule（纯函数）
const TZ_OFFSET = 8 * 3600_000; // Asia/Shanghai 无夏令时
const DAY = 86400_000;
const TIME_RE = /^([01]?\d|2[0-3]):([0-5]\d)$/;

function parseTime(v: string | undefined): number | null {
  const m = TIME_RE.exec((v || "").trim());
  return m ? Number(m[1]) * 60 + Number(m[2]) : null;
}

function formatTime(minutes: number): string {
  return `${String(Math.floor(minutes / 60)).padStart(2, "0")}:${String(minutes % 60).padStart(2, "0")}`;
}

function shDate(ts: number): string {
  return new Date(ts + TZ_OFFSET).toISOString().slice(0, 10);
}

function shMidnight(date: string): number {
  return Date.parse(`${date}T00:00:00Z`) - TZ_OFFSET;
}

/** 某日的执行窗口 [start, end]，结束早于开始表示跨天 */
function windowOf(date: string, runTime: string, runTimeEnd?: string): [number, number] {
  const base = shMidnight(date);
  const start = parseTime(runTime) ?? 600;
  let end = parseTime(runTimeEnd) ?? start;
  if (end < start) end += 24 * 60;
  return [base + start * 60_000, base + end * 60_000];
}

/** 在 now 之后、尚未执行过的最近窗口里随机取一个整分钟，再叠加随机延迟 */
function planNextRun(
  now: number,
  conf: Pick<CheckInConfig, "runTime" | "runTimeEnd" | "randomDelay" | "lastRunDate">,
  rand: () => number = Math.random,
): { at: number; date: string } {
  const today = shMidnight(shDate(now));
  for (let offset = -1; offset <= 2; offset++) {
    const date = shDate(today + offset * DAY);
    if (conf.lastRunDate && date <= conf.lastRunDate) continue;
    const [start, end] = windowOf(date, conf.runTime, conf.runTimeEnd);
    const lower = Math.max(start, Math.ceil((now + 1) / 60_000) * 60_000);
    if (lower > end) continue;
    const slot = lower + Math.floor(rand() * ((end - lower) / 60_000 + 1)) * 60_000;
    const delay = Math.floor(rand() * Math.max(0, conf.randomDelay) * 60_000);
    return { at: slot + delay, date };
  }
  throw new Error("无法计算下一次执行时间");
}

/** 已到点：同一天内补签，隔天则跳过 */
function dueState(now: number, at: number): "wait" | "run" | "missed" {
  if (now < at) return "wait";
  return shDate(now) === shDate(at) ? "run" : "missed";
}
// #endregion

/** 兼容旧版写入的 2026/10/1 */
function normalizeDate(v: unknown): string {
  const m = /^(\d{4})[-/](\d{1,2})[-/](\d{1,2})$/.exec(String(v || ""));
  return m ? `${m[1]}-${m[2].padStart(2, "0")}-${m[3].padStart(2, "0")}` : "";
}

function validateTargets(raw: unknown): SignTarget[] {
  if (!Array.isArray(raw)) throw new Error("签到目标必须是 JSON 数组");
  const ids = new Set<string>();
  return raw.map((item: Record<string, unknown> | null, i) => {
    const s = (k: string) => (typeof item?.[k] === "string" ? (item[k] as string).trim() : "");
    const t: SignTarget = { id: s("id"), name: s("name"), target: s("target"), command: s("command"), enabled: item?.enabled !== false };
    if (!t.id || !t.name || !t.target || !t.command) throw new Error(`第 ${i + 1} 项缺少 id/name/target/command`);
    if (ids.has(t.id)) throw new Error(`重复的 ID: ${t.id}`);
    ids.add(t.id);
    if (s("callbackData")) t.callbackData = s("callbackData");
    else if (s("buttonText")) t.buttonText = s("buttonText");
    return t;
  });
}

function parseMatcher(args: string[]): Matcher {
  const raw = args.join(" ").trim();
  if (!raw) return {};
  if (raw.startsWith("text:")) return { buttonText: raw.slice(5).trim() };
  return { callbackData: raw.replace(/^data:/, "").trim() };
}

function hasMatcher(t: SignTarget): boolean {
  return !!(t.callbackData || t.buttonText);
}

/** layer 229：回调数据在 KeyboardInlineButton.type（InlineButtonTypeCallback）上 */
function findCallbackData(msg: Api.Message, target: SignTarget): Buffer | undefined {
  const markup = msg.replyMarkup;
  if (!(markup instanceof Api.ReplyInlineMarkup)) return undefined;
  for (const row of markup.rows) {
    for (const b of row.buttons) {
      if (!(b.type instanceof Api.InlineButtonTypeCallback)) continue;
      const hit = target.callbackData
        ? Buffer.from(b.type.data).toString("utf-8") === target.callbackData
        : b.text === target.buttonText;
      if (hit) return b.type.data;
    }
  }
  return undefined;
}

function errorText(e: unknown): string {
  if (e instanceof Error) return (e as Error & { errorMessage?: string }).errorMessage || e.message;
  return String(e);
}

function clip(s: string, n: number): string {
  return s.length > n ? `${s.slice(0, n)}…` : s;
}

function sleep(ms: number): Promise<void> {
  return new Promise((r) => setTimeout(r, ms));
}

function formatTs(ts: number): string {
  return new Date(ts).toLocaleString("zh-CN", { timeZone: SH_TZ });
}

function sendViaBot(token: string, chatId: string, text: string): Promise<void> {
  return new Promise((resolve, reject) => {
    const body = JSON.stringify({ chat_id: chatId, text, parse_mode: "HTML", disable_web_page_preview: true });
    const req = https.request(
      `https://api.telegram.org/bot${token}/sendMessage`,
      { method: "POST", timeout: 15_000, headers: { "Content-Type": "application/json", "Content-Length": Buffer.byteLength(body) } },
      (res) => {
        let out = "";
        res.on("data", (c) => (out += c));
        res.on("end", () => (res.statusCode === 200 ? resolve() : reject(new Error(`Bot API ${res.statusCode}: ${clip(out, 200)}`))));
      },
    );
    req.on("timeout", () => req.destroy(new Error("Bot API 请求超时")));
    req.on("error", reject);
    req.end(body);
  });
}

function helpText(): string {
  return `<b>✅ CheckIn 自动签到</b>

<b>基础</b>
<code>${PREFIX}checkin</code> 立即执行全部签到
<code>${PREFIX}checkin settings</code> 查看配置和下次执行时间
<code>${PREFIX}checkin reset</code> 重置今日状态并重新排期

<b>目标</b>
<code>${PREFIX}checkin add [ID] [名称] [目标] [data:回调|text:按钮]</code> 然后<b>回复提示消息</b>发送签到命令
<code>${PREFIX}checkin del [ID]</code>
<code>${PREFIX}checkin list</code>
<code>${PREFIX}checkin toggle [ID]</code>
<code>${PREFIX}checkin test [ID]</code>

<b>设置</b>
<code>${PREFIX}checkin set time [HH:MM]</code> 开始时间
<code>${PREFIX}checkin set range [HH:MM|off]</code> 结束时间，在两者之间随机执行，可跨天
<code>${PREFIX}checkin set delay [0-${MAX_DELAY}]</code> 额外随机延迟（分钟）
<code>${PREFIX}checkin set bot [Token] [ChatID|off]</code> Bot 推送汇总
<code>${PREFIX}checkin set log [ChatID|off]</code> 账号推送汇总

<b>示例</b>
<code>${PREFIX}checkin add storm Storm签到 @storm_bot data:checkin</code>
再回复提示消息 <code>/sign 123456</code>`;
}

class ConfigManager {
  private readonly file = path.join(createDirectoryInAssets("checkin"), "checkin_config.json");
  private data: CheckInConfig = this.load();

  private load(): CheckInConfig {
    try {
      if (!fs.existsSync(this.file)) return { ...DEFAULT_CONFIG };
      const raw = JSON.parse(fs.readFileSync(this.file, "utf-8"));
      delete raw.currentRunTime;
      return {
        ...DEFAULT_CONFIG,
        ...raw,
        lastRunDate: normalizeDate(raw.lastRunDate),
        targets: Array.isArray(raw.targets) ? raw.targets : [],
      };
    } catch (e) {
      console.error("[CheckIn] 配置读取失败:", e);
      return { ...DEFAULT_CONFIG };
    }
  }

  get(): CheckInConfig {
    return this.data;
  }

  save(partial: Partial<CheckInConfig>): void {
    this.data = { ...this.data, ...partial };
    try {
      fs.writeFileSync(this.file, JSON.stringify(this.data, null, 2), "utf-8");
    } catch (e) {
      console.error("[CheckIn] 配置保存失败:", e);
    }
  }
}

class CheckInPlugin extends Plugin {
  description = helpText();
  private readonly cfg = new ConfigManager();
  private timer: NodeJS.Timeout | null = setInterval(() => void this.tick(), 30_000);
  private running = false;
  private readonly pendingAdds = new Map<string, PendingAdd>();

  cleanup(): void {
    if (this.timer) clearInterval(this.timer);
    this.timer = null;
    this.pendingAdds.clear();
  }

  cmdHandlers: Record<string, (msg: Api.Message) => Promise<void>> = {
    checkin: async (msg) => {
      const args = (msg.message || "").trim().split(/\s+/).slice(1);
      try {
        await this.dispatch(msg, (args[0] || "").toLowerCase(), args);
      } catch (e) {
        console.error("[CheckIn] 命令执行失败:", e);
        await this.edit(msg, `❌ 命令执行失败: ${escape(errorText(e))}`).catch(() => {});
      }
    },
  };

  /** 回复式添加：只接受发起人在有效期内对提示消息的回复 */
  listenMessageHandler = async (msg: Api.Message, options?: { isEdited?: boolean }) => {
    if (options?.isEdited || !this.pendingAdds.size) return;
    const chatKey = String(msg.chatId ?? "");
    const pending = this.pendingAdds.get(chatKey);
    if (!pending) return;
    if (Date.now() > pending.expiresAt) {
      this.pendingAdds.delete(chatKey);
      return;
    }
    if (msg.replyToMsgId !== pending.promptMsgId || String(msg.senderId ?? "") !== pending.senderId) return;

    const command = (msg.message || "").trim();
    if (!command) {
      await msg.reply({ message: "❌ 签到命令不能为空，请重新回复提示消息" });
      return;
    }
    this.pendingAdds.delete(chatKey);

    const targets = [...this.cfg.get().targets];
    const next: SignTarget = { ...pending.target, command, enabled: true };
    const i = targets.findIndex((t) => t.id === next.id);
    if (i >= 0) targets[i] = next;
    else targets.push(next);
    this.cfg.save({ targets });

    await msg.reply({
      message: `✅ 已${i >= 0 ? "更新" : "添加"}签到目标 <b>${escape(next.name)}</b> (${escape(next.id)})\n命令: <code>${escape(command)}</code>`,
      parseMode: "html",
      linkPreview: false,
    });
  };

  private async dispatch(msg: Api.Message, action: string, args: string[]): Promise<void> {
    switch (action) {
      case "":
        return this.runManual(msg);
      case "help":
        return this.edit(msg, helpText());
      case "add":
        return this.startAdd(msg, args);
      case "del":
        return this.deleteTarget(msg, args[1]);
      case "list":
        return this.edit(msg, this.listText());
      case "toggle":
        return this.toggleTarget(msg, args[1]);
      case "test":
        return this.testTarget(msg, args[1]);
      case "set":
        return this.edit(msg, this.applySetting((args[1] || "").toLowerCase(), args[2], args[3]));
      case "settings":
        return this.edit(msg, this.settingsText());
      case "reset":
        this.cfg.save({ lastRunDate: "" });
        this.reschedule();
        return this.edit(msg, `✅ 已重置今日状态\n下次执行: ${this.nextRunText()}`);
      default:
        return this.edit(msg, `❌ 未知命令，使用 <code>${PREFIX}checkin help</code> 查看帮助`);
    }
  }

  // ── 命令 ──

  private async runManual(msg: Api.Message): Promise<void> {
    if (!this.cfg.get().targets.some((t) => t.enabled)) {
      return this.edit(msg, `❌ 没有启用的签到目标，先用 <code>${PREFIX}checkin add</code> 添加`);
    }
    if (this.running) return this.edit(msg, "⏳ 签到任务正在执行");
    await this.edit(msg, "🚀 开始执行所有签到任务...");
    void this.runAllSigns("手动触发", msg.chatId?.toString())
      .then(() => msg.delete({ revoke: true }))
      .catch((e) => console.error("[CheckIn] 手动签到失败:", e));
  }

  private async startAdd(msg: Api.Message, args: string[]): Promise<void> {
    const [, id, name, target] = args;
    if (!id || !name || !target) {
      return this.edit(msg, `❌ 格式: <code>${PREFIX}checkin add [ID] [名称] [目标] [data:回调|text:按钮]</code>`);
    }
    const matcher = parseMatcher(args.slice(4));
    await this.edit(
      msg,
      [
        `📝 请<b>回复此消息</b>发送签到命令（可含空格，10 分钟内有效）`,
        ``,
        `ID: ${escape(id)}`,
        `名称: ${escape(name)}`,
        `目标: ${escape(target)}`,
        matcher.callbackData ? `回调: ${escape(matcher.callbackData)}` : "",
        matcher.buttonText ? `按钮: ${escape(matcher.buttonText)}` : "",
      ]
        .filter(Boolean)
        .join("\n"),
    );
    this.pendingAdds.set(String(msg.chatId ?? ""), {
      promptMsgId: msg.id,
      senderId: String(msg.senderId ?? ""),
      expiresAt: Date.now() + PENDING_TTL,
      target: { id, name, target, ...matcher },
    });
  }

  private async deleteTarget(msg: Api.Message, id?: string): Promise<void> {
    if (!id) return this.edit(msg, `❌ 格式: <code>${PREFIX}checkin del [ID]</code>`);
    const targets = this.cfg.get().targets;
    const rest = targets.filter((t) => t.id !== id);
    if (rest.length === targets.length) return this.edit(msg, `❌ 未找到目标: ${escape(id)}`);
    this.cfg.save({ targets: rest });
    await this.edit(msg, `✅ 已删除签到目标: ${escape(id)}`);
  }

  private async toggleTarget(msg: Api.Message, id?: string): Promise<void> {
    if (!id) return this.edit(msg, `❌ 格式: <code>${PREFIX}checkin toggle [ID]</code>`);
    const targets = this.cfg.get().targets.map((t) => (t.id === id ? { ...t, enabled: !t.enabled } : t));
    const t = targets.find((x) => x.id === id);
    if (!t) return this.edit(msg, `❌ 未找到目标: ${escape(id)}`);
    this.cfg.save({ targets });
    await this.edit(msg, `✅ 已${t.enabled ? "启用" : "禁用"}签到目标: ${escape(t.name)} (${escape(id)})`);
  }

  private async testTarget(msg: Api.Message, id?: string): Promise<void> {
    if (!id) return this.edit(msg, `❌ 格式: <code>${PREFIX}checkin test [ID]</code>`);
    const t = this.cfg.get().targets.find((x) => x.id === id);
    if (!t) return this.edit(msg, `❌ 未找到目标: ${escape(id)}`);
    await this.edit(msg, `🚀 正在测试 ${escape(t.name)}...`);
    const r = await this.runSingleSign(t);
    await this.edit(msg, `${r.success ? "✅" : "❌"} <b>${escape(t.name)}</b> 测试${r.success ? "成功" : "失败"}\n\n${escape(clip(r.message, MAX_TEXT))}`);
  }

  /** 应用设置并返回结果文本 */
  private applySetting(key: string, value?: string, extra?: string): string {
    const conf = this.cfg.get();
    const off = !value || value.toLowerCase() === "off";
    switch (key) {
      case "time": {
        const start = parseTime(value);
        if (start === null) return "❌ 格式错误，请使用 HH:MM（例如 10:30）";
        if (conf.runTimeEnd && parseTime(conf.runTimeEnd) === start) return "❌ 开始时间不能与结束时间相同";
        this.cfg.save({ runTime: formatTime(start) });
        break;
      }
      case "range": {
        if (off) {
          this.cfg.save({ runTimeEnd: "" });
          break;
        }
        const end = parseTime(value);
        if (end === null) return "❌ 格式错误，请使用 HH:MM（例如 11:30），或 off 清除";
        if (end === parseTime(conf.runTime)) return "❌ 结束时间不能与开始时间相同";
        this.cfg.save({ runTimeEnd: formatTime(end) });
        break;
      }
      case "delay": {
        const n = Number(value);
        if (!value || !Number.isInteger(n) || n < 0 || n > MAX_DELAY) return `❌ 请输入 0-${MAX_DELAY} 之间的分钟数`;
        this.cfg.save({ randomDelay: n });
        break;
      }
      case "bot": {
        if (off) {
          this.cfg.save({ botToken: "", pushChatId: "" });
          return "✅ 已关闭 Bot 推送";
        }
        if (!extra) return `❌ 格式: <code>${PREFIX}checkin set bot [Token] [ChatID]</code>，或 off 关闭`;
        this.cfg.save({ botToken: value, pushChatId: extra });
        return `✅ Bot 推送已设置 → ${escape(extra)}`;
      }
      case "log":
        this.cfg.save({ logChat: off ? "" : value });
        return off ? "✅ 已清除日志聊天" : `✅ 日志聊天已设置为: ${escape(value)}`;
      default:
        return "❌ 未知设置项，支持 time, range, delay, bot, log";
    }
    this.reschedule();
    return `✅ 执行时间: ${escape(this.windowText())}\n下次执行: ${this.nextRunText()}`;
  }

  // ── 调度 ──

  private reschedule(): void {
    const plan = planNextRun(Date.now(), this.cfg.get());
    this.cfg.save({ nextRunAt: plan.at, nextRunDate: plan.date });
  }

  private async tick(): Promise<void> {
    if (this.running) return;
    try {
      const conf = this.cfg.get();
      if (!conf.nextRunAt || !conf.nextRunDate || conf.nextRunDate <= conf.lastRunDate) return this.reschedule();
      const state = dueState(Date.now(), conf.nextRunAt);
      if (state === "wait") return;
      // 先落盘再执行，执行中重启也不会重复签到
      this.cfg.save({ lastRunDate: conf.nextRunDate });
      this.reschedule();
      if (state === "run" && conf.targets.some((t) => t.enabled)) await this.runAllSigns("自动定时任务");
    } catch (e) {
      console.error("[CheckIn] 定时任务出错:", e);
    }
  }

  // ── 签到 ──

  private async runAllSigns(source: string, fallbackPeer?: string): Promise<void> {
    if (this.running) return;
    this.running = true;
    try {
      const results: Array<{ target: SignTarget; result: SignResult }> = [];
      for (const t of this.cfg.get().targets.filter((x) => x.enabled)) {
        if (results.length) await sleep(2000);
        results.push({ target: t, result: await this.runSingleSign(t) });
      }
      await this.report(source, results, fallbackPeer);
    } finally {
      this.running = false;
    }
  }

  private async report(source: string, results: Array<{ target: SignTarget; result: SignResult }>, fallbackPeer?: string): Promise<void> {
    const ok = results.filter((x) => x.result.success).length;
    let summary =
      `🤖 <b>CheckIn 签到汇总</b>\n` +
      `时间: ${formatTs(Date.now())}\n` +
      `来源: ${escape(source)}\n` +
      `结果: ${ok} 成功 / ${results.length - ok} 失败\n\n`;
    for (const [i, x] of results.entries()) {
      const line = `${x.result.success ? "✅" : "❌"} <b>${i + 1}. ${escape(x.target.name)}</b>\n   ${escape(clip(x.result.message, 200))}\n`;
      if (summary.length + line.length > MAX_TEXT) {
        summary += "…";
        break;
      }
      summary += line;
    }

    const conf = this.cfg.get();
    if (conf.botToken && conf.pushChatId) {
      try {
        return await sendViaBot(conf.botToken, conf.pushChatId, summary);
      } catch (e) {
        console.error("[CheckIn] Bot 推送失败，改用账号推送:", e);
      }
    }
    const peer = conf.logChat || fallbackPeer;
    if (!peer) return;
    const client = await getGlobalClient();
    await client.sendMessage(peer, { message: summary, parseMode: "html", linkPreview: false });
  }

  private async runSingleSign(target: SignTarget): Promise<SignResult> {
    try {
      const client = await getGlobalClient();
      if (!client) return { success: false, message: "客户端未初始化" };
      const sent = await client.sendMessage(target.target, { message: target.command });
      const needButton = hasMatcher(target);

      const first = await this.poll(client, target.target, sent.id, (msgs) =>
        msgs.find((m) => !m.out && (!needButton || findCallbackData(m, target))),
      );
      if (!first) return { success: false, message: needButton ? "未收到带签到按钮的回复" : "未收到签到回复" };
      if (!needButton) return { success: true, message: first.message || "已收到回复" };

      let answer = "";
      try {
        const res = await client.invoke(
          new Api.messages.GetBotCallbackAnswer({ peer: target.target, msgId: first.id, data: findCallbackData(first, target) }),
        );
        answer = res.message || "";
      } catch (e) {
        // 机器人不应答回调时 Telegram 报超时，按钮其实已生效
        if (!/BOT_RESPONSE_TIMEOUT/.test(errorText(e))) throw e;
      }
      if (answer) return { success: true, message: answer };

      // 没有弹窗提示时，取机器人的新回复或对原消息的编辑
      const reply = await this.poll(client, target.target, first.id - 1, (msgs) =>
        msgs.find((m) => !m.out && (m.id > first.id || (m.id === first.id && (m.editDate !== first.editDate || m.message !== first.message)))),
      );
      return { success: true, message: reply?.message || "已点击签到按钮" };
    } catch (e) {
      return { success: false, message: errorText(e) || "执行失败" };
    }
  }

  /** 轮询 minId 之后的消息直到 pick 命中或超时 */
  private async poll(
    client: TelegramClient,
    peer: string,
    minId: number,
    pick: (msgs: Api.Message[]) => Api.Message | undefined,
  ): Promise<Api.Message | undefined> {
    const deadline = Date.now() + REPLY_TIMEOUT;
    while (Date.now() < deadline) {
      await sleep(1000);
      try {
        const msgs = await client.getMessages(peer, { limit: 10, minId });
        const hit = pick(msgs.filter((m) => m instanceof Api.Message));
        if (hit) return hit;
      } catch (e) {
        console.error("[CheckIn] 轮询消息失败:", e);
      }
    }
    return undefined;
  }

  // ── 展示 ──

  private async edit(msg: Api.Message, text: string): Promise<void> {
    await msg.edit({ text, parseMode: "html", linkPreview: false });
  }

  private windowText(): string {
    const { runTime, runTimeEnd } = this.cfg.get();
    if (!runTimeEnd) return `每天 ${runTime}`;
    const cross = (parseTime(runTimeEnd) ?? 0) < (parseTime(runTime) ?? 0);
    return `每天 ${runTime} ~ ${cross ? "次日 " : ""}${runTimeEnd} 随机`;
  }

  private nextRunText(): string {
    const at = this.cfg.get().nextRunAt;
    return at ? formatTs(at) : "未计划";
  }

  private listText(): string {
    const targets = this.cfg.get().targets;
    if (!targets.length) return "📝 当前没有签到目标";
    const enabled = targets.filter((t) => t.enabled).length;
    const lines = targets.map((t, i) => {
      const m = t.callbackData ? `\n   回调: ${escape(t.callbackData)}` : t.buttonText ? `\n   按钮: ${escape(t.buttonText)}` : "";
      return `${t.enabled ? "🟢" : "🔴"} <b>${i + 1}. ${escape(t.name)}</b>\n   ID: ${escape(t.id)}\n   目标: ${escape(t.target)}\n   命令: <code>${escape(t.command)}</code>${m}`;
    });
    return `📝 <b>签到目标</b> (${enabled}/${targets.length} 启用)\n\n${lines.join("\n\n")}`;
  }

  private settingsText(): string {
    const c = this.cfg.get();
    return (
      `⚙️ <b>CheckIn 配置</b>\n\n` +
      `⏰ 执行时间: ${escape(this.windowText())}\n` +
      `🎲 额外随机延迟: ${c.randomDelay} 分钟\n` +
      `📅 下次执行: ${this.nextRunText()}\n` +
      `🗓 上次执行: ${escape(c.lastRunDate || "无")}\n` +
      `🤖 Bot 推送: ${c.botToken ? `已配置 → ${escape(c.pushChatId)}` : "未配置"}\n` +
      `📝 日志聊天: ${escape(c.logChat || "未设置")}\n` +
      `🎯 启用目标: ${c.targets.filter((t) => t.enabled).length}/${c.targets.length}`
    );
  }

  // ── 面板 ──

  panelAdapter: PanelSettingsAdapter = {
    id: "checkin",
    title: "checkin",
    description: "定时自动签到：执行时间、推送设置、签到目标",
    category: "插件配置",
    icon: "✅",
    getSchema: (): PanelSettingField[] => [
      { key: "runTime", label: "开始时间", type: "string", placeholder: "10:00", default: "10:00", description: "每日执行时间 HH:MM（上海时间）" },
      { key: "runTimeEnd", label: "结束时间", type: "string", placeholder: "11:30", description: "填写后在开始和结束之间随机执行，早于开始时间表示跨天；留空为固定时间" },
      { key: "randomDelay", label: "额外随机延迟（分钟）", type: "number", min: 0, max: MAX_DELAY, default: 0, description: "在计划时刻后再随机等待 0~N 分钟" },
      { key: "logChat", label: "日志聊天", type: "string", placeholder: "@channel 或 -100xxxxxx", description: "未配置 Bot 推送时，汇总由账号发到这里" },
      { key: "botToken", label: "Bot Token", type: "password", secret: true, description: "可选，用 Bot 推送签到汇总" },
      { key: "pushChatId", label: "Bot 推送 Chat ID", type: "string", placeholder: "-100xxxxxx", description: "配合 Bot Token 使用" },
      {
        key: "targets",
        label: "签到目标",
        type: "textarea",
        description: "JSON 数组，每项包含 id、name、target、command，可选 callbackData 或 buttonText，以及 enabled",
      },
    ],
    getValues: (): Record<string, unknown> => {
      const c = this.cfg.get();
      return {
        runTime: c.runTime,
        runTimeEnd: c.runTimeEnd || "",
        randomDelay: c.randomDelay,
        logChat: c.logChat,
        botToken: c.botToken,
        pushChatId: c.pushChatId,
        targets: JSON.stringify(c.targets, null, 2),
      };
    },
    setValues: (patch: Record<string, unknown>): void => {
      const updates = this.parsePanelPatch(patch);
      this.cfg.save(updates);
      if (updates.runTime !== undefined || updates.runTimeEnd !== undefined || updates.randomDelay !== undefined) this.reschedule();
    },
  };

  private parsePanelPatch(patch: Record<string, unknown>): Partial<CheckInConfig> {
    const updates: Partial<CheckInConfig> = {};
    const str = (k: string) => (typeof patch[k] === "string" ? (patch[k] as string).trim() : undefined);

    const runTime = str("runTime");
    if (runTime !== undefined) {
      const v = parseTime(runTime);
      if (v === null) throw new Error("开始时间格式应为 HH:MM");
      updates.runTime = formatTime(v);
    }
    const runTimeEnd = str("runTimeEnd");
    if (runTimeEnd !== undefined) {
      const v = parseTime(runTimeEnd);
      if (runTimeEnd && v === null) throw new Error("结束时间格式应为 HH:MM");
      updates.runTimeEnd = v === null ? "" : formatTime(v);
    }
    const start = updates.runTime ?? this.cfg.get().runTime;
    const end = updates.runTimeEnd ?? this.cfg.get().runTimeEnd;
    if (end && parseTime(end) === parseTime(start)) throw new Error("结束时间不能与开始时间相同");

    if (patch.randomDelay !== undefined) {
      const n = Number(patch.randomDelay);
      if (!Number.isInteger(n) || n < 0 || n > MAX_DELAY) throw new Error(`随机延迟应为 0-${MAX_DELAY} 的整数`);
      updates.randomDelay = n;
    }
    for (const k of ["logChat", "botToken", "pushChatId"] as const) {
      const v = str(k);
      if (v !== undefined) updates[k] = v;
    }
    const targets = str("targets");
    if (targets !== undefined) {
      let parsed: unknown;
      try {
        parsed = JSON.parse(targets || "[]");
      } catch {
        throw new Error("签到目标不是合法 JSON");
      }
      updates.targets = validateTargets(parsed);
    }
    return updates;
  }
}

export default new CheckInPlugin();
