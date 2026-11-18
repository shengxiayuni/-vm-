(function (b) {
  const {
    ArgumentType: A,
    BlockType: B,
    translate: T,
    extensions: E,
    runtime: R
  } = b;

  const BT = { CMD: B.COMMAND, REP: B.REPORTER, BOOL: B.BOOLEAN || B.REPORTER };
  const AT = { STR: A.STRING, NUM: A.NUMBER };

  T.setup({
    zh: {
      extensionName: '保护扩展',
      guardStart: '启动 VM 保护，心跳写入 [VAR]',
      guardCheck: '进行扩展检测',
      guardTick: '检查保护（放进重复执行里跑）',
      guardScan: '自动扫描积木（重建指纹）',
      guardOk: 'VM 保护正常？',
      guardWhere: '被改写的位置',
      guardKill: '立即终止游戏，原因 [WHY]',
      safeAdd: '设定安全变量 [VAR]',
      safeSet: '将安全变量 [VAR] 设为 [VALUE]',
      safeAddBy: '将安全变量 [VAR] 增加 [N]',
      safeGet: '安全变量 [VAR] 的值',
      safeMode: '安全变量违规处理 [MODE]',
      safeShow: '显示数据看板 [ON]',
      safeList: '安全变量清单',
      safeRemove: '取消安全变量 [VAR]',
      codeBuild: '积木编号获取',
      codeScan: '积木编号核实扫描',
      codeOf: '核实编号 [OPCODE]'
    },
    en: {
      extensionName: 'Guard Extension',
      guardStart: 'start vm guard, heartbeat to [VAR]',
      guardCheck: 'run extension detection',
      guardTick: 'guard tick (run in forever loop)',
      guardScan: 'auto scan blocks (rebuild print)',
      guardOk: 'vm guard ok?',
      guardWhere: 'tampered location',
      guardKill: 'terminate game, reason [WHY]',
      safeAdd: 'mark safe variable [VAR]',
      safeSet: 'set safe variable [VAR] to [VALUE]',
      safeAddBy: 'change safe variable [VAR] by [N]',
      safeGet: 'value of safe variable [VAR]',
      safeMode: 'safe violation mode [MODE]',
      safeShow: 'show data panel [ON]',
      safeList: 'safe variable list',
      safeRemove: 'unmark safe variable [VAR]',
      codeBuild: 'build block codes',
      codeScan: 'verify block codes',
      codeOf: 'block code of [OPCODE]'
    }
  });

  const PROBES = [
    'runtime._step',
    'runtime.stepRunLoop',
    'runtime.stopAll',
    'runtime.greenFlag',
    'runtime.getOpcodeFunction',
    'runtime._pushThread',
    'runtime._stopThreads',
    'runtime.sequencer.stepThreads',
    'runtime.sequencer.stepThread',
    'runtime.ioDevices.mouse.getScratchX',
    'runtime.ioDevices.mouse.getScratchY',
    'runtime.extensions.register',
    'runtime.constructor.prototype.compilerRegisterExtension',
    'saveProjectSb3',
    'saveProject'
  ];

  const PRIMS = [
    'data_setvariableto',
    'data_changevariableby',
    'data_addtolist',
    'data_deleteoflist',
    'control_stop',
    'control_deleteclone',
    'procedures_call',
    'event_whenflagclicked',
    'motion_gotoxy',
    'looks_switchbackdropto'
  ];

  const TAGOK = {
    DIV: 1, SECTION: 1, ASIDE: 1, HEADER: 1, FOOTER: 1,
    MAIN: 1, NAV: 1, FORM: 1, UL: 1, SPAN: 1, P: 1, DIALOG: 1
  };

  const EDITOR_SEL = [
    '.blocklyToolboxDiv', '.blocklySvg', '.gui_blocks-wrapper',
    '.gui_editor-wrapper', '#react-toolbox', '.blocklyWorkspace'
  ];

  const OURS = {
    'vmguard-kill': 1, 'vmguard-hud': 1, 'vmguard-editorlock': 1,
    'vmguard-safe': 1, 'vmguard-safe-toast': 1
  };

  function esc(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }

  class VMGuard {
    constructor(rt) {
      this._rt = rt;
      this._ticks = 0;
      this._beat = 0;
      this._dead = false;
      this._active = false;
      this._hook = '';
      this._varName = '_hb';
      this._varObj = null;
      this._varState = 'unknown';
      this._editorAtStart = false;
      this._cap = null;
      this._vmRef = null;
      this._seal = Math.random().toString(36).slice(2) + Date.now().toString(36);

      this._probeParts = [];
      for (let i = 0; i < PROBES.length; i++) {
        this._probeParts.push({ p: PROBES[i], parts: PROBES[i].split('.') });
      }

      this._blk = null;
      this._ids = [];
      this._owner = null;
      this._tmap = null;
      this._blkCount = null;
      this._blkTotal = 0;
      this._blkSpan = 1;
      this._seg = 0;
      this._segs = 8;
      this._verifyPending = false;

      this._domCache = new WeakMap();
      this._domQueue = [];
      this._domIdx = 0;
      this._domDirty = true;
      this._lastFast = 0;
      this._lastDom = 0;
      this._lastScript = 0;
      this._lastGlob = 0;
      this._scriptCount = 0;
      this._scriptSrc = null;
      this._susp = [];
      this._suspTick = 0;
      this._issues = [];
      this._primCap = null;
      this._timer = null;
      this._lastBeat = 0;
      this._lastWrite = 0;
      this._busy = false;
      this._safe = {};
      this._safeMode = '提示';
      this._safeHud = null;
      this._safeToastTimer = null;
      this._lastSafe = 0;
      this._codeTable = null;
      this._codeMap = null;
      this._codeTotal = 0;
      this._nukes = [];
      this._stat = { kills: 0, removed: 0, codeAt: 0, checks: 0 };

      this._startTimer();
      this._startWatch();
      try {
        if (rt && rt.on) {
          rt.on('PROJECT_LOADED', () => {
            this._active = false;
            this._cap = null;
            this._primCap = null;
            this._scriptCount = 0;
            this._scriptSrc = null;
            this._domDirty = true;
            this._safe = {};
            this._safeHudToggle(false);
            this._codeTable = null;
            this._codeMap = null;
            this._codeTotal = 0;
          });
        }
      } catch (e) {}
    }

    getInfo() {
      return {
        id: 'vmguard',
        name: T({ id: 'extensionName' }),
        color1: '#3f2b66',
        color2: '#7a5cf0',
        blocks: [
          {
            opcode: 'guardStart',
            func: 'guardStart',
            blockType: BT.CMD,
            text: T({ id: 'guardStart' }),
            arguments: { VAR: { type: AT.STR, defaultValue: '_hb' } }
          },
          { opcode: 'guardCheck', func: 'guardCheck', blockType: BT.CMD, text: T({ id: 'guardCheck' }) },
          { opcode: 'guardTick', func: 'guardTick', blockType: BT.CMD, text: T({ id: 'guardTick' }) },
          { opcode: 'guardScan', func: 'guardScan', blockType: BT.CMD, text: T({ id: 'guardScan' }) },
          { opcode: 'guardOk', func: 'guardOk', blockType: BT.BOOL, text: T({ id: 'guardOk' }) },
          { opcode: 'guardWhere', func: 'guardWhere', blockType: BT.REP, text: T({ id: 'guardWhere' }) },
          {
            opcode: 'guardKill',
            func: 'guardKill',
            blockType: BT.CMD,
            text: T({ id: 'guardKill' }),
            arguments: { WHY: { type: AT.STR, defaultValue: '调用方终止' } }
          },
          {
            opcode: 'safeAdd',
            func: 'safeAdd',
            blockType: BT.CMD,
            text: T({ id: 'safeAdd' }),
            arguments: { VAR: { type: AT.STR, defaultValue: '金币' } }
          },
          {
            opcode: 'safeSet',
            func: 'safeSet',
            blockType: BT.CMD,
            text: T({ id: 'safeSet' }),
            arguments: {
              VAR: { type: AT.STR, defaultValue: '金币' },
              VALUE: { type: AT.STR, defaultValue: '0' }
            }
          },
          {
            opcode: 'safeAddBy',
            func: 'safeAddBy',
            blockType: BT.CMD,
            text: T({ id: 'safeAddBy' }),
            arguments: {
              VAR: { type: AT.STR, defaultValue: '金币' },
              N: { type: AT.NUM, defaultValue: 1 }
            }
          },
          {
            opcode: 'safeGet',
            func: 'safeGet',
            blockType: BT.REP,
            text: T({ id: 'safeGet' }),
            arguments: { VAR: { type: AT.STR, defaultValue: '金币' } }
          },
          {
            opcode: 'safeMode',
            func: 'safeMode',
            blockType: BT.CMD,
            text: T({ id: 'safeMode' }),
            arguments: { MODE: { type: AT.STR, defaultValue: '提示' } }
          },
          {
            opcode: 'safeShow',
            func: 'safeShow',
            blockType: BT.CMD,
            text: T({ id: 'safeShow' }),
            arguments: { ON: { type: AT.NUM, defaultValue: 1 } }
          },
          { opcode: 'safeList', func: 'safeList', blockType: BT.REP, text: T({ id: 'safeList' }) },
          {
            opcode: 'safeRemove',
            func: 'safeRemove',
            blockType: BT.CMD,
            text: T({ id: 'safeRemove' }),
            arguments: { VAR: { type: AT.STR, defaultValue: '金币' } }
          },
          { opcode: 'codeScan', func: 'codeScan', blockType: BT.CMD, text: T({ id: 'codeScan' }) },
          {
            opcode: 'codeOf',
            func: 'codeOf',
            blockType: BT.REP,
            text: T({ id: 'codeOf' }),
            arguments: { OPCODE: { type: AT.STR, defaultValue: 'motion_movesteps' } }
          }
        ]
      };
    }

    _vm() {
      if (this._vmRef && this._vmRef.runtime) return this._vmRef;
      let vm = null;
      try {
        const em = this._rt && this._rt.extensionManager;
        if (em && em.vm) vm = em.vm;
      } catch (e) {}
      try { if (!vm && this._rt && this._rt.vm) vm = this._rt.vm; } catch (e) {}
      try { if (!vm && typeof Scratch !== 'undefined' && Scratch.vm) vm = Scratch.vm; } catch (e) {}
      try { if (!vm && typeof window !== 'undefined' && window.eureka && window.eureka.vm) vm = window.eureka.vm; } catch (e) {}
      try { if (!vm && typeof window !== 'undefined' && window.vm) vm = window.vm; } catch (e) {}
      if (vm && vm.runtime) {
        this._vmRef = vm;
        return vm;
      }
      return null;
    }

    _runtime() {
      const vm = this._vm();
      if (vm && vm.runtime) return vm.runtime;
      try { if (this._rt && this._rt.ioDevices) return this._rt; } catch (e) {}
      return null;
    }

    _allTargets() {
      const rt = this._runtime();
      try { return (rt && rt.targets) || []; } catch (e) { return []; }
    }

    _walk(root, parts) {
      let cur = root;
      for (let i = 0; i < parts.length; i++) {
        if (!cur) return undefined;
        try { cur = cur[parts[i]]; } catch (e) { return undefined; }
      }
      return cur;
    }

    _capture() {
      if (this._cap) return this._cap;
      const vm = this._vm();
      if (!vm) return null;
      const fns = {};
      let n = 0;
      for (let i = 0; i < this._probeParts.length; i++) {
        const rec = this._probeParts[i];
        let v = null;
        try { v = this._walk(vm, rec.parts); } catch (e) {}
        if (typeof v === 'function') { fns[rec.p] = v; n++; }
      }
      if (!fns['runtime._step'] && !fns['runtime.stepRunLoop']) return null;
      this._cap = { vm: vm, rt: vm.runtime, fns: fns };
      const prims = this._snapPrims();
      console.log('[vmguard] probes=' + n + ' prims=' + (prims ? prims.n : 0));
      return this._cap;
    }

    _snapPrims() {
      if (this._primCap) return this._primCap;
      const rt = this._runtime();
      const table = rt && rt._primitives;
      if (!table || typeof table !== 'object') return null;
      const fns = {};
      let n = 0;
      for (let i = 0; i < PRIMS.length; i++) {
        const k = PRIMS[i];
        try {
          const f = table[k];
          if (typeof f === 'function') { fns[k] = f; n++; }
        } catch (e) {}
      }
      this._primCap = { fns: fns, n: n };
      return this._primCap;
    }

    _hooked() {
      const c = this._capture();
      if (!c) return '';
      const vm = this._vm();
      if (!vm) return '';
      if (vm !== c.vm) {
        try { if (vm.runtime !== c.rt) return '外部脚本改写了 VM'; } catch (e) {}
      }
      for (let i = 0; i < this._probeParts.length; i++) {
        const p = this._probeParts[i].p;
        const old = c.fns[p];
        if (!old) continue;
        let now = null;
        try { now = this._walk(vm, this._probeParts[i].parts); } catch (e) {}
        if (typeof now !== 'function' || now !== old) return '外部脚本改写了 VM：' + p;
      }
      const pc = this._primCap;
      if (pc && pc.n) {
        const rt = this._runtime();
        const table = rt && rt._primitives;
        if (table) {
          for (const k in pc.fns) {
            let now = null;
            try { now = table[k]; } catch (e) {}
            if (now !== pc.fns[k]) return '外部脚本接管了积木：' + k;
          }
        } else {
          return '外部脚本移除了积木表';
        }
      }
      return '';
    }

    _editorHit() {
      for (let i = 0; i < EDITOR_SEL.length; i++) {
        try {
          const el = document.querySelector(EDITOR_SEL[i]);
          if (!el) continue;
          const cs = getComputedStyle(el);
          if (cs.display !== 'none' && cs.visibility !== 'hidden') return '积木编辑器已打开';
        } catch (e) {}
      }
      return '';
    }

    _hideEditor() {
      try {
        if (document.getElementById('vmguard-editorlock')) return;
        const st = document.createElement('style');
        st.id = 'vmguard-editorlock';
        st.textContent = EDITOR_SEL.join(',') +
          '{display:none!important;visibility:hidden!important;pointer-events:none!important}';
        (document.head || document.documentElement).appendChild(st);
      } catch (e) {}
    }

    _tagOf(el) {
      if (el.id) return '#' + el.id;
      const cls = el.className;
      if (cls && String(cls).trim()) return '.' + String(cls).trim().split(/\s+/)[0];
      return String(el.tagName || 'node').toLowerCase();
    }

    _domProbe(el, now) {
      let rec = this._domCache.get(el);
      if (rec && (now - rec.t) < 900) return rec.hit;
      let hit = '';
      try {
        if (el.nodeType !== 1) return '';
        if (OURS[el.id]) return '';
        const tag = el.tagName;
        const hasKid = el.childElementCount > 0;
        const inlinePos = el.style && (el.style.position || '');
        const quick = inlinePos === 'fixed' || inlinePos === 'sticky' || inlinePos === 'absolute';
        if (!quick && !hasKid) return '';
        if (!quick && !TAGOK[tag]) return '';
        if (quick && !TAGOK[tag] && el.childElementCount === 0) return '';
        const cs = getComputedStyle(el);
        if (!cs) return '';
        if (cs.display === 'none' || cs.visibility === 'hidden') return '';
        if (Number(cs.opacity) === 0) return '';
        const pos = cs.position;
        if (pos !== 'fixed' && pos !== 'sticky' && pos !== 'absolute') return '';
        const z = parseInt(cs.zIndex || '0', 10) || 0;
        const tag2 = this._tagOf(el);
        if (z >= 900000) hit = '外部脚本：' + tag2 + '（z=' + z + '）';
        if (!hit) {
          let input = 0;
          try { input = el.querySelectorAll('button,input,select,textarea').length; } catch (e) {}
          let area = 0;
          if (pos === 'fixed' || pos === 'sticky' || z >= 100000 || input >= 2) {
            try {
              const r = el.getBoundingClientRect();
              area = r.width * r.height;
            } catch (e) {}
          }
          if (input >= 2 && area >= 20000) hit = '外部脚本：' + tag2 + '（控件 ' + input + '）';
          else if (z >= 100000 && area >= 40000) hit = '外部脚本：' + tag2 + '（z=' + z + '）';
        }
      } catch (e) {}
      this._domCache.set(el, { t: now, hit: hit });
      return hit;
    }

    _rebuildQueue() {
      this._domQueue = [];
      this._domIdx = 0;
      this._domDirty = false;
      const body = document.body;
      if (!body) return;
      const out = this._domQueue;
      const walk = (nodes, depth) => {
        const arr = nodes || [];
        for (let i = 0; i < arr.length; i++) {
          const el = arr[i];
          if (!el || el.nodeType !== 1) continue;
          out.push(el);
          if (out.length >= 1600) return;
          if (depth > 0) walk(el.children, depth - 1);
          if (out.length >= 1600) return;
        }
      };
      walk(body.children, 3);
    }

    _isPanelHit(hit) {
      return !!hit && hit.indexOf('外部脚本：') === 0;
    }

    _nuke(el) {
      try {
        if (el && el.parentNode) el.parentNode.removeChild(el);
        else if (el && el.remove) el.remove();
      } catch (e) {}
      const now = Date.now();
      this._nukes.push(now);
      this._stat.removed++;
      if (this._nukes.length > 30) this._nukes.shift();
      let recent = 0;
      for (let i = 0; i < this._nukes.length; i++) {
        if (now - this._nukes[i] < 10000) recent++;
      }
      this._safeToast('已移除悬浮窗' + (recent > 1 ? ' ×' + recent : ''));
      console.log('[vmguard] panel removed count=' + recent);
      if (recent >= 3) return '外部脚本：悬浮窗反复注入';
      return '';
    }

    _domPass(budget, now) {
      if (this._domDirty || !this._domQueue.length || this._domIdx >= this._domQueue.length) {
        this._rebuildQueue();
      }
      const q = this._domQueue;
      const end = Math.min(q.length, this._domIdx + budget);
      for (let i = this._domIdx; i < end; i++) {
        const el = q[i];
        const hit = this._domProbe(el, now);
        if (!hit) continue;
        if (this._isPanelHit(hit)) {
          const bad = this._nuke(el);
          if (bad) { this._domIdx = i; return bad; }
          continue;
        }
        this._domIdx = i;
        return hit;
      }
      this._domIdx = end;
      if (end >= q.length) this._domIdx = 0;
      return '';
    }

    _suspPush(el) {
      if (!el || el.nodeType !== 1) return;
      if (OURS[el.id]) return;
      if (this._susp.length >= 64) this._susp.shift();
      try {
        const tag = String(el.tagName || '').toLowerCase();
        if (tag === 'script' || tag === 'iframe') {
          this._susp.push({ el: el, tag: tag, t: Date.now(), n: 0, hard: 1 });
          return;
        }
        this._susp.push({ el: el, tag: tag, t: Date.now(), n: 0, hard: 0 });
      } catch (e) {}
    }

    _suspHit(now) {
      const list = this._susp;
      const keep = [];
      for (let i = 0; i < list.length; i++) {
        const r = list[i];
        if (!r || !r.el) continue;
        if (r.hard) return '外部脚本注入（' + r.tag + '）';
        const el = r.el;
        if (!el.isConnected) continue;
        const hit = this._domProbe(el, now);
        if (hit && this._isPanelHit(hit)) {
          const bad = this._nuke(el);
          if (bad) return bad;
          continue;
        }
        if (hit) return hit;
        let flag = '';
        try {
          const cs = getComputedStyle(el);
          if (cs.position === 'fixed' || cs.position === 'absolute') {
            if (el.querySelectorAll('button,input,select,textarea').length >= 1) flag = '外部脚本：新增浮层';
          }
        } catch (e) {}
        if (flag) {
          const bad2 = this._nuke(el);
          if (bad2) return bad2;
          continue;
        }
        r.n++;
        if (r.n < 3 && (now - r.t) < 4000) keep.push(r);
      }
      this._susp = keep;
      return '';
    }

    _scriptHit() {
      try {
        const all = document.querySelectorAll('script');
        const cur = [];
        for (let i = 0; i < all.length; i++) cur.push(String(all[i].src || ''));
        const base = this._scriptSrc;
        if (base) {
          if (cur.length > base.length) {
            for (let i = base.length; i < cur.length; i++) {
              const src = cur[i];
              if (src && (src.indexOf('chrome-extension://') === 0 ||
                src.indexOf('moz-extension://') === 0 ||
                src.indexOf('safari-extension://') === 0 ||
                src.indexOf('.user.js') !== -1)) {
                return '外部脚本：' + src.slice(0, 60);
              }
            }
            return '外部脚本注入（+' + (cur.length - base.length) + '）';
          }
        }
        this._scriptSrc = cur;
        for (let i = 0; i < cur.length; i++) {
          const src = cur[i];
          if (src.indexOf('chrome-extension://') === 0 ||
            src.indexOf('moz-extension://') === 0 ||
            src.indexOf('safari-extension://') === 0 ||
            src.indexOf('.user.js') !== -1) return '外部脚本：' + src.slice(0, 60);
        }
      } catch (e) {}
      return '';
    }

    _globHit() {
      try {
        const keys = Object.keys(window);
        for (let i = 0; i < keys.length; i++) {
          const k = keys[i];
          if (k.indexOf('__CSRT') === 0 || k.indexOf('__csrt') === 0 ||
            k === 'csrt' || k === 'CSRT' || k === 'CheatEngine' ||
            k === '__cheat' || k === 'cheatEngine' || k === '__CC_CHEAT') {
            return '外部脚本：全局 ' + k;
          }
        }
      } catch (e) {}
      return '';
    }

    _hash(s) {
      let h = 2166136261;
      for (let i = 0; i < s.length; i++) {
        h ^= s.charCodeAt(i);
        h = Math.imul(h, 16777619);
      }
      return h >>> 0;
    }

    _collectBlocks() {
      const targets = this._allTargets();
      const rows = [];
      for (let i = 0; i < targets.length; i++) {
        const t = targets[i];
        const blocks = t && t.blocks && t.blocks._blocks;
        if (!blocks) continue;
        rows.push({ t: t, blocks: blocks });
      }
      return rows;
    }

    _buildPrint() {
      const rows = this._collectBlocks();
      let total = 0;
      const blk = {};
      const owner = {};
      const count = {};
      const ids = [];
      for (let i = 0; i < rows.length; i++) {
        const t = rows[i].t;
        const blocks = rows[i].blocks;
        let n = 0;
        for (const id in blocks) {
          const v = blocks[id];
          if (!v || !v.opcode) continue;
          n++;
          total++;
          ids.push(id);
        }
        count[t.id] = n;
      }
      this._blkTotal = total;
      this._blkSpan = Math.max(1, Math.floor(1000000 / Math.max(1, total)));
      for (let i = 0; i < rows.length; i++) {
        const t = rows[i].t;
        const blocks = rows[i].blocks;
        for (const id in blocks) {
          const v = blocks[id];
          if (!v || !v.opcode) continue;
          const op = String(v.opcode);
          blk[id] = { op: op, val: this._hash(op + '#' + id) % this._blkSpan, target: t.id };
          owner[id] = t.id;
        }
      }
      this._ids = ids;
      this._blk = blk;
      this._owner = owner;
      this._blkCount = count;
      this._seg = 0;
      this._verifyPending = true;
      console.log('[vmguard] blocks=' + total + ' span=' + this._blkSpan + ' segs=' + this._segs);
    }

    _scanSegment() {
      if (!this._blk || !this._ids.length) return '';
      const rows = this._collectBlocks();
      const tmap = {};
      for (let i = 0; i < rows.length; i++) tmap[rows[i].t.id] = rows[i].blocks;
      this._tmap = tmap;
      const per = Math.ceil(this._ids.length / this._segs);
      const start = (this._seg % this._segs) * per;
      this._seg = (this._seg + 1) % this._segs;
      const end = Math.min(this._ids.length, start + per);
      for (let i = start; i < end; i++) {
        const id = this._ids[i];
        const rec = this._blk[id];
        if (!rec) continue;
        const blocks = tmap[rec.target];
        if (!blocks) return '外部脚本删除了积木：' + String(id).slice(0, 8);
        const now = blocks[id];
        if (!now || !now.opcode) return '外部脚本删除了积木：' + String(id).slice(0, 8);
        const op = String(now.opcode);
        if (op !== rec.op) {
          return '外部脚本改写了积木：' + String(id).slice(0, 8) + '（' + rec.op + ' → ' + op + '）';
        }
      }
      if (this._seg === 0 && this._verifyPending) {
        this._verifyPending = false;
        return this._countCheck(rows);
      }
      return '';
    }

    _countCheck(rows) {
      let total = 0;
      for (let i = 0; i < rows.length; i++) {
        const t = rows[i].t;
        const blocks = rows[i].blocks;
        let n = 0;
        for (const id in blocks) {
          const v = blocks[id];
          if (v && v.opcode) n++;
        }
        total += n;
        const was = this._blkCount[t.id];
        if (was === undefined) { this._blkCount[t.id] = n; continue; }
        if (n > was) return '外部脚本注入了积木（+' + (n - was) + '）';
        if (n < was) this._blkCount[t.id] = n;
      }
      if (total > this._blkTotal + 0) return '外部脚本注入了积木（+' + (total - this._blkTotal) + '）';
      return '';
    }

    _verifyAll() {
      if (!this._blk) return '';
      const rows = this._collectBlocks();
      const tmap = {};
      for (let i = 0; i < rows.length; i++) tmap[rows[i].t.id] = rows[i].blocks;
      for (let i = 0; i < this._ids.length; i++) {
        const id = this._ids[i];
        const rec = this._blk[id];
        const blocks = tmap[rec.target];
        if (!blocks) return '外部脚本删除了积木：' + String(id).slice(0, 8);
        const now = blocks[id];
        if (!now || !now.opcode) return '外部脚本删除了积木：' + String(id).slice(0, 8);
        if (String(now.opcode) !== rec.op) {
          return '外部脚本改写了积木：' + String(id).slice(0, 8) + '（' + rec.op + ' → ' + String(now.opcode) + '）';
        }
      }
      return this._countCheck(rows);
    }

    _ensureVar(name) {
      const targets = this._allTargets();
      if (!targets.length) { this._varState = 'noStage'; return null; }
      for (let i = 0; i < targets.length; i++) {
        const t = targets[i];
        let vars = null;
        try { vars = t.variables; } catch (e) {}
        if (!vars) continue;
        try {
          if (typeof vars.forEach === 'function') {
            let hit = null;
            vars.forEach((v) => { if (!hit && v && v.name === name) hit = v; });
            if (hit) { this._varState = name + ':ok'; return hit; }
          } else {
            for (const id in vars) {
              const v = vars[id];
              if (v && v.name === name) { this._varState = name + ':ok'; return v; }
            }
          }
        } catch (e) {}
      }
      this._varState = name + ':missing';
      return null;
    }

    _writeBeat(force) {
      if (!this._varName) return;
      const now = Date.now();
      if (!force && now - (this._lastWrite || 0) < 200) return;
      this._lastWrite = now;
      if (!this._varObj || force) this._varObj = this._ensureVar(this._varName);
      if (!this._varObj) return;
      try { this._varObj.value = this._beat; } catch (e) { this._varObj = null; }
    }

    _overlay(reason) {
      try {
        let el = document.getElementById('vmguard-kill');
        if (!el) {
          el = document.createElement('div');
          el.id = 'vmguard-kill';
          el.style.cssText = 'position:fixed;left:0;top:0;right:0;bottom:0;z-index:2147483600;' +
            'display:flex;align-items:center;justify-content:center;flex-direction:column;gap:10px;' +
            'background:rgba(8,10,14,.92);color:#ff5a5a;font:700 22px/1.5 system-ui,sans-serif;' +
            'letter-spacing:1px;text-align:center;padding:24px';
          document.body.appendChild(el);
        }
        el.textContent = 'VM 保护已触发 · 游戏终止';
        const sub = document.createElement('div');
        sub.style.cssText = 'font:400 12px/1.7 ui-monospace,Consolas,monospace;color:#c9d3e4;max-width:70vw;word-break:break-all';
        sub.textContent = '原因：' + reason + '  指纹：' + this._seal;
        el.appendChild(sub);
      } catch (e) {}
    }

    _kill(reason) {
      if (this._dead) return;
      this._dead = true;
      this._stat.kills++;
      this._issues.push(reason);
      if (this._issues.length > 8) this._issues.shift();
      const rt = this._runtime();
      const stop = (this._cap && this._cap.fns['runtime.stopAll']) || (rt && rt.stopAll);
      try { if (typeof stop === 'function') stop.call(rt); } catch (e) {
        try { if (rt && rt.stopAll) rt.stopAll(); } catch (e2) {}
      }
      try { if (rt && rt._threads && rt._threads.length) rt._threads.length = 0; } catch (e) {}
      try { if (document.exitPointerLock) document.exitPointerLock(); } catch (e) {}
      this._overlay(reason);
      console.log('[vmguard] TERMINATED: ' + reason);
      try { if (this._timer) clearInterval(this._timer); } catch (e) {}
      try { if (this._rt && this._rt.startHats) this._rt.startHats('vmguard_whenTampered'); } catch (e) {}
    }

    _running() {
      try {
        const rt = this._runtime();
        if (!rt) return false;
        if (rt._threads && rt._threads.length > 0) return true;
        if (rt.sequencer && rt.sequencer.activeThread) return true;
      } catch (e) {}
      return false;
    }

    _quick(now) {
      const h = this._hooked();
      if (h) return h;
      if (!this._editorAtStart && this._editorHit()) return '积木编辑器已打开';
      if (now - this._lastScript >= 900) {
        this._lastScript = now;
        const s = this._scriptHit();
        if (s) return s;
      }
      if (now - this._lastGlob >= 2000) {
        this._lastGlob = now;
        const g = this._globHit();
        if (g) return g;
      }
      return '';
    }

    _step_(force) {
      if (this._dead) return;
      if (!this._active && !force) return;
      if (this._busy) return;
      const now = performance.now();
      if (!force && now - this._lastFast < 130) return;
      this._lastFast = now;
      this._ticks++;
      this._busy = true;
      try {
        if (Date.now() - this._lastBeat >= 200) {
          this._lastBeat = Date.now();
          this._beat++;
          this._writeBeat(false);
        }
        if (this._ticks === 1) {
          this._capture();
          this._buildPrint();
          this._writeBeat(true);
        }
        const q = this._quick(now);
        if (q) { this._hook = q; this._kill(q); return; }
        if (now - this._lastSafe >= 400) {
          this._lastSafe = now;
          this._safeSample(now);
          this._safeRender();
        }
        const u = this._suspHit(now);
        if (u) { this._hook = u; this._kill(u); return; }
        if (now - this._lastDom >= 550) {
          this._lastDom = now;
          const budget = force ? 100000 : 60;
          const d = this._domPass(budget, now);
          if (d) { this._hook = d; this._kill(d); return; }
        }
        if (!this._running()) return;
        if (force) {
          const v = this._verifyAll();
          if (v) { this._hook = v; this._kill(v); return; }
          return;
        }
        const s = this._scanSegment();
        if (s) { this._hook = s; this._kill(s); return; }
      } finally {
        this._busy = false;
      }
    }

    _startWatch() {
      try {
        if (typeof MutationObserver !== 'function') return;
        const obs = new MutationObserver((muts) => {
          for (let i = 0; i < muts.length; i++) {
            const added = muts[i].addedNodes;
            if (!added || !added.length) continue;
            for (let j = 0; j < added.length; j++) {
              const n = added[j];
              if (!n || n.nodeType !== 1) continue;
              this._suspPush(n);
              this._domDirty = true;
            }
          }
        });
        const target = document.body || document.documentElement;
        if (!target) return;
        obs.observe(target, { childList: true, subtree: true });
        this._obs = obs;
      } catch (e) {}
    }

    _startTimer() {
      try {
        this._timer = setInterval(() => {
          if (this._dead) { clearInterval(this._timer); return; }
          this._step_(false);
        }, 100);
      } catch (e) {}
    }

    _allVars() {
      const out = [];
      const targets = this._allTargets();
      for (let i = 0; i < targets.length; i++) {
        const t = targets[i];
        let vars = null;
        try { vars = t.variables; } catch (e) {}
        if (!vars) continue;
        try {
          if (typeof vars.forEach === 'function') {
            vars.forEach((v) => { if (v) out.push({ obj: v, target: t }); });
          } else {
            for (const id in vars) {
              const v = vars[id];
              if (v) out.push({ obj: v, target: t });
            }
          }
        } catch (e) {}
      }
      return out;
    }

    _findVar(name) {
      const raw = name;
      let key = '';
      if (raw && typeof raw === 'object') {
        key = String(raw.name || raw.id || '');
      } else {
        key = String(raw == null ? '' : raw).trim();
      }
      if (!key) return null;
      const all = this._allVars();
      for (let i = 0; i < all.length; i++) {
        if (String(all[i].obj.name || '').trim() === key) return all[i];
      }
      for (let i = 0; i < all.length; i++) {
        if (String(all[i].obj.id || '') === key) return all[i];
      }
      const lower = key.toLowerCase();
      for (let i = 0; i < all.length; i++) {
        if (String(all[i].obj.name || '').trim().toLowerCase() === lower) return all[i];
      }
      const byValue = [];
      for (let i = 0; i < all.length; i++) {
        try {
          if (String(all[i].obj.value) === key) byValue.push(all[i]);
        } catch (e) {}
      }
      if (byValue.length === 1) return byValue[0];
      return null;
    }

    _argName(v) {
      if (v && typeof v === 'object') return String(v.name || v.id || '').trim();
      return String(v == null ? '' : v).trim();
    }

    _safeLookup(v) {
      const key = this._argName(v);
      if (key && this._safe[key]) return this._safe[key];
      const found = this._findVar(v);
      if (!found) return null;
      const canon = String(found.obj.name || '').trim() || key;
      if (this._safe[canon]) {
        const rec = this._safe[canon];
        rec.obj = found.obj;
        rec.target = found.target;
        return rec;
      }
      const rec = {
        name: canon,
        obj: found.obj,
        target: found.target,
        raw: found.obj.value,
        writes: 0,
        blocks: 0,
        patched: null,
        bypass: 0,
        grace: Date.now() + 800,
        last: ''
      };
      this._safe[canon] = rec;
      this._safePatch(rec);
      return rec;
    }

    _safeRec(name) {
      return this._safeLookup(name);
    }

    _safePatch(rec) {
      const obj = rec.obj;
      if (!obj || rec.patched === obj) return true;
      try { rec.raw = obj.value; } catch (e) { return false; }
      try {
        Object.defineProperty(obj, 'value', {
          configurable: true,
          enumerable: true,
          get: () => rec.raw,
          set: (nv) => { this._safeOnWrite(rec, nv); }
        });
        rec.patched = obj;
        try { rec.desc = Object.getOwnPropertyDescriptor(obj, 'value'); } catch (e) { rec.desc = null; }
        return true;
      } catch (e) {
        rec.patched = null;
        return false;
      }
    }

    _safeOnWrite(rec, nv) {
      if (this._writing) { rec.raw = nv; return; }
      if (nv === rec.raw) return;
      rec.writes++;
      rec.last = String(nv).slice(0, 24);
      if (Date.now() < rec.grace) { rec.raw = nv; return; }
      this._safeViolate(rec, nv);
    }

    _safeViolate(rec, nv) {
      rec.blocks++;
      const why = '安全变量被修改：' + rec.name;
      if (this._safeMode === '终止') {
        this._hook = why;
        this._kill(why + '（' + String(nv).slice(0, 24) + '）');
        return;
      }
      this._safeToast('拦截 ' + rec.name + ' 的非法修改');
      this._safeRender();
      console.log('[vmguard] safe blocked ' + rec.name + ' -> ' + String(nv).slice(0, 24));
    }

    _safeSetValue(rec, val) {
      this._writing = true;
      try {
        rec.raw = val;
        if (rec.patched && rec.obj) rec.obj.value = val;
      } catch (e) {}
      this._writing = false;
      rec.writes++;
      this._safeRender();
    }

    _safeSample(now) {
      const names = Object.keys(this._safe);
      for (let i = 0; i < names.length; i++) {
        const rec = this._safe[names[i]];
        const found = this._findVar(rec.name);
        if (!found) { this._safeRender(); continue; }
        if (found.obj !== rec.obj) { rec.obj = found.obj; rec.patched = null; this._safePatch(rec); continue; }
        if (rec.patched !== rec.obj) {
          if (!this._safePatch(rec)) {
            let cur = null;
            try { cur = rec.obj.value; } catch (e) {}
            if (cur !== rec.raw && Date.now() > rec.grace) {
              rec.bypass++;
              this._safeViolate(rec, cur);
              try { rec.obj.value = rec.raw; } catch (e) {}
            }
          }
          continue;
        }
        try {
          const d = Object.getOwnPropertyDescriptor(rec.obj, 'value');
          if (!d || !rec.desc || d.get !== rec.desc.get) {
            rec.bypass++;
            if (Date.now() > rec.grace) this._safeViolate(rec, d ? d.value : rec.obj.value);
            rec.patched = null;
            this._safePatch(rec);
          }
        } catch (e) {}
      }
    }

    _safeToast(text) {
      try {
        let el = document.getElementById('vmguard-safe-toast');
        if (!el) {
          el = document.createElement('div');
          el.id = 'vmguard-safe-toast';
          el.style.cssText = 'position:fixed;left:50%;top:18px;transform:translateX(-50%);' +
            'z-index:2147483500;background:rgba(12,14,18,.94);color:#ff6b6b;border:1px solid #ff6b6b;' +
            'padding:8px 14px;font:600 13px/1.5 ui-monospace,Consolas,monospace;pointer-events:none';
          document.body.appendChild(el);
        }
        el.textContent = text;
        clearTimeout(this._safeToastTimer);
        this._safeToastTimer = setTimeout(() => {
          try { if (el.parentNode) el.parentNode.removeChild(el); } catch (e) {}
        }, 2200);
      } catch (e) {}
    }

    _safeRender() {
      const el = this._safeHud;
      if (!el || !el.parentNode) return;
      const names = Object.keys(this._safe);
      let rows = '';
      for (let i = 0; i < names.length; i++) {
        const rec = this._safe[names[i]];
        let val = '';
        try { val = String(rec.obj ? rec.obj.value : rec.raw); } catch (e) { val = String(rec.raw); }
        rows += '<div style="display:flex;justify-content:space-between;gap:8px;padding:3px 0;border-top:1px solid rgba(255,255,255,.08)">' +
          '<span style="color:#c9d3e4;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + esc(rec.name) + '</span>' +
          '<span style="color:' + (rec.blocks ? '#ff6b6b' : '#7fe3a1') + '">' + esc(val) +
          (rec.blocks ? ' ×' + rec.blocks : '') + '</span>' +
          '</div>';
      }
      let kinds = 0;
      try { kinds = this._codeTable ? Object.keys(this._codeTable).length : 0; } catch (e) {}
      const probeN = this._cap && this._cap.fns ? Object.keys(this._cap.fns).length : 0;
      const codeAt = this._stat.codeAt ? new Date(this._stat.codeAt).toLocaleTimeString() : '未核实';
      const lastIssue = this._issues.length ? this._issues[this._issues.length - 1] : '无';
      el.innerHTML =
        '<div style="font:700 12px/1.6 ui-monospace,Consolas,monospace;color:#9aa7bd;letter-spacing:.06em;display:flex;justify-content:space-between">' +
        '<span>数据看板</span><span style="color:' + (this._dead ? '#ff6b6b' : '#7fe3a1') + '">' +
        (this._dead ? '已终止' : '运行中') + '</span></div>' +
        '<div style="color:#8b94a8;font:400 11px/1.6 ui-monospace,Consolas,monospace;margin:2px 0 4px">安全变量 · ' + esc(this._safeMode) + '</div>' +
        (rows || '<div style="color:#7a8296;font:400 12px ui-monospace,monospace">未设定安全变量</div>') +
        '<div style="margin-top:6px;padding-top:4px;border-top:1px solid rgba(255,255,255,.18);font:400 11px/1.7 ui-monospace,Consolas,monospace;color:#9aa7bd">' +
        '积木 ' + this._codeTotal + ' 块 / ' + kinds + ' 类<br>' +
        '编号核实 ' + esc(codeAt) + '<br>' +
        '探针 ' + probeN + ' · 拦截 ' + this._stat.kills + '<br>' +
        '移除浮窗 ' + this._stat.removed + '<br>' +
        '最近 ' + esc(String(lastIssue).slice(0, 52)) +
        '</div>';
    }

    _safeHudToggle(on) {
      if (on) {
        if (this._safeHud && this._safeHud.parentNode) { this._safeRender(); return; }
        try {
          const el = document.createElement('div');
          el.id = 'vmguard-safe';
          el.style.cssText = 'position:fixed;right:12px;top:12px;width:264px;z-index:2147483500;' +
            'background:rgba(12,14,18,.9);border:1px solid rgba(154,167,189,.45);padding:8px 10px;' +
            'font:400 12px/1.5 ui-monospace,Consolas,monospace;color:#c9d3e4;pointer-events:none';
          document.body.appendChild(el);
          this._safeHud = el;
          this._safeRender();
        } catch (e) {}
      } else if (this._safeHud) {
        try { if (this._safeHud.parentNode) this._safeHud.parentNode.removeChild(this._safeHud); } catch (e) {}
        this._safeHud = null;
      }
    }

    _b36(n) {
      const s = '0123456789abcdefghijklmnopqrstuvwxyz';
      let v = Math.max(1, Math.floor(n));
      let out = '';
      while (v > 0) {
        out = s.charAt(v % 36) + out;
        v = Math.floor(v / 36);
      }
      return out;
    }

    _computeCodes() {
      const rows = this._collectBlocks();
      const counts = {};
      const list = [];
      for (let i = 0; i < rows.length; i++) {
        const blocks = rows[i].blocks;
        for (const id in blocks) {
          const v = blocks[id];
          if (!v || !v.opcode) continue;
          const op = String(v.opcode);
          counts[op] = (counts[op] || 0) + 1;
          list.push({ id: id, op: op });
        }
      }
      list.sort((a, c) => (a.id < c.id ? -1 : a.id > c.id ? 1 : 0));
      const ops = Object.keys(counts).sort((a, c) => {
        if (counts[c] !== counts[a]) return counts[c] - counts[a];
        return a < c ? -1 : a > c ? 1 : 0;
      });
      const table = {};
      for (let i = 0; i < ops.length; i++) {
        table[ops[i]] = { code: this._b36(i + 1), count: counts[ops[i]] };
      }
      const seq = {};
      const map = {};
      for (let i = 0; i < list.length; i++) {
        const it = list[i];
        seq[it.op] = (seq[it.op] || 0) + 1;
        const c = table[it.op].code;
        map[it.id] = { op: it.op, code: c, serial: c + '-' + seq[it.op] };
      }
      return { table: table, map: map, total: list.length };
    }

    _buildCodes() {
      const now = this._computeCodes();
      this._codeTable = now.table;
      this._codeMap = now.map;
      this._codeTotal = now.total;
      this._stat.codeAt = Date.now();
      const kinds = Object.keys(now.table).length;
      console.log('[vmguard] codes blocks=' + now.total + ' kinds=' + kinds);
      return now;
    }

    _verifyCodes() {
      if (!this._codeTable) return '';
      const now = this._computeCodes();
      if (now.total !== this._codeTotal) {
        return '积木编号失配：数量 ' + this._codeTotal + ' → ' + now.total;
      }
      const oldMap = this._codeMap;
      for (const id in oldMap) {
        const o = oldMap[id];
        const n = now.map[id];
        if (!n) return '积木编号失配：积木被删除 ' + String(id).slice(0, 8);
        if (n.op !== o.op) {
          return '积木编号失配：' + String(id).slice(0, 8) + '（' + o.op + ' → ' + n.op + '）';
        }
        if (n.serial !== o.serial) return '积木编号失配：编号漂移 ' + String(id).slice(0, 8);
      }
      for (const op in this._codeTable) {
        const o = this._codeTable[op];
        const n = now.table[op];
        if (!n) return '积木编号失配：类型消失 ' + op;
        if (n.code !== o.code) return '积木编号失配：号段变化 ' + op;
      }
      for (const op in now.table) {
        if (!this._codeTable[op]) return '积木编号失配：新增类型 ' + op;
      }
      this._codeTable = now.table;
      this._codeMap = now.map;
      this._codeTotal = now.total;
      this._stat.codeAt = Date.now();
      return '';
    }

    guardStart(args) {
      const name = String((args && args.VAR) || '_hb').trim() || '_hb';
      this._varName = name;
      this._varObj = null;
      this._active = true;
      this._cap = null;
      this._primCap = null;
      this._hook = '';
      this._editorAtStart = !!this._editorHit();
      if (!this._editorAtStart) this._hideEditor();
      this._scriptSrc = null;
      this._scriptCount = 0;
      try { this._scriptCount = document.querySelectorAll('script').length; } catch (e) {}
      this._capture();
      this._buildPrint();
      this._buildCodes();
      this._writeBeat(true);
      this._lastFast = 0;
      console.log('[vmguard] started var=' + name + ' state=' + this._varState +
        ' blocks=' + this._blkTotal + ' span=' + this._blkSpan);
      return this._varState;
    }

    guardCheck() {
      this._active = true;
      this._cap = null;
      this._primCap = null;
      this._hook = '';
      this._editorAtStart = !!this._editorHit();
      if (!this._editorAtStart) this._hideEditor();
      this._scriptSrc = null;
      this._scriptCount = 0;
      try { this._scriptCount = document.querySelectorAll('script').length; } catch (e) {}
      this._capture();
      this._buildPrint();
      this._buildCodes();
      const h = this._hooked();
      if (h) { this._hook = h; this._kill(h); return ''; }
      const e = this._editorAtStart ? '' : this._editorHit();
      if (e) { this._hook = e; this._kill(e); return ''; }
      const s = this._scriptHit();
      if (s) { this._hook = s; this._kill(s); return ''; }
      const g = this._globHit();
      if (g) { this._hook = g; this._kill(g); return ''; }
      this._suspHit(performance.now());
      this._lastDom = performance.now() - 10000;
      this._lastFast = 0;
      this._ticks = 0;
      this._step_(true);
      if (this._dead) return '';
      console.log('[vmguard] check ok blocks=' + this._blkTotal + ' span=' + this._blkSpan);
      return '';
    }

    guardTick() {
      this._step_(false);
      return '';
    }

    guardScan() {
      this._buildPrint();
      const v = this._verifyAll();
      if (v) { this._hook = v; this._kill(v); return ''; }
      console.log('[vmguard] rescan blocks=' + this._blkTotal + ' span=' + this._blkSpan);
      return '';
    }

    guardOk() {
      if (this._dead) return false;
      if (this._hooked()) return false;
      if (this._susp.length > 8) return false;
      if (this._scanSegment()) return false;
      return true;
    }

    guardWhere() {
      if (this._hook) return this._hook;
      const h = this._hooked();
      if (h) return h;
      if (this._issues.length) return this._issues[this._issues.length - 1];
      return '无';
    }

    safeAdd(args) {
      const rec = this._safeLookup(args && args.VAR);
      if (!rec) {
        const shown = this._argName(args && args.VAR) || '(空)';
        this._safeToast('变量不存在：' + shown);
        console.log('[vmguard] safe add failed: ' + shown);
        return '';
      }
      this._safeRender();
      console.log('[vmguard] safe add ' + rec.name + ' value=' + String(rec.raw));
      return '';
    }

    safeSet(args) {
      const rec = this._safeLookup(args && args.VAR);
      if (!rec) { this._safeToast('变量不存在：' + (this._argName(args && args.VAR) || '(空)')); return ''; }
      this._safeSetValue(rec, args ? args.VALUE : '');
      return '';
    }

    safeAddBy(args) {
      const rec = this._safeLookup(args && args.VAR);
      if (!rec) { this._safeToast('变量不存在：' + (this._argName(args && args.VAR) || '(空)')); return ''; }
      const step = Number(args && args.N);
      const cur = Number(rec.raw);
      const base = isNaN(cur) ? 0 : cur;
      this._safeSetValue(rec, base + (isNaN(step) ? 0 : step));
      return '';
    }

    safeGet(args) {
      const rec = this._safeLookup(args && args.VAR);
      if (!rec) return '';
      try { return String(rec.obj ? rec.obj.value : rec.raw); } catch (e) {}
      return String(rec.raw);
    }

    safeMode(args) {
      const mode = String((args && args.MODE) || '');
      this._safeMode = mode.indexOf('终止') !== -1 ? '终止' : '提示';
      this._safeRender();
      this._safeToast('安全变量策略：' + this._safeMode);
      return '';
    }

    safeShow(args) {
      this._safeHudToggle(Number(args && args.ON) !== 0);
      return '';
    }

    safeList() {
      const rows = [];
      const names = Object.keys(this._safe);
      for (let i = 0; i < names.length; i++) {
        const rec = this._safe[names[i]];
        let v = rec.raw;
        try { v = rec.obj ? rec.obj.value : rec.raw; } catch (e) {}
        rows.push({ name: rec.name, value: v, writes: rec.writes, blocks: rec.blocks });
      }
      return JSON.stringify(rows);
    }

    safeRemove(args) {
      const rec = this._safeLookup(args && args.VAR);
      if (!rec) return '';
      try {
        if (rec.obj) {
          Object.defineProperty(rec.obj, 'value', {
            value: rec.raw, writable: true, configurable: true, enumerable: true
          });
        }
      } catch (e) {}
      delete this._safe[rec.name];
      this._safeRender();
      return '';
    }

    codeBuild() {
      const n = this._buildCodes();
      const kinds = Object.keys(n.table).length;
      this._safeToast('编号已发放：' + n.total + ' 块 / ' + kinds + ' 类');
      return '';
    }

    codeScan() {
      if (!this._codeTable) this._buildCodes();
      const v = this._verifyCodes();
      if (v) { this._hook = v; this._kill(v); return ''; }
      const kinds = this._codeTable ? Object.keys(this._codeTable).length : 0;
      this._stat.checks++;
      this._safeToast('编号核实通过：' + this._codeTotal + ' 块 / ' + kinds + ' 类');
      this._safeRender();
      return '';
    }

    codeOf(args) {
      const op = String((args && args.OPCODE) || '').trim();
      if (!this._codeTable || !this._codeTable[op]) return '';
      return this._codeTable[op].code;
    }

    guardKill(args) {
      this._kill('积木调用：' + String((args && args.WHY) || ''));
    }
  }

  E.register(new VMGuard(R));
})(Scratch);
