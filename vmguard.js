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
      safeWrites: '安全变量警告次数',
      panelBlock: '拦截特征为 [SEL] 的悬浮窗',
      panelBlockAll: '拦截所有悬浮窗 白名单特征为 [W1] [W2] [W3] [W4] [W5] [W6] [W7] [W8] [W9] [W10]（最高10个）',
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
      safeWrites: 'safe warnings',
      panelBlock: 'block floating window matching [SEL]',
      panelBlockAll: 'block all floating windows, whitelist [W1] [W2] [W3] [W4] [W5] [W6] [W7] [W8] [W9] [W10] (max 10)',
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
      this._stopRef = null;
      this._frozen = false;
      this._freezeH = null;

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

      this._lastFast = 0;
      this._lastScript = 0;
      this._lastGlob = 0;
      this._scriptCount = 0;
      this._scriptSrc = null;
      this._scriptSnap = null;
      this._susp = [];
      this._panelKeys = [];
      this._blockAllFloats = false;
      this._floatWhitelist = [];
      this._floatList = [];
      this._floatCount = 0;
      this._lastPanel = 0;
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
      this._stat = { kills: 0, codeAt: 0, checks: 0, warns: 0, floats: 0 };
      this._safeSig = '';
      this._safeCycle = 0;
      this._safeRenderAt = 0;

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
            this._scriptSnap = null;
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
            opcode: 'safeWrites',
            func: 'safeWrites',
            blockType: BT.REP,
            text: T({ id: 'safeWrites' })
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
          },
          {
            opcode: 'panelBlock',
            func: 'panelBlock',
            blockType: BT.CMD,
            text: T({ id: 'panelBlock' }),
            arguments: { SEL: { type: AT.STR, defaultValue: 'ball' } }
          },
          {
            opcode: 'panelBlockAll',
            func: 'panelBlockAll',
            blockType: BT.CMD,
            text: T({ id: 'panelBlockAll' }),
            arguments: {
              W1: { type: AT.STR, defaultValue: '' },
              W2: { type: AT.STR, defaultValue: '' },
              W3: { type: AT.STR, defaultValue: '' },
              W4: { type: AT.STR, defaultValue: '' },
              W5: { type: AT.STR, defaultValue: '' },
              W6: { type: AT.STR, defaultValue: '' },
              W7: { type: AT.STR, defaultValue: '' },
              W8: { type: AT.STR, defaultValue: '' },
              W9: { type: AT.STR, defaultValue: '' },
              W10: { type: AT.STR, defaultValue: '' }
            }
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

    _suspPush(el) {
      if (!el || el.nodeType !== 1) return;
      if (OURS[el.id]) return;
      let tag = '';
      try { tag = String(el.tagName || '').toLowerCase(); } catch (e) {}
      if (tag !== 'script' && tag !== 'iframe') return;
      if (this._susp.length >= 16) this._susp.shift();
      this._susp.push({ el: el, tag: tag });
    }

    _suspHit() {
      const list = this._susp;
      this._susp = [];
      for (let i = 0; i < list.length; i++) {
        const r = list[i];
        if (!r) continue;
        return '外部脚本注入（' + r.tag + '）';
      }
      return '';
    }

    _scriptBad(src, text) {
      if (src) {
        if (src.indexOf('chrome-extension://') === 0 ||
          src.indexOf('moz-extension://') === 0 ||
          src.indexOf('safari-extension://') === 0 ||
          src.indexOf('.user.js') !== -1) {
          return '外部脚本：' + src.slice(0, 60);
        }
      }
      const head = text ? text.slice(0, 1500) : '';
      if (head) {
        if (head.indexOf('==UserScript==') !== -1 || head.indexOf('@grant') !== -1) {
          return '强制：UserScript 脚本（内联头）';
        }
        const keys = ['__CSRT', 'csrt-ball', 'CSRT pro', 'csrt-window', '__csrt'];
        for (let i = 0; i < keys.length; i++) {
          if (head.indexOf(keys[i]) !== -1) return '强制：CSRT 脚本：' + keys[i];
        }
      }
      return '';
    }

    _floats() {
      const out = [];
      const seen = [];
      const add = (el) => {
        if (!el || el.nodeType !== 1 || OURS[el.id]) return;
        for (let i = 0; i < seen.length; i++) if (seen[i] === el) return;
        seen.push(el);
        out.push(el);
      };
      try {
        const body = document.body;
        if (body) {
          const kids = body.children || [];
          for (let i = 0; i < kids.length && i < 80; i++) add(kids[i]);
        }
        const q = document.querySelectorAll(
          '[style*="position:fixed"],[style*="position: fixed"],[style*="position:absolute"],' +
          '[style*="position: absolute"],[class*="panel"],[class*="window"],[class*="float"],' +
          '[class*="ball"],[class*="overlay"],[class*="modal"],[class*="menu"],[class*="tool"],' +
          '[class*="hud"],[class*="widget"],[id*="panel"],[id*="window"],[id*="float"],' +
          '[id*="ball"],[id*="overlay"],[id*="modal"],[id*="menu"],[id*="tool"]'
        );
        for (let i = 0; i < q.length && i < 200; i++) add(q[i]);
        const frames = document.querySelectorAll('iframe');
        for (let f = 0; f < frames.length && f < 8; f++) {
          try {
            const doc = frames[f].contentDocument;
            if (!doc || !doc.body) continue;
            const kids = doc.body.children || [];
            for (let i = 0; i < kids.length && i < 40; i++) add(kids[i]);
          } catch (e) {}
        }
      } catch (e) {}
      const vw = window.innerWidth || 1920;
      const vh = window.innerHeight || 1080;
      const list = [];
      for (let i = 0; i < out.length; i++) {
        const el = out[i];
        let cs = null;
        try { cs = getComputedStyle(el); } catch (e) {}
        if (!cs) continue;
        const pos = cs.position;
        if (pos !== 'fixed' && pos !== 'absolute') continue;
        if (cs.display === 'none' || cs.visibility === 'hidden' || Number(cs.opacity) === 0) continue;
        let r = null;
        try { r = el.getBoundingClientRect(); } catch (e) {}
        if (!r || r.width < 8 || r.height < 8) continue;
        const w = r.width;
        const h = r.height;
        if (w > vw * 0.92 && h > vh * 0.92) continue;
        if (w * h > vw * vh * 0.7) continue;
        const tag = String(el.tagName || '').toLowerCase();
        if (tag === 'canvas' || tag === 'iframe' || tag === 'html' || tag === 'body') continue;
        if (el.id && /^(app|root|game|stage|game-root|gamecanvas)$/i.test(String(el.id))) continue;
        try { if (el.querySelector && el.querySelector('canvas')) continue; } catch (e) {}
        const cls = String(el.className || '');
        const id = String(el.id || '');
        const label = id ? '#' + id : (cls ? '.' + cls.trim().split(/\s+/)[0] : String(el.tagName || '').toLowerCase());
        const brs = cs.borderTopLeftRadius || cs.borderRadius || '';
        let br = parseFloat(brs);
        if (brs.indexOf('%') !== -1) br = Math.min(w, h) * (parseFloat(brs) / 100);
        const circle = (Math.abs(w - h) <= 6 && w >= 20 && br >= Math.min(w, h) / 2 - 2);
        let text = '';
        try { text = String(el.textContent || '').replace(/\s+/g, ' ').slice(0, 60); } catch (e) {}
        list.push({
          el: el, label: label, cls: cls, id: id, text: text,
          z: parseInt(cs.zIndex || '0', 10) || 0,
          w: Math.round(w), h: Math.round(h), circle: circle
        });
      }
      return list;
    }

    _matchFloat(it, key) {
      const k = String(key || '').trim();
      if (!k) return false;
      if (k.charAt(0) === '.' || k.charAt(0) === '#') {
        try { if (it.el.matches(k)) return true; } catch (e) {}
      }
      const hay = (it.label + ' ' + it.cls + ' ' + it.id + ' ' + it.text).toLowerCase();
      return hay.indexOf(k.toLowerCase()) !== -1;
    }

    _allowedFloat(it) {
      const wl = this._floatWhitelist;
      for (let i = 0; i < wl.length; i++) {
        if (this._matchFloat(it, wl[i])) return true;
      }
      return false;
    }

    _panelScan(force) {
      const now = performance.now();
      if (!force && now - this._lastPanel < 1000) return '';
      this._lastPanel = now;
      let list = [];
      try { list = this._floats(); } catch (e) {}
      this._floatCount = list.length;
      const rows = [];
      const blockAll = this._blockAllFloats;
      for (let i = 0; i < list.length && i < 8; i++) {
        const it = list[i];
        let mark = it.circle ? '○ ' : '□ ';
        if (blockAll) mark = this._allowedFloat(it) ? '✓ ' : '✗ ';
        rows.push(mark + it.label + ' z' + it.z + ' ' + it.w + '×' + it.h);
      }
      if (list.length > 8) rows.push('+' + (list.length - 8) + ' 条');
      this._floatList = rows;
      const keys = this._panelKeys;
      for (let i = 0; i < list.length; i++) {
        const it = list[i];
        for (let k = 0; k < keys.length; k++) {
          if (this._matchFloat(it, keys[k])) {
            this._blockFloat(it);
            break;
          }
        }
        if (blockAll) {
          if (!this._allowedFloat(it)) this._blockFloat(it);
          continue;
        }
      }
      this._safeRender();
      return '';
    }

    _blockFloat(it) {
      if (!it || it.blocked) return;
      it.blocked = true;
      try {
        const el = it.el;
        if (el) {
          if (el.parentNode) el.parentNode.removeChild(el);
          else if (el.remove) el.remove();
        }
      } catch (e) {}
      this._stat.floats++;
      const why = '拦截悬浮窗：' + it.label;
      this._issues.push(why);
      if (this._issues.length > 8) this._issues.shift();
      try { this._safeToast('已拦截悬浮窗 ' + it.label); } catch (e) {}
      console.log('[vmguard] float blocked ' + it.label + ' z=' + it.z);
    }

    panelBlockAll(args) {
      try {
        const wl = [];
        for (let i = 1; i <= 10; i++) {
          const v = String((args && args['W' + i]) || '').trim();
          if (v) wl.push(v);
        }
        this._floatWhitelist = wl;
        this._blockAllFloats = true;
        console.log('[vmguard] block all floats, whitelist=' + wl.join(','));
        this._panelScan(true);
        const n = this._floatCount;
        this._safeToast('拦截全部悬浮窗 · 白名单 ' + wl.length + ' 条 · 扫描到 ' + n + ' 个');
        if (!n) console.log('[vmguard] no float found; target may be in shadow DOM or nested container');
        this._safeRender();
      } catch (e) {
        try { this._safeToast('拦截积木出错：' + (e && e.message)); } catch (x) {}
        console.log('[vmguard] panelBlockAll error ' + e);
      }
      return '';
    }

    panelBlock(args) {
      try {
        const key = String((args && args.SEL) || '').trim();
        if (key) {
          if (this._panelKeys.indexOf(key) === -1) this._panelKeys.push(key);
          console.log('[vmguard] panel feature=' + key);
        }
        this._panelScan(true);
        const n = this._floatCount;
        this._safeToast(key ? ('特征 ' + key + ' 已生效 · 扫描到 ' + n + ' 个悬浮窗') : '特征为空');
        this._safeRender();
      } catch (e) {
        try { this._safeToast('拦截积木出错：' + (e && e.message)); } catch (x) {}
        console.log('[vmguard] panelBlock error ' + e);
      }
      return '';
    }

    _gmHit() {
      try {
        const w = window;
        if (w.GM_info || w.GM || w.unsafeWindow ||
          w.GM_getValue || w.GM_setValue || w.GM_xmlhttpRequest) {
          return '强制：油猴/暴力猴（GM_* 全局）';
        }
        if (w.__CSRT_CONFIG || w.__CSRT_state || w.__CSRT_SCALE || w.__csrt_blob_compat_patched) {
          return '强制：CSRT（全局对象）';
        }
      } catch (e) {}
      try {
        if (document.getElementById('csrt-glass-theme') ||
          document.getElementById('csrt-inspector-panel') ||
          document.querySelector('.csrt-ball') ||
          document.querySelector('.csrt-window')) {
          return '强制：CSRT（面板）';
        }
      } catch (e) {}
      try {
        if (localStorage.getItem('__csrt_features') ||
          localStorage.getItem('__csrt_phone_settings') ||
          localStorage.getItem('__csrt_scale')) {
          return '强制：CSRT（存储）';
        }
      } catch (e) {}
      return '';
    }

    _scriptHit() {
      try {
        const all = document.getElementsByTagName('script');
        const cur = [];
        for (let i = 0; i < all.length; i++) {
          const s = all[i];
          const src = String(s.src || '');
          const text = String(s.textContent || '');
          const bad = this._scriptBad(src, text);
          if (bad) return bad;
          cur.push(src + '|' + text.length + '|' + text.slice(0, 120));
        }
        const base = this._scriptSnap;
        if (!base) {
          this._scriptSnap = cur;
          this._scriptCount = cur.length;
          return '';
        }
        if (cur.length > base.length) {
          this._scriptSnap = cur;
          return '外部脚本注入（script +' + (cur.length - base.length) + '）';
        }
        if (cur.length < base.length) {
          this._scriptSnap = cur;
          return '';
        }
        for (let i = 0; i < cur.length; i++) {
          if (cur[i] !== base[i]) {
            this._scriptSnap = cur;
            return '外部脚本已替换（script）';
          }
        }
        return '';
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

    _overlay(reason, note) {
      try {
        let el = document.getElementById('vmguard-kill');
        if (!el) {
          el = document.createElement('div');
          el.id = 'vmguard-kill';
          el.style.cssText = 'position:fixed;left:0;top:0;right:0;bottom:0;z-index:2147483600;' +
            'display:flex;align-items:center;justify-content:center;flex-direction:column;gap:10px;' +
            'background:rgba(8,10,14,.92);color:#ff5a5a;font:700 22px/1.5 system-ui,sans-serif;' +
            'letter-spacing:1px;text-align:center;padding:24px;pointer-events:auto';
          document.body.appendChild(el);
        }
        el.textContent = '防作弊触发 · 游戏终止' + (note ? ' · ' + note : '');
        const sub = document.createElement('div');
        sub.style.cssText = 'font:400 12px/1.7 ui-monospace,Consolas,monospace;color:#c9d3e4;max-width:70vw;word-break:break-all';
        sub.textContent = '原因：' + reason + '  指纹：' + this._seal + '  刷新页面可退出';
        el.appendChild(sub);
      } catch (e) {}
    }

    _kill(reason) {
      if (this._dead) return;
      const text = String(reason == null ? '' : reason);
      const force = text.indexOf('强制：') === 0;
      const body = force ? text.slice(3) : text;
      if (this._safeMode === '提示' && !force) {
        this._stat.warns++;
        this._issues.push(body);
        if (this._issues.length > 8) this._issues.shift();
        this._safeToast('检测到：' + String(body).slice(0, 70));
        this._safeRender();
        console.log('[vmguard] WARN ' + body);
        return;
      }
      this._doKill(body);
    }

    _doKill(reason) {
      if (this._dead) return;
      this._dead = true;
      this._stat.kills++;
      this._issues.push(reason);
      if (this._issues.length > 8) this._issues.shift();
      const rt = this._runtime();
      try { if (document.exitPointerLock) document.exitPointerLock(); } catch (e) {}
      console.log('[vmguard] TERMINATED: ' + reason);
      try { if (this._timer) clearInterval(this._timer); } catch (e) {}
      const curStop = rt && rt.stopAll;
      const native = this._cap && this._cap.fns && this._cap.fns['runtime.stopAll'];
      let replaced = false;
      if (this._stopRef && curStop && curStop !== this._stopRef) replaced = true;
      if (!replaced && native && curStop && curStop !== native) replaced = true;
      if (!replaced) {
        try {
          if (typeof curStop === 'function') curStop.call(rt);
          else replaced = true;
        } catch (e3) {
          replaced = true;
        }
      }
      this._overlay(reason, replaced ? 'stop 已被替换' : '');
      if (replaced) {
        console.log('[vmguard] stopAll replaced -> hard freeze');
        this._hardFreeze(reason);
      } else {
        setTimeout(() => {
          if (this._threadsAlive()) {
            console.log('[vmguard] stopAll ineffective -> hard freeze');
            this._hardFreeze(reason);
          }
        }, 300);
      }
      try { if (this._rt && this._rt.startHats) this._rt.startHats('vmguard_whenTampered'); } catch (e) {}
    }

    _threadsAlive() {
      try {
        const rt = this._runtime();
        if (!rt) return false;
        if (rt._threads && rt._threads.length > 0) return true;
        if (rt.sequencer && rt.sequencer.activeThread) return true;
      } catch (e) {}
      return false;
    }

    _hardFreeze(reason) {
      if (!this._frozen) {
        this._frozen = true;
        const rt = this._runtime();
        try { if (rt && rt._threads) rt._threads.length = 0; } catch (e) {}
        try { if (rt && rt.sequencer) rt.sequencer.activeThread = null; } catch (e) {}
        try { if (rt && typeof rt.pause === 'function') rt.pause(); } catch (e) {}
        this._freezeInput();
        this._issues.push('stop 失效，已直接冻结');
        if (this._issues.length > 8) this._issues.shift();
        console.log('[vmguard] runtime frozen');
      }
      this._overlay(reason, '已直接冻结');
    }

    _freezeInput() {
      if (this._freezeH) return;
      this._freezeH = (ev) => {
        try {
          if (ev.cancelable) ev.preventDefault();
          ev.stopImmediatePropagation();
        } catch (e) {}
      };
      const types = ['keydown', 'keyup', 'keypress', 'mousedown', 'mouseup', 'mousemove',
        'pointerdown', 'pointerup', 'touchstart', 'touchmove', 'wheel', 'contextmenu', 'dragstart'];
      for (let i = 0; i < types.length; i++) {
        try { window.addEventListener(types[i], this._freezeH, true); } catch (e) {}
      }
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
      if (now - this._lastScript >= 550) {
        this._lastScript = now;
        const s = this._scriptHit();
        if (s) return s;
        const gm = this._gmHit();
        if (gm) return gm;
        const p = this._panelScan();
        if (p) return p;
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
      if (!this._active && !force) {
        if (this._blockAllFloats || this._panelKeys.length) {
          const p = this._panelScan();
          if (p) this._kill(p);
        }
        return;
      }
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
          this._buildCodes();
          this._writeBeat(true);
        }
        const q = this._quick(now);
        if (q) { this._hook = q; this._kill(q); return; }
        if (now - this._lastSafe >= 700) {
          this._lastSafe = now;
          this._safeSample(now);
          this._safeRender();
        }
        const u = this._suspHit();
        if (u) { this._hook = u; this._kill(u); return; }
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
            vars.forEach((v) => {
              if (v) out.push({ obj: v, target: t, vid: String(v.id || '') });
            });
          } else {
            for (const id in vars) {
              const v = vars[id];
              if (v) out.push({ obj: v, target: t, vid: String(v.id || id) });
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
        rec.vid = found.vid || rec.vid;
        return rec;
      }
      const rec = {
        name: canon,
        obj: found.obj,
        target: found.target,
        vid: found.vid || '',
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
      if (!names.length) return;
      this._safeCycle++;
      const deep = (this._safeCycle % 8) === 0;
      for (let i = 0; i < names.length; i++) {
        const rec = this._safe[names[i]];
        if (!rec.obj) {
          const f = this._findVar(rec.name);
          if (!f) continue;
          rec.obj = f.obj;
          rec.target = f.target;
          rec.vid = f.vid || rec.vid;
          rec.patched = null;
          this._safePatch(rec);
          continue;
        }
        if (deep && rec.vid && rec.target && !this._stillVar(rec)) {
          const f = this._findVar(rec.name);
          if (!f) continue;
          rec.obj = f.obj;
          rec.target = f.target;
          rec.vid = f.vid || rec.vid;
          rec.patched = null;
          this._safePatch(rec);
          continue;
        }
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

    _stillVar(rec) {
      try {
        const vars = rec.target && rec.target.variables;
        return !!(vars && vars[rec.vid] === rec.obj);
      } catch (e) {
        return true;
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
      let floats = '';
      const fl = this._floatList || [];
      for (let i = 0; i < fl.length; i++) {
        floats += '<div style="color:#9aa7bd;font:400 10px/1.6 ui-monospace,Consolas,monospace;' +
          'overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + esc(fl[i]) + '</div>';
      }
      if (!floats) floats = '<div style="color:#7a8296;font:400 10px/1.6 ui-monospace,monospace">无</div>';
      const probeN = this._cap && this._cap.fns ? Object.keys(this._cap.fns).length : 0;
      const codeAt = this._stat.codeAt ? new Date(this._stat.codeAt).toLocaleTimeString() : '未核实';
      const lastIssue = this._issues.length ? this._issues[this._issues.length - 1] : '无';
      const sig = this._safeMode + '|' + this._warnTotal() + '|' + this._stat.kills + '|' +
        this._stat.floats + '|' + this._codeTotal + '|' + this._issues.length + '|' + rows + '|' + fl.join('|');
      const stamp = Date.now();
      if (sig === this._safeSig && stamp - this._safeRenderAt < 1000) return;
      this._safeSig = sig;
      this._safeRenderAt = stamp;
      el.innerHTML =
        '<div style="font:700 12px/1.6 ui-monospace,Consolas,monospace;color:#9aa7bd;letter-spacing:.06em;display:flex;justify-content:space-between;align-items:center;gap:8px">' +
        '<span>数据看板</span>' +
        '<button id="vmguard-code-btn" type="button" style="pointer-events:auto;cursor:pointer;background:transparent;' +
        'border:1px solid rgba(154,167,189,.6);color:#c9d3e4;font:600 10px/1.5 ui-monospace,Consolas,monospace;' +
        'padding:2px 6px">获得编号</button>' +
        '<button id="vmguard-float-btn" type="button" style="pointer-events:auto;cursor:pointer;background:transparent;' +
        'border:1px solid rgba(154,167,189,.6);color:#c9d3e4;font:600 10px/1.5 ui-monospace,Consolas,monospace;' +
        'padding:2px 6px;margin-left:4px">复制特征</button>' +
        '</div>' +
        '<div style="color:#8b94a8;font:400 11px/1.6 ui-monospace,Consolas,monospace;margin:2px 0 4px">安全变量 · ' +
        esc(this._safeMode) + ' · 警告 ' + this._warnTotal() + '</div>' +
        (rows || '<div style="color:#7a8296;font:400 12px ui-monospace,monospace">未设定安全变量</div>') +
        '<div style="margin-top:6px;padding-top:4px;border-top:1px solid rgba(255,255,255,.18);' +
        'font:700 10px/1.6 ui-monospace,Consolas,monospace;color:#9aa7bd">悬浮窗 ' + fl.length + '</div>' +
        floats +
        '<div style="margin-top:6px;padding-top:4px;border-top:1px solid rgba(255,255,255,.18);font:400 11px/1.7 ui-monospace,Consolas,monospace;color:#9aa7bd">' +
        '积木 ' + this._codeTotal + ' 块 / ' + kinds + ' 类<br>' +
        '编号核实 ' + esc(codeAt) + '<br>' +
        '探针 ' + probeN + ' · 拦截 ' + this._stat.kills + '<br>' +
        '浮窗拦截 ' + this._stat.floats + '<br>' +
        '最近 ' + esc(String(lastIssue).slice(0, 52)) +
        '</div>';
    }

    _copyText(text) {
      const done = () => { this._safeToast('编号已复制'); };
      const fb = () => {
        try {
          const ta = document.createElement('textarea');
          ta.value = text;
          ta.style.cssText = 'position:fixed;opacity:0;left:-9999px';
          document.body.appendChild(ta);
          ta.select();
          try { document.execCommand('copy'); } catch (e) {}
          ta.remove();
        } catch (e) {}
        done();
      };
      try {
        if (navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(text).then(done, fb);
          return;
        }
      } catch (e) {}
      fb();
    }

    _copyCodes() {
      try {
        this._buildCodes();
        const ops = Object.keys(this._codeTable || {});
        ops.sort((a, c) => Number(this._codeTable[a].code) - Number(this._codeTable[c].code));
        const lines = [];
        for (let i = 0; i < ops.length; i++) {
          lines.push(this._codeTable[ops[i]].code + ' ' + ops[i]);
        }
        this._copyText(lines.join('\n'));
      } catch (e) {}
    }

    _copyFloatFeatures() {
      try {
        const list = this._floats();
        const lines = [];
        const seen = {};
        for (let i = 0; i < list.length; i++) {
          const label = list[i].label;
          if (!label || seen[label]) continue;
          seen[label] = 1;
          lines.push(label);
        }
        if (!lines.length) {
          this._safeToast('当前没有悬浮窗');
          return;
        }
        this._copyText(lines.join('\n'));
        this._safeToast('已复制 ' + lines.length + ' 条悬浮窗特征');
      } catch (e) {}
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
          el.addEventListener('click', (ev) => {
            const id = ev && ev.target && ev.target.id;
            if (id === 'vmguard-code-btn') this._copyCodes();
            else if (id === 'vmguard-float-btn') this._copyFloatFeatures();
          });
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
        const t = rows[i].t;
        const tname = String((t && t.getName && t.getName()) || (t && t.name) || (t && t.id) || '');
        for (const id in blocks) {
          const v = blocks[id];
          if (!v || !v.opcode) continue;
          const op = String(v.opcode);
          counts[op] = (counts[op] || 0) + 1;
          list.push({ id: id, op: op, target: tname });
        }
      }
      list.sort((a, c) => (a.id < c.id ? -1 : a.id > c.id ? 1 : 0));
      const ops = Object.keys(counts).sort((a, c) => {
        if (counts[c] !== counts[a]) return counts[c] - counts[a];
        return a < c ? -1 : a > c ? 1 : 0;
      });
      const table = {};
      for (let i = 0; i < ops.length; i++) {
        table[ops[i]] = { code: String(i + 1), count: counts[ops[i]] };
      }
      const seq = {};
      const map = {};
      for (let i = 0; i < list.length; i++) {
        const it = list[i];
        seq[it.op] = (seq[it.op] || 0) + 1;
        const c = table[it.op].code;
        map[it.id] = { op: it.op, code: c, serial: c + '-' + seq[it.op], target: it.target };
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
      this._scriptSnap = null;
      this._scriptCount = 0;
      try { this._scriptCount = document.querySelectorAll('script').length; } catch (e) {}
      this._capture();
      try { const rr = this._runtime(); this._stopRef = rr && rr.stopAll; } catch (e) {}
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
      this._scriptSnap = null;
      this._scriptCount = 0;
      try { this._scriptCount = document.querySelectorAll('script').length; } catch (e) {}
      this._capture();
      try { const rr = this._runtime(); this._stopRef = rr && rr.stopAll; } catch (e) {}
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
      this._buildCodes();
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

    safeWrites(args) {
      return this._warnTotal();
    }

    _warnTotal() {
      let n = this._stat.warns;
      const names = Object.keys(this._safe);
      for (let i = 0; i < names.length; i++) {
        const rec = this._safe[names[i]];
        if (rec && rec.blocks) n += rec.blocks;
      }
      return n;
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
      this._doKill('积木调用：' + String((args && args.WHY) || ''));
    }
  }

  E.register(new VMGuard(R));
})(Scratch);
