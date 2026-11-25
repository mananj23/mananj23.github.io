// Arena engine: iterated prisoner's dilemma with noise.
// Every strategy is a small finite-state machine, so expected match payoffs are computed
// exactly by propagating the joint state distribution: no sampling, no seed sensitivity.
// Runs in a Web Worker in the page and in Node for tests.
(function (root) {
  'use strict';
  var C = 0, D = 1;
  var PAY = [[3, 0], [5, 1]]; // [my][their]: R=3, S=0, T=5, P=1

  // A machine: { start, pc(s) -> P(intend C), next(s, my, their) -> state }
  function memOne(p, first) { // states: 0..3 last outcome (my*2+their), 4 = start
    return { start: 4, pc: function (s) { return s === 4 ? first : p[s]; }, next: function (s, m, t) { return m * 2 + t; } };
  }
  function always(q) { return { start: 0, pc: function () { return q; }, next: function () { return 0; } }; }

  var LIB = {
    TFT:    { name: 'Tit for Tat', short: 'TFT', rule: 'Cooperates first, then copies your last move.', m: memOne([1, 0, 1, 0], 1) },
    GTFT:   { name: 'Generous Tit for Tat', short: 'GTFT', rule: 'Copies your last move but forgives a defection one time in three.', m: memOne([1, 1 / 3, 1, 1 / 3], 1) },
    TF2T:   { name: 'Tit for Two Tats', short: 'TF2T', rule: 'Defects only after you defect twice in a row.', m: { start: 0, pc: function (s) { return s >= 2 ? 0 : 1; }, next: function (s, m, t) { return t === D ? Math.min(s + 1, 2) : 0; } } },
    WSLS:   { name: 'Win-Stay, Lose-Shift', short: 'WSLS', rule: 'Repeats its move after scoring 3 or 5; switches after scoring 0 or 1.', m: memOne([1, 0, 0, 1], 1) },
    GRIM:   { name: 'Grim Trigger', short: 'Grim', rule: 'Cooperates until you defect once, then defects forever.', m: { start: 0, pc: function (s) { return s ? 0 : 1; }, next: function (s, m, t) { return s || t === D ? 1 : 0; } } },
    // Prober: opens C, D, C, C. If you defected in rounds 2–4 it plays Tit for Tat; otherwise it defects forever.
    // states: 0..3 opening index with flag in bit 4 (16); 20 = TFT mode after their C, 21 = TFT mode after their D; 30 = defect forever
    PROBER: { name: 'Prober', short: 'Prober', rule: 'Opens C, D, C, C. If you hit back during the opening it plays Tit for Tat; if not, it defects forever.', m: {
      start: 0,
      pc: function (s) { if (s < 20) { var i = s & 15; return i === 1 ? 0 : 1; } if (s === 20) return 1; if (s === 21) return 0; return 0; },
      next: function (s, m, t) {
        if (s < 20) {
          var i = s & 15, flag = (s & 16) || (i >= 1 && t === D ? 16 : 0);
          if (i < 3) return (i + 1) | flag;
          return flag ? (t === D ? 21 : 20) : 30;
        }
        if (s === 30) return 30;
        return t === D ? 21 : 20;
      } } },
    EXTORT: { name: 'Extort-2', short: 'Extort', rule: 'A zero-determinant extortioner: its gain above 1 point is always twice yours.', m: memOne([8 / 9, 1 / 2, 1 / 3, 0], 1) },
    ZDGTFT: { name: 'ZD Generous', short: 'ZD-Gen', rule: 'A generous zero-determinant strategy: it forgives often and never out-scores you.', m: memOne([1, 1 / 8, 1, 1 / 4], 1) },
    ALLD:   { name: 'Always Defect', short: 'AllD', rule: 'Defects every round.', m: always(0) },
    ALLC:   { name: 'Always Cooperate', short: 'AllC', rule: 'Cooperates every round.', m: always(1) },
    RAND:   { name: 'Random', short: 'Random', rule: 'Flips a fair coin every round.', m: always(0.5) },
    ALT:    { name: 'Alternator', short: 'Alt', rule: 'Plays C, D, C, D… whatever you do.', m: { start: 0, pc: function (s) { return s ? 0 : 1; }, next: function (s) { return 1 - s; } } }
  };

  // exact expected per-round payoffs and cooperation over `turns` rounds with execution noise eps
  function match(ma, mb, turns, eps) {
    var dist = new Map(); dist.set(ma.start + '|' + mb.start, { a: ma.start, b: mb.start, p: 1 });
    var ea = 0, eb = 0, ca = 0, cb = 0;
    for (var t = 0; t < turns; t++) {
      var nd = new Map();
      dist.forEach(function (st) {
        var qa = ma.pc(st.a), qb = mb.pc(st.b);
        qa = qa * (1 - eps) + (1 - qa) * eps; qb = qb * (1 - eps) + (1 - qb) * eps;
        for (var x = 0; x < 2; x++) for (var y = 0; y < 2; y++) {
          var pr = st.p * (x === C ? qa : 1 - qa) * (y === C ? qb : 1 - qb);
          if (pr < 1e-15) continue;
          ea += pr * PAY[x][y]; eb += pr * PAY[y][x];
          if (x === C) ca += pr; if (y === C) cb += pr;
          var na = ma.next(st.a, x, y), nb = mb.next(st.b, y, x), key = na + '|' + nb, o = nd.get(key);
          if (o) o.p += pr; else nd.set(key, { a: na, b: nb, p: pr });
        }
      });
      dist = nd;
    }
    return { sa: ea / turns, sb: eb / turns, ca: ca / turns, cb: cb / turns };
  }

  function matrix(machines, turns, eps) {
    var n = machines.length, M = [], K = [];
    for (var i = 0; i < n; i++) { M.push(new Array(n).fill(0)); K.push(new Array(n).fill(0)); }
    for (var i2 = 0; i2 < n; i2++) for (var j = i2; j < n; j++) {
      var r = match(machines[i2], machines[j], turns, eps);
      M[i2][j] = r.sa; M[j][i2] = r.sb; K[i2][j] = r.ca; K[j][i2] = r.cb;
    }
    return { M: M, K: K };
  }

  function replicate(M, x0, gens) {
    var n = x0.length, x = x0.slice(), out = [x.slice()];
    for (var g = 0; g < gens; g++) {
      var f = new Array(n).fill(0), fbar = 0;
      for (var i = 0; i < n; i++) { for (var j = 0; j < n; j++) f[i] += M[i][j] * x[j]; fbar += x[i] * f[i]; }
      var s = 0;
      for (var k = 0; k < n; k++) { x[k] = x[k] * f[k] / fbar; if (x[k] < 1e-7) x[k] = 0; s += x[k]; }
      for (var k2 = 0; k2 < n; k2++) x[k2] /= s;
      out.push(x.slice());
    }
    return out;
  }

  // the three challenges, evaluated for a memory-one agent p (+ first move)
  var FIELD = ['TFT', 'GTFT', 'TF2T', 'WSLS', 'GRIM', 'PROBER', 'EXTORT', 'ZDGTFT', 'ALLD', 'ALLC', 'RAND', 'ALT'];
  var HOSTILE = { keys: ['ALLD', 'EXTORT', 'RAND', 'PROBER'], x0: [0.35, 0.35, 0.15, 0.14, 0.01] };
  var SETTINGS = { turns: 200, eps: 0.05, gens: 300 };

  function evaluate(p, first, opts) {
    opts = opts || SETTINGS;
    var me = memOne(p, first);
    var ms = FIELD.map(function (k) { return LIB[k].m; }).concat([me]);
    var n = ms.length, mk = matrix(ms, opts.turns, opts.eps);
    var avg = mk.M.map(function (r) { return r.reduce(function (a, b) { return a + b; }, 0) / n; });
    var rank = 1 + avg.filter(function (v) { return v > avg[n - 1] + 1e-12; }).length;
    var evo = replicate(mk.M, new Array(n).fill(1 / n), opts.gens);
    var end = evo[evo.length - 1], top = end.indexOf(Math.max.apply(null, end));
    var hm = HOSTILE.keys.map(function (k) { return LIB[k].m; }).concat([me]);
    var hk = matrix(hm, opts.turns, opts.eps), hevo = replicate(hk.M, HOSTILE.x0, opts.gens);
    var hend = hevo[hevo.length - 1][HOSTILE.keys.length];
    return {
      names: FIELD.concat(['YOU']), M: mk.M, K: mk.K, avg: avg, rank: rank, evo: evo, hevo: hevo, hostileKeys: HOSTILE.keys.concat(['YOU']),
      share: end[n - 1], topIndex: top,
      pass: [rank === 1, top === n - 1, hend > 0.5], hostileShare: hend
    };
  }

  // quick head-to-head preview (no evolution) for live slider feedback
  function preview(p, first, opts) {
    opts = opts || SETTINGS;
    var me = memOne(p, first);
    return FIELD.map(function (k) { var r = match(me, LIB[k].m, opts.turns, opts.eps); return { key: k, you: r.sa, them: r.sb, coop: r.ca }; });
  }

  // a sampled player for live duels
  function sampler(m) { var s = m.start; return { act: function (r) { return r() < m.pc(s) ? C : D; }, see: function (my, their) { s = m.next(s, my, their); } }; }

  function rng(seed) { var a = seed >>> 0; return function () { a = (a + 0x6D2B79F5) >>> 0; var t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

  var api = { C: C, D: D, PAY: PAY, LIB: LIB, FIELD: FIELD, HOSTILE: HOSTILE, SETTINGS: SETTINGS, memOne: memOne, match: match, matrix: matrix, replicate: replicate, evaluate: evaluate, preview: preview, sampler: sampler, rng: rng };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.Arena = api;
})(typeof self !== 'undefined' ? self : this);
