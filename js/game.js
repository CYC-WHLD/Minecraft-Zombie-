/* ============================================================
   末日晶核 — 遊戲主程式（完整整合版 v8）
   ============================================================ */
import * as THREE from 'three';

const CFG = {
  PLAYER_HEIGHT: 1.8, PLAYER_RADIUS: 0.3,
  GRAVITY: -25, MOVE_SPEED: 6, JUMP_SPEED: 8,
  PLAYER_MAX_HP: 100,
  MAX_ZOMBIES: 15, SPAWN_INTERVAL: 2.0,
  ZOMBIE_ATTACK_RANGE: 1.6, ZOMBIE_ATTACK_CD: 1.0,
  CORE_PICKUP_RANGE: 2.5, MAX_STEP_HEIGHT: 2,
};

let currentMouseSens = 0.0022;
const STORAGE_KEY = 'bw_best_time';

const State = Object.freeze({
  MENU:'menu', PLAYING:'playing', PAUSED:'paused',
  INVENTORY:'inventory', RESULT:'result',
});
let state = State.MENU;

const $ = (s) => document.querySelector(s);
const dom = {
  canvas: $('#game-canvas'),
  hud: $('#hud'),
  timerValue: $('#hud-timer-value'),
  hearts: $('#hud-hearts'),
  coreWhite: $('#hud-core-white'),
  coreBlue: $('#hud-core-blue'),
  corePurple: $('#hud-core-purple'),
  coreRed: $('#hud-core-red'),
  coreKey: $('#hud-core-key'),
  ammoDisplay: $('#ammo-display'),
  overlayMenu: $('#overlay-menu'),
  overlayPause: $('#overlay-pause'),
  overlayResult: $('#overlay-result'),
  overlayInventory: $('#overlay-inventory'),
  resultTitle: $('#result-title'),
  resultText: $('#result-text'),
  resultBest: $('#result-best'),
  btnStart: $('#btn-start'),
  btnResume: $('#btn-resume'),
  btnRestart: $('#btn-restart'),
  btnCloseInventory: $('#btn-close-inventory'),
  invGrid: $('#inv-grid'),
  craftGrid: $('#craft-grid'),
  craftResultCell: $('#craft-result-cell'),
  scopeOverlay: $('#scope-overlay'),
  scopeCanvas: $('#scope-canvas'),
};

let renderer, scene, camera, headLamp;
let weaponRig = null;
let gunGroup = null;
let handGroup = null;
let handMesh = null;
let muzzleFlash = null;

const player = {
  pos: new THREE.Vector3(64.5, 25, 64.5),
  vel: new THREE.Vector3(),
  onGround: false,
  yaw: 0, pitch: 0,
  hp: CFG.PLAYER_MAX_HP,
};
const keys = Object.create(null);
let elapsedTime = 0;
let rafId = 0;
let lastTime = 0;

/* ---------------- 武器定義 ---------------- */
const WEAPONS = {
  pistol: {
    name:'手槍', damage:28, fireRate:320, range:40,
    magSize:12, reloadTime:1.0, spread:0.008,
    color:0x4a4a4a, adsFov:55, sightY:0.069,
    headshotMultiplier:4.0,
  },
  smg: {
    name:'衝鋒槍', damage:16, fireRate:90, range:35,
    magSize:30, reloadTime:1.5, spread:0.025,
    color:0x3a3a3a, adsFov:50, sightY:0.084,
    headshotMultiplier:3.0,
  },
  rifle: {
    name:'步槍', damage:34, fireRate:140, range:60,
    magSize:30, reloadTime:1.4, spread:0.012, // 彈藥改為 30
    color:0x2a2a2a, adsFov:45, sightY:0.084, // 機瞄高度與 SMG 相同
    headshotMultiplier:3.0,
  },
  sniper: {
    name:'狙擊槍', damage:120, fireRate:1100, range:120,
    magSize:5, reloadTime:2.2, spread:0.001,
    color:0x1a1a1a, adsFov:25, sightY:0.124,
    headshotMultiplier:3.0,
    useScopeOverlay:true,
  },
  rocket: {
    name:'火箭筒', damage:0, fireRate:1500, range:200,
    magSize:1, reloadTime:3.0, spread:0.005,
    color:0x2a3a2a, adsFov:60, sightY:0.114,
    explosive:true,
    explosionInnerRadius:3, explosionOuterRadius:6,
    explosionInnerDamage:9999, explosionOuterMaxDamage:200,
  },
};
const weaponOrder = ['pistol','smg','rifle','sniper','rocket'];

const ammo = {
  pistol:{ mag:12, reloading:false, reloadEnd:0 },
  smg:   { mag:30, reloading:false, reloadEnd:0 },
  rifle: { mag:30, reloading:false, reloadEnd:0 }, // 同步為 30
  sniper:{ mag:5,  reloading:false, reloadEnd:0 },
  rocket:{ mag:1,  reloading:false, reloadEnd:0 },
};

let currentSlot = 0;
let currentWeapon = 'pistol';
const blockOrderMap = { 5:3, 6:6, 7:8, 8:9 };

let isAiming = false;
const HIP_FOV = 75;
let currentFov = HIP_FOV;
const HIP_POS = { x:0.22, y:-0.26, z:-0.55 };
const ADS_Z = -0.55;

const inventory = { white:0, blue:0, purple:0, red:0, key:0 };

const CHUNK = 16, WORLD_W = 128, WORLD_D = 128, WORLD_H = 40;
const BLOCK = Object.freeze({
  AIR:0, GRASS:1, DIRT:2, STONE:3, COAL:4, DIAMOND:5,
  WOOD:6, LEAF:7, SAND:8, IRON:9, GOLD:10,
});
const world = new Uint8Array(WORLD_W * WORLD_H * WORLD_D);
const idx = (x,y,z) => x + z * WORLD_W + y * WORLD_W * WORLD_D;
const chunkMeshes = new Map();

function makeNoise2D(seed) {
  const perm = new Uint8Array(512);
  const p = new Uint8Array(256);
  for (let i = 0; i < 256; i++) p[i] = i;
  let s = seed || 1;
  for (let i = 255; i > 0; i--) {
    s = (s * 16807) % 2147483647;
    const j = s % (i + 1);
    const t = p[i]; p[i] = p[j]; p[j] = t;
  }
  for (let i = 0; i < 512; i++) perm[i] = p[i & 255];
  const fade = (t) => t * t * t * (t * (t * 6 - 15) + 10);
  const lerp = (a,b,t) => a + t * (b - a);
  const grad = (h,x,y) => {
    switch (h & 7) {
      case 0: return x + y; case 1: return x - y;
      case 2: return -x + y; case 3: return -x - y;
      case 4: return x; case 5: return -x;
      case 6: return y; default: return -y;
    }
  };
  return function (x,y) {
    const X = Math.floor(x) & 255, Y = Math.floor(y) & 255;
    const xf = x - Math.floor(x), yf = y - Math.floor(y);
    const u = fade(xf), v = fade(yf);
    const aa = perm[perm[X] + Y], ab = perm[perm[X] + Y + 1];
    const ba = perm[perm[X + 1] + Y], bb = perm[perm[X + 1] + Y + 1];
    const x1 = lerp(grad(aa, xf, yf), grad(ba, xf - 1, yf), u);
    const x2 = lerp(grad(ab, xf, yf - 1), grad(bb, xf - 1, yf - 1), u);
    return lerp(x1, x2, v);
  };
}

function makeTile(base, variance, size) {
  size = size || 16;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  const img = ctx.createImageData(size, size);
  for (let i = 0; i < size * size; i++) {
    const n = (Math.random() - 0.5) * variance * 2;
    img.data[i*4+0] = Math.max(0, Math.min(255, base[0] + n));
    img.data[i*4+1] = Math.max(0, Math.min(255, base[1] + n));
    img.data[i*4+2] = Math.max(0, Math.min(255, base[2] + n));
    img.data[i*4+3] = 255;
  }
  ctx.putImageData(img, 0, 0);
  return c;
}

function makeGrassSide(size) {
  size = size || 16;
  const out = document.createElement('canvas');
  out.width = out.height = size;
  const ctx = out.getContext('2d');
  const grass = makeTile([80, 130, 50], 18, size);
  const dirt = makeTile([100, 75, 55], 18, size);
  ctx.drawImage(dirt, 0, 0);
  for (let x = 0; x < size; x++) {
    const h = 3 + (Math.random() < 0.45 ? 1 : 0);
    ctx.drawImage(grass, x, 0, 1, h, x, 0, 1, h);
  }
  return out;
}

function makeWoodTexture(size) {
  size = size || 16;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const ring = Math.sin((x/size) * Math.PI * 3) * 12;
      const grain = (Math.random() - 0.5) * 10;
      const v = 100 + ring + grain;
      ctx.fillStyle = `rgb(${v|0},${(v*0.65)|0},${(v*0.35)|0})`;
      ctx.fillRect(x, y, 1, 1);
    }
  }
  return c;
}

function makeLeafTexture(size) {
  size = size || 16;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      if (Math.random() < 0.2) continue;
      const g = 50 + Math.random() * 60;
      ctx.fillStyle = `rgb(${(g*0.4)|0},${g|0},${(g*0.3)|0})`;
      ctx.fillRect(x, y, 1, 1);
    }
  }
  return c;
}

function makeOreTexture(oreColor, darkColor, size) {
  size = size || 16;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  ctx.drawImage(makeTile([110,110,110], 14, size), 0, 0);
  const count = 6 + Math.floor(Math.random() * 4);
  for (let i = 0; i < count; i++) {
    const x = Math.floor(Math.random()*size), y = Math.floor(Math.random()*size);
    const w = 1 + Math.floor(Math.random()*2), h = 1 + Math.floor(Math.random()*2);
    ctx.fillStyle = `rgb(${oreColor[0]},${oreColor[1]},${oreColor[2]})`;
    ctx.fillRect(x, y, w, h);
    ctx.fillStyle = `rgb(${darkColor[0]},${darkColor[1]},${darkColor[2]})`;
    ctx.fillRect(x, y + h, w, 1);
  }
  return c;
}

/* ---------------- 精緻槍枝貼皮（移除步槍瞄準鏡紋理） ---------------- */
function makeGunSkinTexture(weaponKey, size) {
  size = size || 128;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  const S = size;

  const palettes = {
    pistol:{ base:'#4a4a4a', dark:'#2a2a2a', light:'#6a6a6a', hi:'#8a8a8a', accent:'#c0392b' },
    smg:   { base:'#3a3a3a', dark:'#1a1a1a', light:'#5a5a5a', hi:'#7a7a7a', accent:'#6a9a4a' },
    rifle: { base:'#2a2a2a', dark:'#0a0a0a', light:'#4a4a4a', hi:'#6a6a6a', accent:'#4a7a9a' },
    sniper:{ base:'#1a2a1a', dark:'#0a1a0a', light:'#3a4a3a', hi:'#5a6a5a', accent:'#5a8a5a' },
    rocket:{ base:'#2a3a2a', dark:'#1a2a1a', light:'#3a4a3a', hi:'#5a6a5a', accent:'#c0392b' },
  };
  const pal = palettes[weaponKey] || palettes.pistol;

  ctx.fillStyle = pal.base;
  ctx.fillRect(0, 0, S, S);

  for (let i = 0; i < S * S * 0.15; i++) {
    const x = Math.random() * S | 0;
    const y = Math.random() * S | 0;
    ctx.fillStyle = Math.random() < 0.5 ? pal.dark : pal.light;
    ctx.globalAlpha = 0.35;
    ctx.fillRect(x, y, 1, 1);
  }
  ctx.globalAlpha = 1;

  if (weaponKey === 'pistol') {
    for (let y = S * 0.55; y < S; y++) {
      for (let x = S * 0.08; x < S * 0.92; x++) {
        if ((x + y) % 6 === 0 || (x - y + S * 2) % 6 === 0) {
          ctx.fillStyle = pal.dark;
          ctx.fillRect(x | 0, y | 0, 1, 1);
        }
      }
    }
    const screws = [[S*0.2,S*0.2],[S*0.8,S*0.2],[S*0.2,S*0.45],[S*0.8,S*0.45]];
    screws.forEach(([x,y]) => {
      ctx.fillStyle = pal.hi; ctx.fillRect(x-2, y-2, 4, 4);
      ctx.fillStyle = pal.dark; ctx.fillRect(x-1, y-1, 2, 2);
    });
    ctx.fillStyle = pal.accent;
    ctx.fillRect(S/2 - 2, S*0.12, 4, 4);
    ctx.fillStyle = pal.hi;
    ctx.globalAlpha = 0.4;
    ctx.fillRect(0, S*0.32, S, 2);
    ctx.globalAlpha = 1;
    for (let i = 0; i < 30; i++) {
      ctx.fillStyle = 'rgba(0,0,0,0.4)';
      ctx.fillRect(Math.random()*S, Math.random()*S, Math.random()*8+2, 1);
    }
  } else if (weaponKey === 'smg') {
    ctx.fillStyle = pal.accent;
    ctx.globalAlpha = 0.55;
    for (let y = S * 0.15; y < S * 0.5; y++) {
      for (let x = 0; x < S; x++) {
        if ((x + y * 2) % 16 < 6) ctx.fillRect(x, y | 0, 1, 1);
      }
    }
    ctx.globalAlpha = 1;
    for (let y = S * 0.6; y < S * 0.95; y += 4) {
      ctx.fillStyle = pal.dark;
      ctx.fillRect(S*0.15, y | 0, S*0.7, 1);
    }
    [[S*0.15,S*0.18],[S*0.85,S*0.18]].forEach(([x,y]) => {
      ctx.fillStyle = pal.hi; ctx.fillRect(x-2, y-2, 4, 4);
    });
    for (let i = 0; i < 40; i++) {
      ctx.fillStyle = 'rgba(0,0,0,0.35)';
      ctx.fillRect(Math.random()*S, Math.random()*S, Math.random()*10+2, 1);
    }
  } else if (weaponKey === 'rifle') {
    // 移除圓環瞄具紋理，保留裝飾條
    ctx.fillStyle = pal.accent;
    ctx.globalAlpha = 0.65;
    ctx.fillRect(0, S*0.28, S, 4);
    ctx.fillRect(0, S*0.44, S, 2);
    ctx.globalAlpha = 1;
    for (let y = S * 0.75; y < S; y++) {
      for (let x = S * 0.15; x < S * 0.85; x += 3) {
        ctx.fillStyle = pal.dark;
        ctx.fillRect(x | 0, y | 0, 2, 1);
      }
    }
    for (let i = 0; i < 50; i++) {
      ctx.fillStyle = 'rgba(0,0,0,0.4)';
      ctx.fillRect(Math.random()*S, Math.random()*S, Math.random()*12+2, 1);
    }
    [[S*0.1,S*0.35],[S*0.9,S*0.35],[S*0.1,S*0.55],[S*0.9,S*0.55]].forEach(([x,y]) => {
      ctx.fillStyle = pal.hi; ctx.fillRect(x-1, y-1, 3, 3);
    });
  } else if (weaponKey === 'sniper') {
    for (let i = 0; i < 40; i++) {
      const x = Math.random() * S, y = Math.random() * S;
      const w = Math.random() * 16 + 6, h = Math.random() * 12 + 4;
      const shades = [pal.dark, pal.light, '#2a4a2a', '#1a3a1a', '#3a5a3a'];
      ctx.fillStyle = shades[i % shades.length];
      ctx.globalAlpha = 0.45 + Math.random() * 0.3;
      ctx.beginPath();
      ctx.ellipse(x, y, w, h, Math.random() * Math.PI, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
    ctx.strokeStyle = pal.hi;
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.arc(S/2, S*0.18, S*0.08, 0, Math.PI * 2);
    ctx.stroke();
    ctx.fillStyle = '#6a9a6a';
    ctx.globalAlpha = 0.8;
    ctx.beginPath();
    ctx.arc(S/2, S*0.18, S*0.05, 0, Math.PI * 2);
    ctx.fill();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = 'rgba(0,0,0,0.6)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(S/2 - S*0.06, S*0.18);
    ctx.lineTo(S/2 + S*0.06, S*0.18);
    ctx.moveTo(S/2, S*0.18 - S*0.06);
    ctx.lineTo(S/2, S*0.18 + S*0.06);
    ctx.stroke();
  } else if (weaponKey === 'rocket') {
    for (let x = 0; x < S; x += 16) {
      if (x % 32 < 16) {
        ctx.fillStyle = pal.accent;
        ctx.globalAlpha = 0.8;
        ctx.fillRect(x, S*0.2, 8, S*0.2);
      }
    }
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#f7d06b';
    ctx.lineWidth = 3;
    ctx.strokeRect(S*0.25, S*0.4, S*0.5, S*0.25);
    ctx.fillStyle = '#f7d06b';
    ctx.font = 'bold 24px monospace';
    ctx.textAlign = 'center';
    ctx.fillText('!', S/2, S*0.58);
    for (let i = 0; i < 25; i++) {
      const x = Math.random() * S * 0.25;
      const y = S*0.5 + Math.random() * S * 0.5;
      ctx.fillStyle = Math.random() < 0.5 ? '#ffaa00' : '#ff6600';
      ctx.fillRect(x | 0, y | 0, 2, 2);
    }
    for (let i = 0; i < 30; i++) {
      ctx.fillStyle = 'rgba(0,0,0,0.4)';
      ctx.fillRect(Math.random()*S, Math.random()*S, Math.random()*10+2, 1);
    }
  }

  return c;
}

function makeHandSkinTexture(size) {
  size = size || 64;
  const c = document.createElement('canvas');
  c.width = c.height = size;
  const ctx = c.getContext('2d');
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const n = (Math.random() - 0.5) * 18;
      ctx.fillStyle = `rgb(${190+n},${150+n},${120+n})`;
      ctx.fillRect(x, y, 1, 1);
    }
  }
  ctx.fillStyle = 'rgba(80,50,30,0.25)';
  for (let i = 0; i < 4; i++) {
    ctx.fillRect(size*0.2, size*(0.15 + i*0.2), size*0.6, 2);
  }
  return c;
}

function canvasToTexture(canvas) {
  const tex = new THREE.CanvasTexture(canvas);
  tex.magFilter = THREE.NearestFilter;
  tex.minFilter = THREE.NearestFilter;
  tex.wrapS = tex.wrapT = THREE.ClampToEdgeWrapping;
  tex.colorSpace = THREE.SRGBColorSpace;
  return tex;
}

/* ---------------- 物品欄圖示生成器（像素槍枝 + 3D 方塊） ---------------- */
function generateItemIcons() {
  const root = document.documentElement.style;

  // 1. 生成 2D 像素小槍枝
  const makeGunIcon = (type) => {
    const c = document.createElement('canvas');
    c.width = 32; c.height = 32;
    const ctx = c.getContext('2d');
    ctx.fillStyle = '#555'; // 底色
    if (type === 'pistol') {
      ctx.fillRect(10, 12, 14, 6); // 槍管
      ctx.fillRect(18, 18, 6, 8);  // 握把
      ctx.fillStyle = '#222'; ctx.fillRect(10, 12, 3, 6); // 滑套
    } else if (type === 'smg') {
      ctx.fillRect(6, 12, 20, 6);
      ctx.fillRect(18, 18, 5, 10);
      ctx.fillRect(8, 18, 6, 4); // 彈匣
      ctx.fillStyle = '#888'; ctx.fillRect(4, 12, 4, 2); // 槍托
    } else if (type === 'rifle') {
      ctx.fillRect(2, 14, 26, 4);
      ctx.fillRect(18, 18, 5, 8);
      ctx.fillRect(8, 18, 4, 4);
      ctx.fillStyle = '#333'; ctx.fillRect(2, 14, 6, 4); // 護木
    } else if (type === 'sniper') {
      ctx.fillRect(2, 15, 28, 2);
      ctx.fillRect(18, 18, 4, 8);
      ctx.fillStyle = '#222'; ctx.fillRect(10, 10, 12, 4); // 瞄準鏡
      ctx.fillStyle = '#88a'; ctx.fillRect(11, 11, 10, 2);
    } else if (type === 'rocket') {
      ctx.fillRect(4, 12, 22, 8); // 圓筒
      ctx.fillStyle = '#b22'; ctx.fillRect(22, 12, 4, 8); // 彈頭
      ctx.fillStyle = '#222'; ctx.fillRect(12, 20, 4, 8); // 握把
    }
    // 加陰影
    ctx.fillStyle = 'rgba(0,0,0,0.3)';
    ctx.fillRect(0, 28, 32, 4);
    return c.toDataURL();
  };

  root.setProperty('--icon-pistol', `url(${makeGunIcon('pistol')})`);
  root.setProperty('--icon-smg', `url(${makeGunIcon('smg')})`);
  root.setProperty('--icon-rifle', `url(${makeGunIcon('rifle')})`);
  root.setProperty('--icon-sniper', `url(${makeGunIcon('sniper')})`);
  root.setProperty('--icon-rocket', `url(${makeGunIcon('rocket')})`);

  // 2. 生成 3D 等角視角小方塊
  const makeIsoCube = (cTop, cLeft, cRight) => {
    const c = document.createElement('canvas');
    c.width = 32; c.height = 32;
    const ctx = c.getContext('2d');
    
    const drawPoly = (points, color) => {
      ctx.fillStyle = color;
      ctx.beginPath();
      ctx.moveTo(points[0][0], points[0][1]);
      for(let i=1; i<points.length; i++) ctx.lineTo(points[i][0], points[i][1]);
      ctx.closePath();
      ctx.fill();
      ctx.strokeStyle = 'rgba(0,0,0,0.4)';
      ctx.lineWidth = 1;
      ctx.stroke();
    };

    // 頂面
    drawPoly([[16,4], [28,10], [16,16], [4,10]], cTop);
    // 左面
    drawPoly([[4,10], [16,16], [16,28], [4,22]], cLeft);
    // 右面
    drawPoly([[16,16], [28,10], [28,22], [16,28]], cRight);

    return c.toDataURL();
  };

  root.setProperty('--icon-stone-3d', `url(${makeIsoCube('#aaa', '#777', '#555')})`);
  root.setProperty('--icon-wood-3d', `url(${makeIsoCube('#b87', '#965', '#743')})`);
  root.setProperty('--icon-sand-3d', `url(${makeIsoCube('#edc', '#cba', '#a98')})`);
  root.setProperty('--icon-iron-3d', `url(${makeIsoCube('#bcc', '#899', '#677')})`);
}

/* ---------------- 材質建置 ---------------- */
const BLOCK_GEO = new THREE.BoxGeometry(1, 1, 1);
let BLOCK_MAT = null;

function buildMaterials() {
  const mk = (c) => new THREE.MeshLambertMaterial({ map: canvasToTexture(c) });
  const mGrassTop = mk(makeTile([80,130,50], 18));
  const mGrassSide = mk(makeGrassSide(16));
  const mDirt = mk(makeTile([100,75,55], 18));
  const mStone = mk(makeTile([110,110,110], 14));
  const mCoal = mk(makeTile([50,50,50], 22));
  const mDiamond = new THREE.MeshLambertMaterial({
    map: canvasToTexture(makeTile([92,219,213], 30)), emissive: 0x1a4a4a,
  });
  const mWood = mk(makeWoodTexture(16));
  const mLeaf = new THREE.MeshLambertMaterial({
    map: canvasToTexture(makeLeafTexture(16)),
    transparent: true, alphaTest: 0.5, side: THREE.DoubleSide,
  });
  const mSand = mk(makeTile([200,185,130], 16));
  const mIron = mk(makeOreTexture([180,160,140], [80,80,80]));
  const mGold = mk(makeOreTexture([252,220,80], [120,90,20]));

  BLOCK_MAT = {
    [BLOCK.GRASS]: [mGrassSide, mGrassSide, mGrassTop, mDirt, mGrassSide, mGrassSide],
    [BLOCK.DIRT]: [mDirt, mDirt, mDirt, mDirt, mDirt, mDirt],
    [BLOCK.STONE]: [mStone, mStone, mStone, mStone, mStone, mStone],
    [BLOCK.COAL]: [mCoal, mCoal, mCoal, mCoal, mCoal, mCoal],
    [BLOCK.DIAMOND]: [mDiamond, mDiamond, mDiamond, mDiamond, mDiamond, mDiamond],
    [BLOCK.WOOD]: [mWood, mWood, mWood, mWood, mWood, mWood],
    [BLOCK.LEAF]: [mLeaf, mLeaf, mLeaf, mLeaf, mLeaf, mLeaf],
    [BLOCK.SAND]: [mSand, mSand, mSand, mSand, mSand, mSand],
    [BLOCK.IRON]: [mIron, mIron, mIron, mIron, mIron, mIron],
    [BLOCK.GOLD]: [mGold, mGold, mGold, mGold, mGold, mGold],
  };

  const root = document.documentElement.style;
  root.setProperty('--tex-stone', `url(${makeTile([110,110,110], 14).toDataURL()})`);
  root.setProperty('--tex-wood', `url(${makeWoodTexture(16).toDataURL()})`);
  root.setProperty('--tex-sand', `url(${makeTile([200,185,130], 16).toDataURL()})`);
  root.setProperty('--tex-iron', `url(${makeOreTexture([180,160,140], [80,80,80]).toDataURL()})`);
}

function generateWorld() {
  world.fill(BLOCK.AIR);
  const noise = makeNoise2D(1337);

  for (let z = 0; z < WORLD_D; z++) {
    for (let x = 0; x < WORLD_W; x++) {
      const h = noise(x*0.06, z*0.06)*6 + noise(x*0.15, z*0.15)*2;
      const surface = Math.max(4, Math.min(WORLD_H - 4, Math.floor(16 + h)));
      for (let y = 0; y <= surface; y++) {
        let type = BLOCK.STONE;
        if (y === surface) type = BLOCK.GRASS;
        else if (y > surface - 4) type = BLOCK.DIRT;
        if (type === BLOCK.STONE && y < surface) {
          const r = Math.random();
          if (y < 10 && r < 0.010) type = BLOCK.DIAMOND;
          else if (y < 14 && r < 0.028) type = BLOCK.GOLD;
          else if (y < 20 && r < 0.055) type = BLOCK.IRON;
          else if (y < 26 && r < 0.080) type = BLOCK.COAL;
        }
        world[idx(x, y, z)] = type;
      }
      world[idx(x, 0, z)] = BLOCK.STONE;
    }
  }

  for (let i = 0; i < 60; i++) {
    const tx = 3 + Math.floor(Math.random()*(WORLD_W-6));
    const tz = 3 + Math.floor(Math.random()*(WORLD_D-6));
    const ty = findSurfaceY(tx, tz);
    if (ty <= 1 || ty >= WORLD_H - 6) continue;
    if (world[idx(tx, ty-1, tz)] !== BLOCK.GRASS) continue;
    const trunkH = 3 + Math.floor(Math.random()*3);
    for (let h = 0; h < trunkH; h++) {
      if (ty + h < WORLD_H) world[idx(tx, ty+h, tz)] = BLOCK.WOOD;
    }
    const top = ty + trunkH;
    for (let dy = -1; dy <= 1; dy++)
      for (let dx = -2; dx <= 2; dx++)
        for (let dz = -2; dz <= 2; dz++) {
          if (dx === 0 && dz === 0 && dy < 1) continue;
          if (Math.abs(dx) === 2 && Math.abs(dz) === 2) continue;
          if (dy === 1 && (Math.abs(dx) === 2 || Math.abs(dz) === 2)) continue;
          const lx = tx+dx, ly = top+dy, lz = tz+dz;
          if (lx<0||lx>=WORLD_W||lz<0||lz>=WORLD_D) continue;
          if (ly<0||ly>=WORLD_H) continue;
          if (world[idx(lx,ly,lz)] === BLOCK.AIR) world[idx(lx,ly,lz)] = BLOCK.LEAF;
        }
  }

  generateCityBuildings();
  generateStreets();
}

function generateCityBuildings() {
  const templates = [
    { w:9, d:9, h:5, style:'house' },
    { w:11, d:8, h:7, style:'twoStory' },
    { w:8, d:12, h:6, style:'longhouse' },
    { w:14, d:10, h:9, style:'tower' },
  ];
  const buildingCount = 10 + Math.floor(Math.random()*5);
  const occupied = [];
  for (let b = 0; b < buildingCount; b++) {
    const tpl = templates[Math.floor(Math.random()*templates.length)];
    let bx, bz, attempts = 0;
    do {
      bx = 15 + Math.floor(Math.random()*(WORLD_W-30));
      bz = 15 + Math.floor(Math.random()*(WORLD_D-30));
      attempts++;
      if (attempts > 40) break;
    } while (occupied.some(o => Math.abs(o.x-bx) < tpl.w+8 && Math.abs(o.z-bz) < tpl.d+8));
    occupied.push({ x:bx, z:bz });
    buildHouse(bx, bz, tpl);
  }
}

function buildHouse(bx, bz, tpl) {
  const { w, d, h, style } = tpl;
  let maxY = -Infinity;
  for (let x = bx; x < bx + w; x++) {
    if (x < 0 || x >= WORLD_W) continue;
    for (let z = bz; z < bz + d; z++) {
      if (z < 0 || z >= WORLD_D) continue;
      const sy = findSurfaceY(x, z);
      if (sy > maxY) maxY = sy;
    }
  }
  if (!isFinite(maxY) || maxY + h >= WORLD_H - 2) return;
  const floorY = maxY;

  for (let x = bx; x < bx + w; x++) {
    if (x < 0 || x >= WORLD_W) continue;
    for (let z = bz; z < bz + d; z++) {
      if (z < 0 || z >= WORLD_D) continue;
      const sy = findSurfaceY(x, z);
      for (let y = sy; y < floorY; y++) {
        if (y >= 0 && y < WORLD_H) world[idx(x,y,z)] = BLOCK.STONE;
      }
      world[idx(x, floorY-1, z)] = BLOCK.WOOD;
    }
  }

  for (let y = floorY; y < floorY + h; y++) {
    for (let x = bx; x < bx + w; x++) {
      if (x < 0 || x >= WORLD_W) continue;
      for (let z = bz; z < bz + d; z++) {
        if (z < 0 || z >= WORLD_D) continue;
        const isWall = (x === bx || x === bx+w-1 || z === bz || z === bz+d-1);
        if (!isWall) continue;
        const isWindow = (y === floorY+1 || y === floorY+2) &&
                         ((x - bx) % 3 === 1) &&
                         (z === bz || z === bz+d-1);
        if (isWindow) { world[idx(x,y,z)] = BLOCK.AIR; continue; }
        world[idx(x,y,z)] = BLOCK.STONE;
      }
    }
  }

  const doorSide = Math.floor(Math.random()*4);
  const doorW = 2, doorH = 2;
  const doorOffset = 1 + Math.floor(Math.random()*Math.max(1, w - doorW - 2));
  if (doorSide === 0) {
    for (let x = bx+doorOffset; x < bx+doorOffset+doorW; x++)
      for (let y = floorY; y < floorY+doorH; y++)
        if (x >= 0 && x < WORLD_W) world[idx(x,y,bz)] = BLOCK.AIR;
  } else if (doorSide === 1) {
    for (let x = bx+doorOffset; x < bx+doorOffset+doorW; x++)
      for (let y = floorY; y < floorY+doorH; y++)
        if (x >= 0 && x < WORLD_W) world[idx(x,y,bz+d-1)] = BLOCK.AIR;
  } else if (doorSide === 2) {
    for (let z = bz+doorOffset; z < bz+doorOffset+doorW; z++)
      for (let y = floorY; y < floorY+doorH; y++)
        if (z >= 0 && z < WORLD_D) world[idx(bx,y,z)] = BLOCK.AIR;
  } else {
    for (let z = bz+doorOffset; z < bz+doorOffset+doorW; z++)
      for (let y = floorY; y < floorY+doorH; y++)
        if (z >= 0 && z < WORLD_D) world[idx(bx+w-1,y,z)] = BLOCK.AIR;
  }

  if (style === 'twoStory' || style === 'tower') {
    const midY = floorY + Math.floor(h/2);
    for (let x = bx+1; x < bx+w-1; x++)
      for (let z = bz+1; z < bz+d-1; z++)
        if (Math.random() < 0.8) world[idx(x,midY,z)] = BLOCK.WOOD;
    for (let s = 0; s < 3; s++) {
      const sx = bx + 2 + s;
      if (sx < bx + w - 1) {
        world[idx(sx, midY, bz+2)] = BLOCK.AIR;
        world[idx(sx, midY+1, bz+2)] = BLOCK.AIR;
      }
    }
  }

  for (let x = bx; x < bx + w; x++) {
    if (x < 0 || x >= WORLD_W) continue;
    for (let z = bz; z < bz + d; z++) {
      if (z < 0 || z >= WORLD_D) continue;
      const edgeDist = Math.min(x-bx, bx+w-1-x, z-bz, bz+d-1-z);
      if (edgeDist < 2 || Math.random() < 0.7) {
        world[idx(x, floorY+h-1, z)] = BLOCK.WOOD;
      }
    }
  }
}

function generateStreets() {
  for (let i = 0; i < 3; i++) {
    const roadZ = 20 + Math.floor(Math.random()*(WORLD_D-40));
    for (let x = 5; x < WORLD_W - 5; x++) {
      for (let dz = -2; dz <= 2; dz++) {
        const z = roadZ + dz;
        if (z < 0 || z >= WORLD_D) continue;
        for (let y = WORLD_H-1; y >= 0; y--) {
          const b = world[idx(x,y,z)];
          if (b === BLOCK.GRASS || b === BLOCK.DIRT || b === BLOCK.SAND) {
            world[idx(x,y,z)] = (Math.abs(dz) <= 1) ? BLOCK.STONE : BLOCK.SAND;
            break;
          }
          if (b === BLOCK.WOOD || b === BLOCK.LEAF) break;
        }
      }
    }
  }
  for (let i = 0; i < 3; i++) {
    const roadX = 20 + Math.floor(Math.random()*(WORLD_W-40));
    for (let z = 5; z < WORLD_D - 5; z++) {
      for (let dx = -2; dx <= 2; dx++) {
        const x = roadX + dx;
        if (x < 0 || x >= WORLD_W) continue;
        for (let y = WORLD_H-1; y >= 0; y--) {
          const b = world[idx(x,y,z)];
          if (b === BLOCK.GRASS || b === BLOCK.DIRT || b === BLOCK.SAND) {
            world[idx(x,y,z)] = (Math.abs(dx) <= 1) ? BLOCK.STONE : BLOCK.SAND;
            break;
          }
          if (b === BLOCK.WOOD || b === BLOCK.LEAF) break;
        }
      }
    }
  }
}

function isExposed(x, y, z) {
  const nb = [[x+1,y,z],[x-1,y,z],[x,y+1,z],[x,y-1,z],[x,y,z+1],[x,y,z-1]];
  for (let i = 0; i < nb.length; i++) {
    const [nx,ny,nz] = nb[i];
    if (nx<0||nx>=WORLD_W||nz<0||nz>=WORLD_D) return true;
    if (ny < 0) return false;
    if (ny >= WORLD_H) return true;
    if (world[idx(nx,ny,nz)] === BLOCK.AIR) return true;
  }
  return false;
}

function rebuildChunk(cx, cz) {
  const key = `${cx},${cz}`;
  const old = chunkMeshes.get(key);
  if (old) {
    for (const m of old.meshes) { scene.remove(m); m.geometry.dispose(); }
    chunkMeshes.delete(key);
  }
  const byType = new Map();
  for (let x = cx*CHUNK; x < (cx+1)*CHUNK; x++) {
    if (x < 0 || x >= WORLD_W) continue;
    for (let z = cz*CHUNK; z < (cz+1)*CHUNK; z++) {
      if (z < 0 || z >= WORLD_D) continue;
      for (let y = 1; y < WORLD_H; y++) {
        const t = world[idx(x,y,z)];
        if (t === BLOCK.AIR || !isExposed(x,y,z)) continue;
        if (!byType.has(t)) byType.set(t, []);
        byType.get(t).push({ x, y, z, type: t });
      }
    }
  }
  const meshes = [];
  const dummy = new THREE.Object3D();
  for (const [type, list] of byType) {
    if (!BLOCK_MAT[type]) continue;
    const mesh = new THREE.InstancedMesh(BLOCK_GEO, BLOCK_MAT[type], list.length);
    for (let i = 0; i < list.length; i++) {
      const b = list[i];
      dummy.position.set(b.x+0.5, b.y+0.5, b.z+0.5);
      dummy.updateMatrix();
      mesh.setMatrixAt(i, dummy.matrix);
    }
    mesh.instanceMatrix.needsUpdate = true;
    mesh.userData.blocks = list;
    scene.add(mesh);
    meshes.push(mesh);
  }
  chunkMeshes.set(key, { meshes });
}

function generateAllChunks() {
  for (let cz = 0; cz < WORLD_D/CHUNK; cz++)
    for (let cx = 0; cx < WORLD_W/CHUNK; cx++)
      rebuildChunk(cx, cz);
}
function clearAllChunks() {
  for (const { meshes } of chunkMeshes.values())
    for (const m of meshes) { scene.remove(m); m.geometry.dispose(); }
  chunkMeshes.clear();
}
function findSurfaceY(x, z) {
  for (let y = WORLD_H-1; y >= 0; y--)
    if (world[idx(x,y,z)] !== BLOCK.AIR) return y + 1;
  return 16;
}
function isSolid(x, y, z) {
  if (y < 0) return true;
  if (y >= WORLD_H) return false;
  if (x<0||x>=WORLD_W||z<0||z>=WORLD_D) return true;
  return world[idx(x,y,z)] !== BLOCK.AIR;
}

let audioCtx = null;
function ensureAudio() {
  if (!audioCtx) {
    try { audioCtx = new (window.AudioContext || window.webkitAudioContext)(); } catch(e) {}
  }
  return audioCtx;
}
function playGunSound(k) {
  const ctx = ensureAudio(); if (!ctx) return;
  try {
    const t = ctx.currentTime;
    const size = ctx.sampleRate * 0.08;
    const buffer = ctx.createBuffer(1, size, ctx.sampleRate);
    const data = buffer.getChannelData(0);
    for (let i = 0; i < size; i++)
      data[i] = (Math.random()*2-1) * Math.pow(1-i/size, 2);
    const src = ctx.createBufferSource(); src.buffer = buffer;
    const g = ctx.createGain();
    g.gain.setValueAtTime(k === 'rocket' ? 0.5 : k === 'sniper' ? 0.4 : 0.3, t);
    g.gain.exponentialRampToValueAtTime(0.001, t+0.1);
    src.connect(g).connect(ctx.destination); src.start(t);
  } catch(e) {}
}
function playExplosionSound() {
  const ctx = ensureAudio(); if (!ctx) return;
  try {
    const t = ctx.currentTime;
    const size = ctx.sampleRate * 0.5;
    const buffer = ctx.createBuffer(1, size, ctx.sampleRate);
    const data = buffer.getChannelData(0);
    for (let i = 0; i < size; i++)
      data[i] = (Math.random()*2-1) * Math.pow(1-i/size, 1.5);
    const src = ctx.createBufferSource(); src.buffer = buffer;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.6, t);
    g.gain.exponentialRampToValueAtTime(0.001, t+0.5);
    src.connect(g).connect(ctx.destination); src.start(t);
  } catch(e) {}
}
function playHitSound() {
  const ctx = ensureAudio(); if (!ctx) return;
  try {
    const t = ctx.currentTime;
    const osc = ctx.createOscillator(); const g = ctx.createGain();
    osc.frequency.setValueAtTime(180, t);
    osc.frequency.exponentialRampToValueAtTime(60, t+0.08);
    g.gain.setValueAtTime(0.15, t);
    g.gain.exponentialRampToValueAtTime(0.001, t+0.1);
    osc.connect(g).connect(ctx.destination);
    osc.start(t); osc.stop(t+0.1);
  } catch(e) {}
}
function playPickupSound() {
  const ctx = ensureAudio(); if (!ctx) return;
  try {
    const t = ctx.currentTime;
    const osc = ctx.createOscillator(); const g = ctx.createGain();
    osc.type = 'triangle';
    osc.frequency.setValueAtTime(880, t);
    osc.frequency.linearRampToValueAtTime(1320, t+0.06);
    g.gain.setValueAtTime(0.12, t);
    g.gain.exponentialRampToValueAtTime(0.001, t+0.12);
    osc.connect(g).connect(ctx.destination);
    osc.start(t); osc.stop(t+0.12);
  } catch(e) {}
}
function playReloadSound() {
  const ctx = ensureAudio(); if (!ctx) return;
  try {
    const t = ctx.currentTime;
    const osc = ctx.createOscillator(); const g = ctx.createGain();
    osc.type = 'square';
    osc.frequency.setValueAtTime(220, t);
    osc.frequency.linearRampToValueAtTime(320, t+0.15);
    g.gain.setValueAtTime(0.1, t);
    g.gain.exponentialRampToValueAtTime(0.001, t+0.2);
    osc.connect(g).connect(ctx.destination);
    osc.start(t); osc.stop(t+0.2);
  } catch(e) {}
}

function initThree() {
  renderer = new THREE.WebGLRenderer({
    canvas: dom.canvas, antialias: false, powerPreference: 'high-performance',
  });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.setClearColor(0x2a3040);

  scene = new THREE.Scene();
  scene.fog = new THREE.Fog(0x2a3040, 20, 55);

  camera = new THREE.PerspectiveCamera(HIP_FOV, window.innerWidth/window.innerHeight, 0.1, 200);
  camera.rotation.order = 'YXZ';
  scene.add(camera);

  scene.add(new THREE.AmbientLight(0x8890aa, 0.6));
  const sun = new THREE.DirectionalLight(0xffcc99, 0.75);
  sun.position.set(-30, 50, 20); scene.add(sun);
  const rim = new THREE.DirectionalLight(0x8844aa, 0.35);
  rim.position.set(20, 30, -20); scene.add(rim);
  headLamp = new THREE.PointLight(0xffcc88, 1.0, 20, 1.6);
  scene.add(headLamp);

  buildMaterials();
  generateWorld();
  generateAllChunks();
  buildViewModel();

  const spawnY = findSurfaceY(64, 64);
  player.pos.set(64.5, spawnY, 64.5);
  syncCamera();
  window.addEventListener('resize', onResize);
}
function onResize() {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
}

let recoilAmount = 0;
let swayTime = 0;

function buildViewModel() {
  weaponRig = new THREE.Group();
  camera.add(weaponRig);

  handGroup = new THREE.Group();
  handGroup.position.set(0.32, -0.42, -0.40);
  handGroup.rotation.set(0.15, -0.15, 0);
  weaponRig.add(handGroup);

  const handTex = canvasToTexture(makeHandSkinTexture(64));
  const handMat = new THREE.MeshLambertMaterial({ map: handTex });
  handMesh = new THREE.Mesh(new THREE.BoxGeometry(0.14, 0.14, 0.55), handMat);
  handGroup.add(handMesh);

  gunGroup = new THREE.Group();
  gunGroup.position.set(HIP_POS.x, HIP_POS.y, HIP_POS.z);
  weaponRig.add(gunGroup);

  for (const key of weaponOrder) {
    const gun = buildGunMesh(key);
    gun.visible = false;
    gunGroup.add(gun);
  }

  muzzleFlash = new THREE.PointLight(0xffcc44, 0, 3, 2);
  gunGroup.add(muzzleFlash);
  switchWeaponModel('pistol');
}

function createFrontSight(mat) {
  const geo = new THREE.BoxGeometry(0.006, 0.018, 0.01);
  return new THREE.Mesh(geo, mat);
}

function createRearSight(mat) {
  const group = new THREE.Group();
  const w = 0.032; 
  const h = 0.02;
  const t = 0.014;
  const p = 0.005;

  const base = new THREE.Mesh(new THREE.BoxGeometry(w, p, t), mat);
  base.position.y = p / 2;
  group.add(base);

  const left = new THREE.Mesh(new THREE.BoxGeometry(p * 2, h - p, t), mat);
  left.position.set(-w/2 + p, h/2, 0);
  group.add(left);

  const right = new THREE.Mesh(new THREE.BoxGeometry(p * 2, h - p, t), mat);
  right.position.set(w/2 - p, h/2, 0);
  group.add(right);

  return group;
}

function buildGunMesh(weaponKey) {
  const skinTex = canvasToTexture(makeGunSkinTexture(weaponKey, 128));
  const mat = new THREE.MeshLambertMaterial({ map: skinTex });
  const darkMat = new THREE.MeshLambertMaterial({ color: 0x1a1a1a });
  const metalMat = new THREE.MeshLambertMaterial({ color: 0x555555 });

  const group = new THREE.Group();
  group.userData.weaponKey = weaponKey;

  if (weaponKey === 'pistol') {
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.10, 0.32), mat);
    const barrel = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.04, 0.16), darkMat);
    barrel.position.set(0, 0.02, -0.22);
    const grip = new THREE.Mesh(new THREE.BoxGeometry(0.07, 0.18, 0.08), darkMat);
    grip.position.set(0, -0.12, 0.06);
    grip.rotation.x = -0.25;
    
    const frontSight = createFrontSight(metalMat);
    frontSight.position.set(0, 0.06, -0.12);
    const rearSight = createRearSight(metalMat);
    rearSight.position.set(0, 0.055, 0.10);
    
    group.add(body, barrel, grip, frontSight, rearSight);
  } else if (weaponKey === 'smg') {
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.10, 0.12, 0.45), mat);
    const barrel = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.04, 0.20), darkMat);
    barrel.position.set(0, 0.02, -0.30);
    const mag = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.22, 0.08), darkMat);
    mag.position.set(0, -0.16, 0.05);
    const stock = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.08, 0.14), darkMat);
    stock.position.set(0, -0.02, 0.25);
    
    const frontSight = createFrontSight(metalMat);
    frontSight.position.set(0, 0.075, -0.20);
    const rearSight = createRearSight(metalMat);
    rearSight.position.set(0, 0.065, 0.12);
    
    group.add(body, barrel, mag, stock, frontSight, rearSight);
  } else if (weaponKey === 'rifle') {
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.10, 0.11, 0.62), mat);
    const barrel = new THREE.Mesh(new THREE.BoxGeometry(0.035, 0.035, 0.30), darkMat);
    barrel.position.set(0, 0.03, -0.42);
    const mag = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.24, 0.10), darkMat);
    mag.position.set(0, -0.16, 0.02);
    const stock = new THREE.Mesh(new THREE.BoxGeometry(0.07, 0.10, 0.20), darkMat);
    stock.position.set(0, -0.03, 0.35);
    
    // 移除瞄準鏡，改用機瞄
    const frontSight = createFrontSight(metalMat);
    frontSight.position.set(0, 0.075, -0.20);
    const rearSight = createRearSight(metalMat);
    rearSight.position.set(0, 0.065, 0.12);
    
    group.add(body, barrel, mag, stock, frontSight, rearSight);
  } else if (weaponKey === 'sniper') {
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.09, 0.10, 0.85), mat);
    const barrel = new THREE.Mesh(new THREE.BoxGeometry(0.03, 0.03, 0.45), darkMat);
    barrel.position.set(0, 0.03, -0.58);
    const mag = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.12, 0.08), darkMat);
    mag.position.set(0, -0.10, 0.05);
    const stock = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.12, 0.26), darkMat);
    stock.position.set(0, -0.04, 0.48);
    
    const scope = new THREE.Mesh(new THREE.CylinderGeometry(0.035, 0.035, 0.24, 8), darkMat);
    scope.rotation.x = Math.PI/2;
    scope.position.set(0, 0.12, -0.10);

    // 使用具備反光與透明感的玻璃材質
    const scopeGlass = new THREE.Mesh(new THREE.CircleGeometry(0.032, 16), 
      new THREE.MeshPhysicalMaterial({ 
        color: 0x88ccff, 
        transparent: true, 
        opacity: 0.6, 
        roughness: 0.1, 
        metalness: 0.9,
        clearcoat: 1.0
      })
    );
    scopeGlass.rotation.x = -Math.PI/2;
    scopeGlass.position.set(0, 0.138, -0.10);
    
    const frontSight = createFrontSight(metalMat);
    frontSight.position.set(0, 0.115, -0.20);
    const rearSight = createRearSight(metalMat);
    rearSight.position.set(0, 0.11, 0.00);
    
    group.add(body, barrel, mag, stock, scope, scopeGlass, frontSight, rearSight);
  } else if (weaponKey === 'rocket') {
    const tube = new THREE.Mesh(new THREE.CylinderGeometry(0.08, 0.08, 0.7, 8), mat);
    tube.rotation.x = Math.PI/2;
    tube.position.set(0, 0.02, -0.15);
    const frontCap = new THREE.Mesh(new THREE.CylinderGeometry(0.10, 0.10, 0.12, 8), darkMat);
    frontCap.rotation.x = Math.PI/2;
    frontCap.position.set(0, 0.02, -0.55);
    const backCap = new THREE.Mesh(new THREE.CylinderGeometry(0.09, 0.09, 0.08, 8), darkMat);
    backCap.rotation.x = Math.PI/2;
    backCap.position.set(0, 0.02, 0.22);
    const grip = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.16, 0.06), darkMat);
    grip.position.set(0, -0.12, -0.05);
    grip.rotation.x = -0.2;
    const trigger = new THREE.Mesh(new THREE.BoxGeometry(0.03, 0.05, 0.03), metalMat);
    trigger.position.set(0, -0.08, 0.02);
    
    const frontSight = createFrontSight(metalMat);
    frontSight.position.set(0, 0.105, -0.20);
    const rearSight = createRearSight(metalMat);
    rearSight.position.set(0, 0.095, 0.05);
    
    group.add(tube, frontCap, backCap, grip, trigger, frontSight, rearSight);
  }

  return group;
}

function switchWeaponModel(weaponKey) {
  if (!gunGroup) return;
  gunGroup.children.forEach(child => {
    if (child.userData.weaponKey) {
      child.visible = child.userData.weaponKey === weaponKey;
    }
  });
}

function updateViewModel(dt) {
  if (!weaponRig) return;
  swayTime += dt;
  const t = swayTime * 2;
  const swayZ = Math.sin(t * 1.3) * 0.006;
  const swayRotY = Math.sin(t * 0.7) * 0.01;

  if (gunGroup) {
    gunGroup.rotation.z = swayZ;
    gunGroup.rotation.y = swayRotY;
  }
  if (handGroup) {
    handGroup.rotation.z = swayZ;
    handGroup.rotation.y = swayRotY;
  }

  if (recoilAmount > 0) {
    recoilAmount = Math.max(0, recoilAmount - dt * 8);
    if (gunGroup && !isAiming) gunGroup.rotation.x = recoilAmount * 0.15;
  } else if (gunGroup) {
    gunGroup.rotation.x = 0;
  }

  if (muzzleFlash && muzzleFlash.intensity > 0) {
    muzzleFlash.intensity = Math.max(0, muzzleFlash.intensity - dt * 30);
  }
}

function updateAim(dt) {
  const w = currentWeapon ? WEAPONS[currentWeapon] : null;
  const targetFov = (isAiming && w) ? w.adsFov : HIP_FOV;
  currentFov += (targetFov - currentFov) * Math.min(dt * 12, 1);
  if (Math.abs(camera.fov - currentFov) > 0.01) {
    camera.fov = currentFov;
    camera.updateProjectionMatrix();
  }
  currentMouseSens = isAiming ? 0.0010 : 0.0022;
  if (!gunGroup || !handGroup) return;

  let targetX, targetY, targetZ;
  if (isAiming && w && !w.useScopeOverlay) {
    targetX = 0;
    targetY = -w.sightY;
    targetZ = ADS_Z;
    const handTargetX = 0.10;
    const handTargetY = -w.sightY - 0.16;
    handGroup.position.x += (handTargetX - handGroup.position.x) * Math.min(dt*12, 1);
    handGroup.position.y += (handTargetY - handGroup.position.y) * Math.min(dt*12, 1);
  } else {
    targetX = HIP_POS.x;
    targetY = HIP_POS.y;
    targetZ = HIP_POS.z;
    handGroup.position.x += (0.32 - handGroup.position.x) * Math.min(dt*12, 1);
    handGroup.position.y += (-0.42 - handGroup.position.y) * Math.min(dt*12, 1);
  }
  gunGroup.position.x += (targetX - gunGroup.position.x) * Math.min(dt*12, 1);
  gunGroup.position.y += (targetY - gunGroup.position.y) * Math.min(dt*12, 1);
  gunGroup.position.z += (targetZ - gunGroup.position.z) * Math.min(dt*12, 1);

  if (w && w.useScopeOverlay && isAiming) {
    dom.scopeOverlay.classList.remove('hidden');
    drawScope();
  } else {
    dom.scopeOverlay.classList.add('hidden');
  }
}

/* ---------------- 狙擊鏡密位繪製 ---------------- */
function drawScope() {
  const canvas = dom.scopeCanvas;
  const W = window.innerWidth, H = window.innerHeight;
  if (canvas.width !== W || canvas.height !== H) {
    canvas.width = W; canvas.height = H;
  }
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, W, H);

  const cx = W/2, cy = H/2;
  const radius = Math.min(W, H) * 0.38;

  // 遮罩
  ctx.fillStyle = 'rgba(0, 0, 0, 0.95)';
  ctx.fillRect(0, 0, W, H);
  ctx.globalCompositeOperation = 'destination-out';
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.fill();

  ctx.globalCompositeOperation = 'source-over';

  // 鏡片邊緣漸層
  const grad = ctx.createRadialGradient(cx, cy, radius*0.85, cx, cy, radius);
  grad.addColorStop(0, 'rgba(0,0,0,0)');
  grad.addColorStop(1, 'rgba(0,0,0,0.8)');
  ctx.fillStyle = grad;
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.fill();

  // 十字線
  ctx.strokeStyle = 'rgba(255,255,255,0.85)';
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(cx - radius, cy); ctx.lineTo(cx + radius, cy);
  ctx.moveTo(cx, cy - radius); ctx.lineTo(cx, cy + radius);
  ctx.stroke();

  // 密位刻度 (Mil-Dot)
  ctx.fillStyle = 'rgba(255,255,255,0.8)';
  for (let i = -5; i <= 5; i++) {
    if (i === 0) continue;
    const offX = (radius / 6) * i;
    const offY = (radius / 6) * i;

    // 垂直線上的點
    ctx.beginPath();
    ctx.arc(cx, cy + offY, 1.5, 0, Math.PI * 2);
    ctx.fill();
    // 垂直線上的刻度 (每2格長一點)
    if (i % 2 === 0) {
      ctx.beginPath();
      ctx.moveTo(cx - 4, cy + offY); ctx.lineTo(cx + 4, cy + offY);
      ctx.stroke();
    }

    // 水平線上的點
    ctx.beginPath();
    ctx.arc(cx + offX, cy, 1.5, 0, Math.PI * 2);
    ctx.fill();
    // 水平線上的刻度
    if (i % 2 === 0) {
      ctx.beginPath();
      ctx.moveTo(cx + offX, cy - 4); ctx.lineTo(cx + offX, cy + 4);
      ctx.stroke();
    }
  }

  // 中心紅點
  ctx.fillStyle = '#e74c3c';
  ctx.beginPath();
  ctx.arc(cx, cy, 2.5, 0, Math.PI * 2);
  ctx.fill();
}

function syncCamera() {
  camera.position.set(
    player.pos.x,
    player.pos.y + CFG.PLAYER_HEIGHT * 0.9,
    player.pos.z
  );
  camera.rotation.y = player.yaw;
  camera.rotation.x = player.pitch;
  if (headLamp) {
    headLamp.position.set(camera.position.x, camera.position.y, camera.position.z);
  }
}

function updatePlayer(dt) {
  player.vel.y += CFG.GRAVITY * dt;
  const sin = Math.sin(player.yaw), cos = Math.cos(player.yaw);
  let ix = 0, iz = 0;
  if (keys['KeyS']) iz -= 1;
  if (keys['KeyW']) iz += 1;
  if (keys['KeyA']) ix -= 1;
  if (keys['KeyD']) ix += 1;
  const len = Math.hypot(ix, iz) || 1;
  ix /= len; iz /= len;

  const speedMul = isAiming ? 0.5 : 1;
  const vx = (ix*cos - iz*sin) * CFG.MOVE_SPEED * speedMul;
  const vz = (ix*-sin - iz*cos) * CFG.MOVE_SPEED * speedMul;

  tryMove('x', vx * dt);
  tryMove('z', vz * dt);
  tryMove('y', player.vel.y * dt);

  player.pos.x = THREE.MathUtils.clamp(player.pos.x, 0.5, WORLD_W - 0.5);
  player.pos.z = THREE.MathUtils.clamp(player.pos.z, 0.5, WORLD_D - 0.5);

  if (keys['Space'] && player.onGround) {
    player.vel.y = CFG.JUMP_SPEED;
    player.onGround = false;
  }
  syncCamera();
}

function tryMove(axis, d) {
  if (!d) return;
  player.pos[axis] += d;
  const r = CFG.PLAYER_RADIUS, h = CFG.PLAYER_HEIGHT;
  const minX = Math.floor(player.pos.x - r), maxX = Math.floor(player.pos.x + r);
  const minY = Math.floor(player.pos.y), maxY = Math.floor(player.pos.y + h);
  const minZ = Math.floor(player.pos.z - r), maxZ = Math.floor(player.pos.z + r);
  for (let x = minX; x <= maxX; x++)
    for (let y = minY; y <= maxY; y++)
      for (let z = minZ; z <= maxZ; z++) {
        if (!isSolid(x, y, z)) continue;
        player.pos[axis] -= d;
        if (axis === 'y') {
          if (d < 0) player.onGround = true;
          player.vel.y = 0;
        }
        return;
      }
}

function onKeyDown(e) {
  keys[e.code] = true;
  if (e.code === 'Escape' && state === State.PLAYING) pauseGame();
  if (e.code === 'KeyE' && state === State.PLAYING) openInventory();
  if (e.code === 'KeyR' && state === State.PLAYING) startReload();
  const n = parseInt(e.key, 10);
  if (n >= 1 && n <= 9 && state === State.PLAYING) selectHotbarSlot(n - 1);
}
function onKeyUp(e) { keys[e.code] = false; }

function onPointerMove(e) {
  if (state !== State.PLAYING) return;
  if (!document.pointerLockElement) return;
  player.yaw -= e.movementX * currentMouseSens;
  player.pitch -= e.movementY * currentMouseSens;
  player.pitch = THREE.MathUtils.clamp(player.pitch, -Math.PI/2 + 0.01, Math.PI/2 - 0.01);
}

function onPointerLockChange() {
  const locked = document.pointerLockElement === dom.canvas;
  if (!locked && state === State.PLAYING) pauseGame();
}

function requestLock() {
  const p = dom.canvas.requestPointerLock?.();
  if (p && typeof p.catch === 'function') p.catch(() => {});
}

let mouseLeftDown = false;

function onMouseDown(e) {
  if (state !== State.PLAYING) return;
  if (!document.pointerLockElement) return;
  if (e.button === 0) {
    mouseLeftDown = true;
    onPrimaryAction();
  } else if (e.button === 2) {
    if (currentSlot < 5 && currentWeapon) isAiming = true;
    else if (currentSlot >= 5) onSecondaryAction();
  }
}
function onMouseUp(e) {
  if (e.button === 0) mouseLeftDown = false;
  if (e.button === 2) isAiming = false;
}
function onPrimaryAction() {
  if (currentSlot < 5) fireCurrentWeapon();
  else breakBlockAtCursor();
}
function onSecondaryAction() {
  if (currentSlot >= 5) placeBlockAtCursor();
}

function selectHotbarSlot(index) {
  if (index < 0 || index > 8) return;
  currentSlot = index;
  document.querySelectorAll('.hotbar-slot').forEach((el, i) => {
    el.classList.toggle('is-active', i === index);
  });
  if (index < 5) {
    currentWeapon = weaponOrder[index];
    switchWeaponModel(currentWeapon);
  } else {
    currentWeapon = null;
    switchWeaponModel(null);
    isAiming = false;
  }
  updateAmmoDisplay();
}

function onHotbarWheel(e) {
  if (state !== State.PLAYING) return;
  e.preventDefault();
  const dir = Math.sign(e.deltaY);
  selectHotbarSlot((currentSlot + dir + 9) % 9);
}

function updateAmmoDisplay() {
  if (!dom.ammoDisplay) return;
  if (currentWeapon) {
    const a = ammo[currentWeapon];
    if (a.reloading) dom.ammoDisplay.textContent = '換彈中…';
    else dom.ammoDisplay.textContent = `${a.mag} / ∞`;
  } else {
    dom.ammoDisplay.textContent = '';
  }
}

function startReload() {
  if (!currentWeapon) return;
  const a = ammo[currentWeapon];
  if (a.reloading) return;
  if (a.mag >= WEAPONS[currentWeapon].magSize) return;
  a.reloading = true;
  a.reloadEnd = performance.now() + WEAPONS[currentWeapon].reloadTime * 1000;
  playReloadSound();
  updateAmmoDisplay();
}
function checkReloadComplete() {
  if (!currentWeapon) return;
  const a = ammo[currentWeapon];
  if (a.reloading && performance.now() >= a.reloadEnd) {
    a.reloading = false;
    a.mag = WEAPONS[currentWeapon].magSize;
    updateAmmoDisplay();
  }
}

const raycaster = new THREE.Raycaster();
const CENTER = new THREE.Vector2(0, 0);
let lastShotTime = 0;

function fireCurrentWeapon() {
  if (!currentWeapon) return;
  const a = ammo[currentWeapon];
  const w = WEAPONS[currentWeapon];
  if (a.reloading) return;
  if (a.mag <= 0) { startReload(); return; }

  const now = performance.now();
  if (now - lastShotTime < w.fireRate) return;
  lastShotTime = now;

  a.mag--;
  updateAmmoDisplay();
  playGunSound(currentWeapon);

  recoilAmount = 1;
  player.pitch += 0.012 + w.spread * 0.3;
  player.pitch = THREE.MathUtils.clamp(player.pitch, -Math.PI/2 + 0.01, Math.PI/2 - 0.01);

  if (muzzleFlash) {
    muzzleFlash.position.set(0.25, -0.15, -0.7);
    muzzleFlash.intensity = 2.5;
  }

  raycaster.setFromCamera(CENTER, camera);
  raycaster.far = w.range;

  if (w.explosive) {
    launchRocket(w);
  } else {
    const targets = zombies.map(z => z.mesh);
    const hits = raycaster.intersectObjects(targets, true);
    if (hits.length > 0) {
      const hit = hits[0];
      let obj = hit.object;
      while (obj.parent && obj.parent !== scene) obj = obj.parent;
      const zi = zombies.findIndex(z => z.mesh === obj);
      if (zi !== -1) {
        const z = zombies[zi];
        let isHeadshot = false;
        if (hit.object.userData.isHead) isHeadshot = true;
        else {
          let p = hit.object;
          while (p) {
            if (p.userData && p.userData.isHead) { isHeadshot = true; break; }
            p = p.parent;
          }
        }
        let damage = w.damage;
        if (isHeadshot) damage *= (w.headshotMultiplier || 2.0);
        z.hp -= damage;
        flashZombie(z);
        spawnHitParticles(hit.point, isHeadshot);
        playHitSound();
        if (z.hp <= 0) killZombie(zi);
      }
    }
  }
  if (a.mag <= 0) startReload();
}

function launchRocket(w) {
  const origin = camera.position.clone();
  const dir = new THREE.Vector3(0, 0, -1).applyQuaternion(camera.quaternion).normalize();
  const geo = new THREE.SphereGeometry(0.12, 6, 6);
  const mat = new THREE.MeshLambertMaterial({ color: 0xff6600, emissive: 0xff3300 });
  const rocketMesh = new THREE.Mesh(geo, mat);
  rocketMesh.position.copy(origin);
  scene.add(rocketMesh);
  rockets.push({
    mesh: rocketMesh,
    vel: dir.clone().multiplyScalar(35),
    life: 2.5,
  });
}

const rockets = [];

function updateRockets(dt) {
  for (let i = rockets.length - 1; i >= 0; i--) {
    const r = rockets[i];
    r.life -= dt;
    r.mesh.position.addScaledVector(r.vel, dt);
    r.mesh.rotation.x += dt * 10;

    let hit = false;
    const pos = r.mesh.position;
    if (isSolid(Math.floor(pos.x), Math.floor(pos.y), Math.floor(pos.z))) hit = true;
    if (!hit) {
      for (const z of zombies) {
        if (z.mesh.position.distanceTo(pos) < 1.0) { hit = true; break; }
      }
    }

    if (hit || r.life <= 0) {
      explode(r.mesh.position.clone());
      scene.remove(r.mesh);
      r.mesh.geometry.dispose();
      r.mesh.material.dispose();
      rockets.splice(i, 1);
    }
  }
}

function explode(center) {
  playExplosionSound();
  const w = WEAPONS.rocket;
  const innerR = w.explosionInnerRadius;
  const outerR = w.explosionOuterRadius;

  for (let i = zombies.length - 1; i >= 0; i--) {
    const z = zombies[i];
    const dist = z.mesh.position.distanceTo(center);
    let dmg = 0;
    if (dist <= innerR) dmg = w.explosionInnerDamage;
    else if (dist <= outerR) dmg = w.explosionOuterMaxDamage * (outerR - dist) / (outerR - innerR);
    else continue;
    z.hp -= dmg;
    flashZombie(z);
    if (z.hp <= 0) killZombie(i);
  }

  for (let i = 0; i < 30; i++) {
    const geo = new THREE.BoxGeometry(0.1, 0.1, 0.1);
    const colors = [0xff4400, 0xffaa00, 0xffdd00, 0x888888];
    const mat = new THREE.MeshBasicMaterial({ color: colors[i % colors.length] });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.copy(center);
    scene.add(mesh);
    particles.push({
      mesh,
      vel: new THREE.Vector3(
        (Math.random() - 0.5) * 12,
        Math.random() * 10,
        (Math.random() - 0.5) * 12
      ),
      life: 0.8,
    });
  }

  const ringGeo = new THREE.RingGeometry(0.5, 0.6, 16);
  const ringMat = new THREE.MeshBasicMaterial({ color: 0xffaa00, transparent: true, opacity: 0.8, side: THREE.DoubleSide });
  const ring = new THREE.Mesh(ringGeo, ringMat);
  ring.position.copy(center);
  ring.rotation.x = -Math.PI/2;
  scene.add(ring);
  const startTime = performance.now();
  function animateRing() {
    const t = (performance.now() - startTime) / 500;
    if (t >= 1) { scene.remove(ring); ring.geometry.dispose(); ring.material.dispose(); return; }
    ring.scale.setScalar(1 + t * 10);
    ring.material.opacity = 0.8 * (1 - t);
    requestAnimationFrame(animateRing);
  }
  animateRing();
}

const highlightBox = new THREE.LineSegments(
  new THREE.EdgesGeometry(new THREE.BoxGeometry(1.02, 1.02, 1.02)),
  new THREE.LineBasicMaterial({ color: 0x000000 })
);
highlightBox.visible = false;
function initHighlight() {
  highlightBox.visible = false;
  scene.add(highlightBox);
}

function pickBlock() {
  raycaster.setFromCamera(CENTER, camera);
  raycaster.far = 6;
  const meshes = [];
  for (const { meshes: m } of chunkMeshes.values())
    for (const mesh of m) meshes.push(mesh);
  const hits = raycaster.intersectObjects(meshes, false);
  if (!hits.length) return null;
  const hit = hits[0];
  const blocks = hit.object.userData.blocks;
  if (!blocks || hit.instanceId == null) return null;
  return { block: blocks[hit.instanceId], normal: hit.face.normal.clone() };
}

function updateBlockHighlight() {
  if (state !== State.PLAYING || currentSlot < 5) {
    if (highlightBox) highlightBox.visible = false;
    return;
  }
  const p = pickBlock();
  if (p && p.block) {
    highlightBox.visible = true;
    highlightBox.position.set(p.block.x + 0.5, p.block.y + 0.5, p.block.z + 0.5);
  } else {
    highlightBox.visible = false;
  }
}

function breakBlockAtCursor() {
  const p = pickBlock();
  if (!p) return;
  const { x, y, z } = p.block;
  if (y <= 0) return;
  world[idx(x,y,z)] = BLOCK.AIR;
  rebuildChunk(Math.floor(x/CHUNK), Math.floor(z/CHUNK));
  if (x % CHUNK === 0) rebuildChunk(Math.floor(x/CHUNK)-1, Math.floor(z/CHUNK));
  if (x % CHUNK === CHUNK-1) rebuildChunk(Math.floor(x/CHUNK)+1, Math.floor(z/CHUNK));
  if (z % CHUNK === 0) rebuildChunk(Math.floor(x/CHUNK), Math.floor(z/CHUNK)-1);
  if (z % CHUNK === CHUNK-1) rebuildChunk(Math.floor(x/CHUNK), Math.floor(z/CHUNK)+1);
}

function placeBlockAtCursor() {
  const p = pickBlock();
  if (!p) return;
  const nx = p.block.x + p.normal.x;
  const ny = p.block.y + p.normal.y;
  const nz = p.block.z + p.normal.z;
  if (nx<0||nx>=WORLD_W||nz<0||nz>=WORLD_D) return;
  if (ny<0||ny>=WORLD_H) return;
  if (world[idx(nx,ny,nz)] !== BLOCK.AIR) return;
  if (isPlayerInside(nx,ny,nz)) return;
  const blockType = blockOrderMap[currentSlot];
  if (!blockType) return;
  world[idx(nx,ny,nz)] = blockType;
  rebuildChunk(Math.floor(nx/CHUNK), Math.floor(nz/CHUNK));
}

function isPlayerInside(bx, by, bz) {
  const r = CFG.PLAYER_RADIUS, h = CFG.PLAYER_HEIGHT;
  return (
    player.pos.x + r > bx && player.pos.x - r < bx + 1 &&
    player.pos.y + h > by && player.pos.y < by + 1 &&
    player.pos.z + r > bz && player.pos.z - r < bz + 1
  );
}

const zombies = [];
const particles = [];

const ZOMBIE_STATS = {
  white:{ hp:60, speed:1.4, damage:6 },
  blue:{ hp:100, speed:1.9, damage:9 },
  purple:{ hp:180, speed:2.4, damage:14 },
  red:{ hp:320, speed:3.0, damage:22 },
};
const ZOMBIE_PALETTES = {
  white:{ skin:0x6a8a5a, shirt:0x3a4a3a, pants:0x2a2a2a, eyes:0xffee55 },
  blue:{ skin:0x5a7aa8, shirt:0x2a3a5a, pants:0x1a1a2a, eyes:0x88ddff },
  purple:{ skin:0x8a5a9a, shirt:0x4a2a5a, pants:0x2a1a2a, eyes:0xff66dd },
  red:{ skin:0xa83a3a, shirt:0x5a1a1a, pants:0x2a0a0a, eyes:0xffff00 },
};
const CORE_COLORS = {
  white:0xe0e0e0, blue:0x4a90d9,
  purple:0x9b59b6, red:0xe74c3c,
};

function buildZombieMesh(quality) {
  const p = ZOMBIE_PALETTES[quality];
  const materials = [];
  const mk = (color) => {
    const m = new THREE.MeshLambertMaterial({ color });
    materials.push(m);
    return m;
  };
  const skinMat = mk(p.skin);
  const shirtMat = mk(p.shirt);
  const pantsMat = mk(p.pants);
  const eyeMat = new THREE.MeshBasicMaterial({ color: p.eyes });

  const g = new THREE.Group();
  const head = new THREE.Mesh(new THREE.BoxGeometry(0.5, 0.5, 0.5), skinMat);
  head.position.y = 1.6;
  head.userData.isHead = true;
  const eyeL = new THREE.Mesh(new THREE.BoxGeometry(0.1, 0.1, 0.05), eyeMat);
  eyeL.position.set(-0.12, 1.65, 0.26);
  eyeL.userData.isHead = true;
  const eyeR = new THREE.Mesh(new THREE.BoxGeometry(0.1, 0.1, 0.05), eyeMat);
  eyeR.position.set(0.12, 1.65, 0.26);
  eyeR.userData.isHead = true;
  const body = new THREE.Mesh(new THREE.BoxGeometry(0.6, 0.8, 0.3), shirtMat);
  body.position.y = 0.9;
  const armL = new THREE.Mesh(new THREE.BoxGeometry(0.2, 0.75, 0.2), skinMat);
  armL.position.set(-0.42, 1.05, 0.12);
  armL.rotation.x = -Math.PI/2.4;
  const armR = new THREE.Mesh(new THREE.BoxGeometry(0.2, 0.75, 0.2), skinMat);
  armR.position.set(0.42, 1.05, 0.12);
  armR.rotation.x = -Math.PI/2.4;
  const legL = new THREE.Mesh(new THREE.BoxGeometry(0.22, 0.8, 0.22), pantsMat);
  legL.position.set(-0.15, 0.4, 0);
  const legR = new THREE.Mesh(new THREE.BoxGeometry(0.22, 0.8, 0.22), pantsMat);
  legR.position.set(0.15, 0.4, 0);

  g.add(head, eyeL, eyeR, body, armL, armR, legL, legR);
  g.userData.materials = materials;
  g.userData.eyeMat = eyeMat;
  return g;
}

function spawnZombie() {
  if (zombies.length >= CFG.MAX_ZOMBIES || !scene) return;
  let spawnX, spawnZ, attempts = 0;
  do {
    const angle = Math.random() * Math.PI * 2;
    const dist = 15 + Math.random() * 15;
    spawnX = Math.round(player.pos.x + Math.cos(angle) * dist);
    spawnZ = Math.round(player.pos.z + Math.sin(angle) * dist);
    attempts++;
    if (attempts > 10) return;
  } while (spawnX < 2 || spawnX >= WORLD_W-2 || spawnZ < 2 || spawnZ >= WORLD_D-2);

  const spawnY = findSurfaceY(spawnX, spawnZ);
  if (spawnY <= 0 || spawnY >= WORLD_H - 2) return;
  if (!isSolid(spawnX, spawnY - 1, spawnZ)) return;
  if (spawnY > 25) return;

  const tier = Math.random();
  let quality = 'white';
  if (tier > 0.95) quality = 'red';
  else if (tier > 0.85) quality = 'purple';
  else if (tier > 0.65) quality = 'blue';

  const stats = ZOMBIE_STATS[quality];
  const group = buildZombieMesh(quality);
  group.position.set(spawnX + 0.5, spawnY, spawnZ + 0.5);
  scene.add(group);

  zombies.push({
    mesh: group, hp: stats.hp, maxHp: stats.hp, quality,
    speed: stats.speed, damage: stats.damage,
    lastAttack: 0, hitFlash: 0,
    baseMaterials: group.userData.materials,
  });
}

function flashZombie(z) {
  z.hitFlash = 0.12;
  for (const m of z.baseMaterials) m.emissive.setHex(0xffffff);
}

function updateZombies(dt) {
  const now = performance.now();
  for (let i = zombies.length - 1; i >= 0; i--) {
    const z = zombies[i];
    const pos = z.mesh.position;

    if (z.hitFlash > 0) {
      z.hitFlash -= dt;
      if (z.hitFlash <= 0)
        for (const m of z.baseMaterials) m.emissive.setHex(0x000000);
    }

    const dx = player.pos.x - pos.x;
    const dz = player.pos.z - pos.z;
    const dist = Math.hypot(dx, dz);

    if (dist > CFG.ZOMBIE_ATTACK_RANGE) {
      const stepX = (dx/dist) * z.speed * dt;
      const stepZ = (dz/dist) * z.speed * dt;
      const nextX = pos.x + stepX;
      const nextZ = pos.z + stepZ;

      const currentGroundY = findSurfaceY(Math.floor(pos.x), Math.floor(pos.z));
      const nextGroundY = findSurfaceY(Math.floor(nextX), Math.floor(nextZ));
      const heightDiff = nextGroundY - currentGroundY;

      if (heightDiff <= CFG.MAX_STEP_HEIGHT) {
        pos.x = nextX; pos.z = nextZ;
        pos.y += (nextGroundY - pos.y) * Math.min(dt*8, 1);
      } else {
        const nextGroundX = findSurfaceY(Math.floor(nextX), Math.floor(pos.z));
        const nextGroundZ = findSurfaceY(Math.floor(pos.x), Math.floor(nextZ));
        if (nextGroundX - currentGroundY <= CFG.MAX_STEP_HEIGHT) {
          pos.x = nextX;
          pos.y += (nextGroundX - pos.y) * Math.min(dt*8, 1);
        } else if (nextGroundZ - currentGroundY <= CFG.MAX_STEP_HEIGHT) {
          pos.z = nextZ;
          pos.y += (nextGroundZ - pos.y) * Math.min(dt*8, 1);
        }
      }
      z.mesh.rotation.y = Math.atan2(dx, dz);
    } else if (now - z.lastAttack > CFG.ZOMBIE_ATTACK_CD * 1000) {
      z.lastAttack = now;
      damagePlayer(z.damage);
    }
  }
}

function killZombie(index) {
  const z = zombies[index];
  dropCore(z.mesh.position.clone(), z.quality);
  scene.remove(z.mesh);
  z.mesh.traverse(o => { if (o.geometry) o.geometry.dispose(); });
  for (const m of z.baseMaterials) m.dispose();
  if (z.mesh.userData.eyeMat) z.mesh.userData.eyeMat.dispose();
  zombies.splice(index, 1);
}

const coreDrops = [];

function dropCore(position, quality) {
  const color = CORE_COLORS[quality];
  const geo = new THREE.OctahedronGeometry(0.22, 0);
  const mat = new THREE.MeshLambertMaterial({
    color, emissive: color, emissiveIntensity: 0.6,
    transparent: true, opacity: 0.95,
  });
  const mesh = new THREE.Mesh(geo, mat);

  const groundY = position.y;

  mesh.position.set(
    position.x + (Math.random() - 0.5) * 0.4,
    position.y + 0.4,
    position.z + (Math.random() - 0.5) * 0.4
  );
  scene.add(mesh);

  coreDrops.push({
    mesh, quality,
    groundY,
    vel: new THREE.Vector3(
      (Math.random() - 0.5) * 1.5,
      Math.random() * 2 + 1.5,
      (Math.random() - 0.5) * 1.5
    ),
    life: 30, pickedUp: false, pickupTimer: 0,
  });
}

function updateCoreDrops(dt) {
  for (let i = coreDrops.length - 1; i >= 0; i--) {
    const d = coreDrops[i];
    d.life -= dt;

    if (d.life <= 0 && !d.pickedUp) {
      scene.remove(d.mesh); d.mesh.geometry.dispose(); d.mesh.material.dispose();
      coreDrops.splice(i, 1); continue;
    }

    if (!d.pickedUp) {
      const dx = player.pos.x - d.mesh.position.x;
      const dz = player.pos.z - d.mesh.position.z;
      const dy = (player.pos.y + 0.9) - d.mesh.position.y;
      const dist = Math.sqrt(dx*dx + dy*dy + dz*dz);

      if (dist < CFG.CORE_PICKUP_RANGE) {
        d.pickedUp = true; d.pickupTimer = 0;
      } else {
        d.vel.y -= 20 * dt;
        d.mesh.position.addScaledVector(d.vel, dt);
        d.mesh.rotation.y += dt * 3;
        d.mesh.rotation.x += dt * 1.5;

        if (d.mesh.position.y < d.groundY + 0.3) {
          d.mesh.position.y = d.groundY + 0.3;
          d.vel.y *= -0.3;
          d.vel.x *= 0.7;
          d.vel.z *= 0.7;
        }
      }
    } else {
      d.pickupTimer += dt;
      const target = new THREE.Vector3(player.pos.x, player.pos.y + 0.9, player.pos.z);
      const k = Math.min(d.pickupTimer * 6, 1);
      d.mesh.position.lerp(target, k);
      d.mesh.scale.setScalar(1 - k * 0.8);
      if (k >= 1) {
        inventory[d.quality]++;
        updateHUD();
        playPickupSound();
        scene.remove(d.mesh); d.mesh.geometry.dispose(); d.mesh.material.dispose();
        coreDrops.splice(i, 1);
      }
    }
  }
}

function spawnHitParticles(point, isHeadshot) {
  const count = isHeadshot ? 12 : 6;
  const color = isHeadshot ? 0xffaa00 : 0xff4444;
  for (let i = 0; i < count; i++) {
    const geo = new THREE.BoxGeometry(0.08, 0.08, 0.08);
    const mat = new THREE.MeshBasicMaterial({ color });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.copy(point);
    scene.add(mesh);
    particles.push({
      mesh,
      vel: new THREE.Vector3(
        (Math.random() - 0.5) * 3,
        Math.random() * 3 + 1,
        (Math.random() - 0.5) * 3
      ),
      life: 0.4,
    });
  }
}

function updateParticles(dt) {
  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i];
    p.life -= dt;
    if (p.life <= 0) {
      scene.remove(p.mesh); p.mesh.geometry.dispose(); p.mesh.material.dispose();
      particles.splice(i, 1); continue;
    }
    p.vel.y -= 18 * dt;
    p.mesh.position.addScaledVector(p.vel, dt);
    p.mesh.rotation.x += dt * 6;
    p.mesh.rotation.z += dt * 6;
  }
}

function damagePlayer(amount) {
  if (state !== State.PLAYING) return;
  player.hp = Math.max(0, player.hp - amount);
  updateHUD();
  document.body.classList.add('hit-flash');
  setTimeout(() => document.body.classList.remove('hit-flash'), 150);
  if (player.hp <= 0) endGame(false);
}

let spawnAccum = 0;
function updateSpawner(dt) {
  spawnAccum += dt;
  if (spawnAccum >= CFG.SPAWN_INTERVAL && zombies.length < CFG.MAX_ZOMBIES) {
    spawnAccum = 0;
    spawnZombie();
  }
}

function startGame() {
  elapsedTime = 0; spawnAccum = 0;
  player.hp = CFG.PLAYER_MAX_HP;
  inventory.white = 0; inventory.blue = 0;
  inventory.purple = 0; inventory.red = 0; inventory.key = 0;

  ammo.pistol.mag = 12; ammo.pistol.reloading = false;
  ammo.smg.mag = 30;    ammo.smg.reloading = false;
  ammo.rifle.mag = 30;  ammo.rifle.reloading = false;
  ammo.sniper.mag = 5;  ammo.sniper.reloading = false;
  ammo.rocket.mag = 1;  ammo.rocket.reloading = false;

  isAiming = false;
  currentFov = HIP_FOV;
  camera.fov = HIP_FOV;
  camera.updateProjectionMatrix();
  dom.scopeOverlay.classList.add('hidden');

  if (gunGroup) gunGroup.position.set(HIP_POS.x, HIP_POS.y, HIP_POS.z);
  if (handGroup) handGroup.position.set(0.32, -0.42, -0.40);

  for (const z of zombies) {
    scene.remove(z.mesh);
    z.mesh.traverse(o => { if (o.geometry) o.geometry.dispose(); });
    for (const m of z.baseMaterials) m.dispose();
  }
  zombies.length = 0;

  for (const p of particles) {
    scene.remove(p.mesh); p.mesh.geometry.dispose(); p.mesh.material.dispose();
  }
  particles.length = 0;

  for (const r of rockets) {
    scene.remove(r.mesh); r.mesh.geometry.dispose(); r.mesh.material.dispose();
  }
  rockets.length = 0;

  for (const d of coreDrops) {
    scene.remove(d.mesh); d.mesh.geometry.dispose(); d.mesh.material.dispose();
  }
  coreDrops.length = 0;

  clearAllChunks();
  generateWorld();
  generateAllChunks();

  const spawnY = findSurfaceY(64, 64);
  player.pos.set(64.5, spawnY, 64.5);
  player.vel.set(0, 0, 0);
  player.yaw = 0; player.pitch = 0;
  player.onGround = false;
  syncCamera();

  for (const k in keys) delete keys[k];
  mouseLeftDown = false;

  selectHotbarSlot(0);
  hideAllOverlays();
  dom.hud.classList.remove('hidden');
  updateHUD();

  for (let i = 0; i < 4; i++) spawnZombie();

  state = State.PLAYING;
  requestLock();
}

function pauseGame() {
  if (state !== State.PLAYING) return;
  state = State.PAUSED;
  dom.overlayPause.classList.remove('hidden');
  dom.hud.classList.add('hidden');
  mouseLeftDown = false; isAiming = false;
  dom.scopeOverlay.classList.add('hidden');
  if (document.pointerLockElement) document.exitPointerLock();
}
function resumeGame() {
  if (state !== State.PAUSED) return;
  dom.overlayPause.classList.add('hidden');
  dom.hud.classList.remove('hidden');
  state = State.PLAYING;
  requestLock();
}
function endGame(win) {
  if (state === State.RESULT) return;
  state = State.RESULT;
  if (document.pointerLockElement) document.exitPointerLock();
  dom.hud.classList.add('hidden');
  dom.overlayInventory.classList.add('hidden');
  dom.scopeOverlay.classList.add('hidden');
  mouseLeftDown = false; isAiming = false;

  dom.resultTitle.textContent = win ? '時空穿越成功！' : '你已倒下…';
  dom.resultText.textContent = win
    ? `你在 ${elapsedTime.toFixed(1)} 秒內集齊晶核，開啟了扭曲之門。`
    : `你撐了 ${elapsedTime.toFixed(1)} 秒，最終倒在了廢土之中。`;

  const best = getBestTime();
  if (win) {
    if (best === 0 || elapsedTime < best) {
      setBestTime(elapsedTime);
      dom.resultBest.textContent = `新紀錄：${elapsedTime.toFixed(1)}s`;
    } else {
      dom.resultBest.textContent = `最佳紀錄：${best.toFixed(1)}s`;
    }
  } else {
    dom.resultBest.textContent = best ? `最佳紀錄：${best.toFixed(1)}s` : '';
  }
  dom.overlayResult.classList.remove('hidden');
}

function hideAllOverlays() {
  dom.overlayMenu.classList.add('hidden');
  dom.overlayPause.classList.add('hidden');
  dom.overlayResult.classList.add('hidden');
  dom.overlayInventory.classList.add('hidden');
}

const RECIPES = [
  { id:'white-to-blue', pattern:['white'], count:9, result:{ type:'blue', count:1 } },
  { id:'blue-to-purple', pattern:['blue'], count:9, result:{ type:'purple', count:1 } },
  { id:'purple-to-red', pattern:['purple'], count:9, result:{ type:'red', count:1 } },
  { id:'key', pattern:['purple','purple','purple','purple','purple','purple','purple','purple','red'], count:1, result:{ type:'key', count:1 } },
];
let craftGrid = new Array(9).fill(null);

function getInvCount(type) { return inventory[type] || 0; }
function setInvCount(type, count) {
  inventory[type] = Math.max(0, count);
  updateHUD();
}

function renderInventory() {
  const types = [
    { key:'white', name:'白色晶核' },
    { key:'blue', name:'藍色晶核' },
    { key:'purple', name:'紫色晶核' },
    { key:'red', name:'紅色晶核' },
    { key:'key', name:'扭曲之鑰' },
  ];
  dom.invGrid.innerHTML = types.map(t => {
    const count = getInvCount(t.key);
    return `
      <div class="inv-slot ${count === 0 ? 'empty' : ''}" data-type="${t.key}">
        <span class="inv-slot-icon core-${t.key}"></span>
        <span class="inv-slot-name">${t.name}</span>
        <span class="inv-slot-count">${count}</span>
      </div>`;
  }).join('');

  const cells = dom.craftGrid.querySelectorAll('.craft-cell');
  cells.forEach((cell, i) => {
    cell.innerHTML = '';
    cell.classList.remove('filled');
    const item = craftGrid[i];
    if (item && item.count > 0) {
      cell.innerHTML = `<span class="cell-icon core-${item.type}"></span>
                        <span class="cell-count">${item.count}</span>`;
      cell.classList.add('filled');
    }
  });
  updateCraftResult();
}

function updateCraftResult() {
  const resultCell = dom.craftResultCell;
  resultCell.innerHTML = '';
  resultCell.classList.remove('has-result');
  const recipe = findMatchingRecipe();
  if (!recipe) return;
  resultCell.innerHTML = `<span class="cell-icon core-${recipe.result.type}"></span>
                          <span class="cell-count">${recipe.result.count}</span>`;
  resultCell.classList.add('has-result');
}

function findMatchingRecipe() {
  const counts = {};
  let totalItems = 0;
  for (const item of craftGrid) {
    if (!item) continue;
    counts[item.type] = (counts[item.type] || 0) + item.count;
    totalItems += item.count;
  }
  for (const recipe of RECIPES) {
    if (recipe.pattern.length === 1) {
      const type = recipe.pattern[0];
      if (totalItems === recipe.count && counts[type] === recipe.count) {
        let otherMaterial = false;
        for (const [k, v] of Object.entries(counts)) {
          if (k !== type && v > 0) { otherMaterial = true; break; }
        }
        if (!otherMaterial) return recipe;
      }
    } else {
      const purpleCount = counts['purple'] || 0;
      const redCount = counts['red'] || 0;
      if (totalItems === 9 && purpleCount === 8 && redCount === 1) return recipe;
    }
  }
  return null;
}

function openInventory() {
  if (state !== State.PLAYING) return;
  state = State.INVENTORY;
  dom.overlayInventory.classList.remove('hidden');
  dom.hud.classList.add('hidden');
  mouseLeftDown = false; isAiming = false;
  dom.scopeOverlay.classList.add('hidden');
  if (document.pointerLockElement) document.exitPointerLock();
  craftGrid = new Array(9).fill(null);
  renderInventory();
}
function closeInventory() {
  if (state !== State.INVENTORY) return;
  for (const item of craftGrid) {
    if (item && item.count > 0) setInvCount(item.type, getInvCount(item.type) + item.count);
  }
  craftGrid = new Array(9).fill(null);
  dom.overlayInventory.classList.add('hidden');
  dom.hud.classList.remove('hidden');
  state = State.PLAYING;
  requestLock();
}

function bindInventoryEvents() {
  dom.invGrid.addEventListener('click', (e) => {
    const slot = e.target.closest('.inv-slot');
    if (!slot) return;
    const type = slot.dataset.type;
    if (getInvCount(type) <= 0) return;
    const emptyIndex = craftGrid.findIndex(c => c === null);
    if (emptyIndex === -1) return;
    setInvCount(type, getInvCount(type) - 1);
    craftGrid[emptyIndex] = { type, count: 1 };
    renderInventory();
  });
  dom.craftGrid.addEventListener('click', (e) => {
    const cell = e.target.closest('.craft-cell');
    if (!cell || !cell.dataset.cell || cell.dataset.cell === 'result') return;
    const i = parseInt(cell.dataset.cell);
    const item = craftGrid[i];
    if (!item) return;
    setInvCount(item.type, getInvCount(item.type) + item.count);
    craftGrid[i] = null;
    renderInventory();
  });
  dom.craftResultCell.addEventListener('click', () => {
    const recipe = findMatchingRecipe();
    if (!recipe) return;
    for (let i = 0; i < 9; i++) craftGrid[i] = null;
    setInvCount(recipe.result.type, getInvCount(recipe.result.type) + recipe.result.count);
    playPickupSound();
    renderInventory();
    if (recipe.result.type === 'key') {
      setTimeout(() => {
        if (state === State.INVENTORY) {
          dom.overlayInventory.classList.add('hidden');
          endGame(true);
        }
      }, 300);
    }
  });
  dom.btnCloseInventory.onclick = closeInventory;
}

let lastHudTick = -1;
function updateHUD() {
  const tick = Math.floor(elapsedTime * 10);
  if (tick !== lastHudTick) {
    dom.timerValue.textContent = elapsedTime.toFixed(1);
    lastHudTick = tick;
  }

  const totalHearts = 10;
  const hpPerHeart = CFG.PLAYER_MAX_HP / totalHearts;
  let heartHtml = '';
  for (let i = 0; i < totalHearts; i++) {
    const heartHp = player.hp - i * hpPerHeart;
    let cls = 'empty';
    if (heartHp >= hpPerHeart) cls = 'full';
    else if (heartHp > 0) cls = 'half';
    heartHtml += `<span class="heart ${cls}"></span>`;
  }
  dom.hearts.innerHTML = heartHtml;
  dom.hearts.classList.toggle('low-hp', player.hp <= 25 && player.hp > 0);

  dom.coreWhite.textContent = inventory.white;
  dom.coreBlue.textContent = inventory.blue;
  dom.corePurple.textContent = inventory.purple;
  dom.coreRed.textContent = inventory.red;
  dom.coreKey.textContent = inventory.key;
}

function getBestTime() {
  const raw = localStorage.getItem(STORAGE_KEY);
  const n = raw ? parseFloat(raw) : 0;
  return Number.isFinite(n) ? n : 0;
}
function setBestTime(t) { localStorage.setItem(STORAGE_KEY, String(t)); }

function loop(now) {
  rafId = requestAnimationFrame(loop);
  const dt = Math.min((now - lastTime) / 1000, 0.1);
  lastTime = now;
  if (state === State.PLAYING) {
    elapsedTime += dt;
    updatePlayer(dt);
    updateAim(dt);
    updateZombies(dt);
    updateSpawner(dt);
    updateParticles(dt);
    updateCoreDrops(dt);
    updateRockets(dt);
    updateViewModel(dt);
    updateBlockHighlight();
    checkReloadComplete();
    if (mouseLeftDown && currentWeapon && WEAPONS[currentWeapon].fireRate < 200) {
      fireCurrentWeapon();
    }
    updateHUD();
  } else {
    updateParticles(dt);
  }
  renderer.render(scene, camera);
}

function bindEvents() {
  window.addEventListener('keydown', onKeyDown);
  window.addEventListener('keyup', onKeyUp);
  document.addEventListener('mousemove', onPointerMove);
  document.addEventListener('pointerlockchange', onPointerLockChange);
  window.addEventListener('mousedown', onMouseDown);
  window.addEventListener('mouseup', onMouseUp);
  window.addEventListener('contextmenu', (e) => e.preventDefault());
  window.addEventListener('wheel', onHotbarWheel, { passive: false });

  dom.btnStart.onclick = () => { hideAllOverlays(); startGame(); };
  dom.btnResume.onclick = resumeGame;
  dom.btnRestart.onclick = () => {
    dom.overlayResult.classList.add('hidden');
    startGame();
  };
}

function init() {
  generateItemIcons(); // 生成新的物品欄像素與3D圖示
  initThree();
  initHighlight();
  bindEvents();
  bindInventoryEvents();
  state = State.MENU;
  lastTime = performance.now();
  rafId = requestAnimationFrame(loop);
}
init();