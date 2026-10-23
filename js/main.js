/* ===========================================================
   末日晶核 — 首頁邏輯
   =========================================================== */
(function () {
  'use strict';

  function clamp255(v) {
    return v < 0 ? 0 : v > 255 ? 255 : v | 0;
  }

  function makeTile(base, variance, size) {
    size = size || 16;
    var canvas = document.createElement('canvas');
    canvas.width = canvas.height = size;
    var ctx = canvas.getContext('2d');
    var img = ctx.createImageData(size, size);
    for (var i = 0; i < size * size; i++) {
      var n = (Math.random() - 0.5) * variance * 2;
      img.data[i * 4 + 0] = clamp255(base[0] + n);
      img.data[i * 4 + 1] = clamp255(base[1] + n);
      img.data[i * 4 + 2] = clamp255(base[2] + n);
      img.data[i * 4 + 3] = 255;
    }
    ctx.putImageData(img, 0, 0);
    return canvas;
  }

  function makeGrassSide(size) {
    size = size || 16;
    var out = document.createElement('canvas');
    out.width = out.height = size;
    var ctx = out.getContext('2d');
    var grass = makeTile([80, 130, 50], 18, size);
    var dirt = makeTile([100, 75, 55], 18, size);
    ctx.drawImage(dirt, 0, 0);
    for (var x = 0; x < size; x++) {
      var h = 3 + (Math.random() < 0.45 ? 1 : 0);
      ctx.drawImage(grass, x, 0, 1, h, x, 0, 1, h);
    }
    return out;
  }

  function toCSSUrl(canvas) {
    return 'url(' + canvas.toDataURL() + ')';
  }

  function injectTextures() {
    var root = document.documentElement.style;
    root.setProperty('--tex-grass', toCSSUrl(makeTile([80, 130, 50], 18)));
    root.setProperty('--tex-grass-side', toCSSUrl(makeGrassSide(16)));
    root.setProperty('--tex-dirt', toCSSUrl(makeTile([100, 75, 55], 18)));
    root.setProperty('--tex-stone', toCSSUrl(makeTile([110, 110, 110], 14)));
    root.setProperty('--tex-diamond', toCSSUrl(makeTile([92, 219, 213], 26)));
  }

  function init() {
    injectTextures();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();