(function () {
  var prods = JSON.parse(document.getElementById('datos').textContent);
  var porId = {}; prods.forEach(function (p) { porId[p.id] = p; });
  var carro = {}; // id -> cantidad
  var $ = function (id) { return document.getElementById(id); };
  var cop = function (n) { return '$' + Math.round(n || 0).toString().replace(/\B(?=(\d{3})+(?!\d))/g, '.'); };
  var num = function (s) { return parseInt(String(s || '').replace(/[^\d]/g, ''), 10) || 0; };
  var esc = function (s) { var d = document.createElement('div'); d.textContent = s; return d.innerHTML; };

  function pintarLista() {
    var t = $('buscar').value.trim().toLowerCase(), n = 0, h = '';
    prods.forEach(function (p) {
      if (n >= 60) return;
      if (t && p.nombre.toLowerCase().indexOf(t) < 0 && (p.sku || '').toLowerCase().indexOf(t) < 0) return;
      n++;
      var agotado = p.controla_stock && p.stock <= 0;
      h += '<button class="prod' + (agotado ? ' agotado' : '') + '" data-id="' + p.id + '"' + (agotado ? ' disabled' : '') + '><b>' + esc(p.nombre) + '</b><span>' + cop(p.precio) +
        '</span><small>' + (p.controla_stock ? (agotado ? 'Agotado' : p.stock + ' disp.') : '') + '</small></button>';
    });
    $('lista').innerHTML = h || '<p class="muted">Sin resultados.</p>';
  }

  function agregar(id) {
    var p = porId[id]; if (!p) return;
    var ya = carro[id] || 0;
    if (p.controla_stock && ya + 1 > p.stock) { mostrarError('Solo quedan ' + p.stock + ' de «' + p.nombre + '».'); return; }
    mostrarError(''); carro[id] = ya + 1; pintarCarro();
  }

  function subtotal() { var s = 0; Object.keys(carro).forEach(function (id) { s += porId[id].precio * carro[id]; }); return s; }

  function pintarCarro() {
    var ids = Object.keys(carro), h = '';
    ids.forEach(function (id) {
      var p = porId[id];
      h += '<div class="linea"><div class="ln-n">' + esc(p.nombre) + '<small>' + cop(p.precio) + '</small></div>' +
        '<div class="ln-c"><button data-menos="' + id + '">−</button><b>' + carro[id] + '</b><button data-mas="' + id + '">+</button></div>' +
        '<div class="ln-t">' + cop(p.precio * carro[id]) + '</div></div>';
    });
    $('carro').innerHTML = h || '<p class="muted">Toca un producto para agregarlo.</p>';
    totales();
  }

  function totales() {
    var s = subtotal(), d = Math.min(num($('descuento').value), s), t = s - d;
    $('subtotal').textContent = cop(s); $('total').textContent = cop(t);
    var ef = $('metodo').value === 'efectivo';
    $('caja-efectivo').style.display = ef ? '' : 'none';
    var rec = num($('recibido').value);
    $('cambio').textContent = cop(ef && rec >= t ? rec - t : 0);
    $('cobrar').disabled = !Object.keys(carro).length || (ef && $('recibido').value !== '' && rec < t);
  }

  function mostrarError(m) { var e = $('error'); e.textContent = m; e.hidden = !m; }

  $('lista').addEventListener('click', function (e) { var b = e.target.closest('.prod'); if (b) agregar(b.dataset.id); });
  $('carro').addEventListener('click', function (e) {
    var m = e.target.dataset.menos, a = e.target.dataset.mas;
    if (m) { carro[m]--; if (carro[m] <= 0) delete carro[m]; pintarCarro(); }
    if (a) agregar(a);
  });
  $('buscar').addEventListener('input', pintarLista);
  $('buscar').addEventListener('keydown', function (e) {
    if (e.key !== 'Enter') return;
    var t = this.value.trim().toLowerCase(); if (!t) return;
    var exacto = prods.filter(function (p) { return (p.sku || '').toLowerCase() === t; })[0];
    var unico = prods.filter(function (p) { return p.nombre.toLowerCase().indexOf(t) >= 0; });
    var p = exacto || (unico.length === 1 ? unico[0] : null);
    if (p) { agregar(p.id); this.value = ''; pintarLista(); }
    e.preventDefault();
  });
  ['descuento', 'recibido', 'metodo'].forEach(function (id) { $(id).addEventListener('input', totales); $(id).addEventListener('change', totales); });
  $('vaciar').addEventListener('click', function () { carro = {}; $('descuento').value = ''; $('recibido').value = ''; mostrarError(''); pintarCarro(); });

  $('cobrar').addEventListener('click', function () {
    var btn = this; btn.disabled = true; mostrarError('');
    var items = Object.keys(carro).map(function (id) { return { id: +id, cant: carro[id] }; });
    fetch(window.TT_COBRAR, {
      method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF': window.TT_CSRF },
      body: JSON.stringify({ items: items, descuento: num($('descuento').value), metodo: $('metodo').value, recibido: num($('recibido').value), cliente_id: $('cliente').value })
    }).then(function (r) { return r.json().then(function (j) { return { ok: r.ok, j: j }; }); })
      .then(function (r) {
        if (r.ok && r.j.ok) { window.location = window.TT_RECIBO + r.j.id + '/recibo?nuevo=1'; }
        else { mostrarError(r.j.error || 'No se pudo cobrar.'); btn.disabled = false; }
      }).catch(function () { mostrarError('Sin conexión. Intenta de nuevo.'); btn.disabled = false; });
  });

  pintarLista(); pintarCarro();
})();
