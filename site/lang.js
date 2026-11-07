(function () {
  var root = document.documentElement;
  var btn = document.getElementById('lang');

  function apply(l) {
    root.setAttribute('data-lang', l);
    root.lang = l;
    btn.setAttribute('aria-pressed', l === 'ja');
  }

  function setManual(l) {
    apply(l);
    try {
      localStorage.setItem('dst-lang-manual', l);
    } catch (e) { }
  }

  apply(root.getAttribute('data-lang') || 'en');
  btn.addEventListener('click', function () {
    setManual(root.getAttribute('data-lang') === 'ja' ? 'en' : 'ja');
  });
})();
