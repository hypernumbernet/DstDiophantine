(function () {
  function primaryTag() {
    try {
      var list = navigator.languages;
      if (list && list.length) {
        var first = list[0];
        if (typeof first === 'string' && first) return first;
      }
      if (navigator.language) return navigator.language;
    } catch (e) { }
    return '';
  }

  function fromBrowser() {
    var tag = primaryTag();
    if (!tag) return 'en';
    var base = tag.toLowerCase().split('-')[0];
    return base === 'ja' ? 'ja' : 'en';
  }

  function resolve() {
    try {
      var manual = localStorage.getItem('dst-lang-manual');
      if (manual === 'ja' || manual === 'en') return manual;
    } catch (e) { }
    return fromBrowser();
  }

  var lang = resolve();
  document.documentElement.setAttribute('data-lang', lang);
  document.documentElement.lang = lang;
})();
