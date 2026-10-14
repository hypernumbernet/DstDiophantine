(function(){
  var root=document.documentElement,btn=document.getElementById('lang');
  function set(l){root.setAttribute('data-lang',l);root.lang=l;try{localStorage.setItem('dst-lang',l)}catch(e){}
    btn.setAttribute('aria-pressed',l==='ja');}
  set(root.getAttribute('data-lang')||'en');
  btn.addEventListener('click',function(){set(root.getAttribute('data-lang')==='ja'?'en':'ja');});
})();
