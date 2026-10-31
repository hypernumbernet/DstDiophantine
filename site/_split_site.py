#!/usr/bin/env python3
"""One-off splitter: index.monolith.html -> multi-page site. Run from site/."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "index.monolith.html"
text = SRC.read_text(encoding="utf-8")

head_match = re.search(r"(?s)^(.+?)<body>\s*", text)
footer_m = re.search(
    r"(<footer>.*?</footer>)", text, re.S
)
if not footer_m:
    raise SystemExit("footer parse failed")
FOOTER_INNER = footer_m.group(1)

main_match = re.search(r"(?s)<main id=\"top\">(.*?)</main>", text)
if not (head_match and main_match):
    raise SystemExit("parse failed")
HEAD_PREFIX = head_match.group(1)
MAIN_INNER = main_match.group(1)

hero_m = re.search(r"(?s)(<section class=\"hero\">.*?</section>\s*)", MAIN_INNER)
hero = hero_m.group(1) if hero_m else ""

sections = {}
for m in re.finditer(r'(?s)(<section id="([^"]+)">.*?</section>)', MAIN_INNER):
    sections[m.group(2)] = m.group(1)

# Composite pages (section id -> filename)
PAGE_SECTIONS = [
    ("overview.html", ["two"]),
    ("gravity.html", ["gravity"]),
    ("admissible.html", ["ceiling"]),
    ("layers.html", ["electron"]),
    ("antiparticle.html", ["antiparticle"]),
    ("physics.html", ["physics"]),
    ("rotation.html", ["rotation"]),
    ("numbers.html", ["numbers"]),
    ("logic.html", ["logic"]),
    ("lean.html", ["lean", "read"]),
]

ANCHOR_TO_PAGE = {}
for fname, ids in PAGE_SECTIONS:
    for sid in ids:
        ANCHOR_TO_PAGE[sid] = fname
# sub-anchors inside gravity
for sub in ("lean-coords", "weak-field"):
    ANCHOR_TO_PAGE[sub] = "gravity.html"
for sub in ("superposition",):
    ANCHOR_TO_PAGE[sub] = "admissible.html"
for sub in ("strong", "rutherford", "neutron", "shells", "coldfusion"):
    ANCHOR_TO_PAGE[sub] = "layers.html"
for sub in ("shield-ceiling", "holding-shield", "hold-price", "circular-hold", "field-control"):
    ANCHOR_TO_PAGE[sub] = "physics.html"

PAGE_ORDER = ["index.html"] + [p[0] for p in PAGE_SECTIONS]

PAGE_TITLES = {
    "index.html": ("Contents · Double Spacetime Theory", "目次 · 二重時空理論"),
    "overview.html": ("Two spacetimes · DST", "二つの時空 · DST"),
    "gravity.html": ("Gravity · DST", "重力 · DST"),
    "admissible.html": ("Admissible cone & superposition · DST", "許容錐と重ね合わせ · DST"),
    "layers.html": ("Layers & nuclear physics · DST", "層と原子核 · DST"),
    "antiparticle.html": ("Antiparticles · DST", "反粒子 · DST"),
    "physics.html": ("Shields & field control · DST", "シールドと場 · DST"),
    "rotation.html": ("Rotation hypothesis · DST", "回転の仮説 · DST"),
    "numbers.html": ("Number theory · DST", "数論 · DST"),
    "logic.html": ("Four-valued logic · DST", "4値論理 · DST"),
    "lean.html": ("Lean verification · DST", "Lean 検証 · DST"),
}

TOC = [
    ("overview.html", "two", "Two spacetimes inside one algebra", "一つの代数の中の二つの時空",
     "Biquaternions, dual map, rotors.", "双四元数、双対写像、ローター。"),
    ("gravity.html", "gravity", "Gravity as a mismatch", "重力は「ずれ」",
     "Ω, Schwarzschild match, weak fields & galaxies.", "Ω、シュヴァルツシルト一致、弱い場と銀河。"),
    ("admissible.html", "ceiling", "Ceiling & superposition", "上限と重ね合わせ",
     "Admissible cone, internal sum vs expressed state.", "許容錐、内部の和と表出。"),
    ("layers.html", "electron", "Sign-changing layers", "符号が入れ替わる層",
     "Strong force, shells, scattering, cold fusion.", "強い力、電子殻、散乱、常温核融合。"),
    ("antiparticle.html", "antiparticle", "Antiparticles", "反粒子",
     "Dual map + charge conjugation; quantum superposition.", "双対写像と荷電共役、量子の重ね合わせ。"),
    ("physics.html", "physics", "Gravity, shields & control", "重力・シールド・制御",
     "Killing axis, shields, hold price, circular hold, EM.", "キリング軸、保持、円偏光駆動、電磁気。"),
    ("rotation.html", "rotation", "Why things rotate", "なぜ回転するか",
     "Hypothesis: offset spacetimes.", "仮説：ずれた二つの空間。"),
    ("numbers.html", "numbers", "Diophantine geometry", "ディオファントス幾何",
     "Goldbach, Polignac, Collatz, bridges.", "ゴールドバッハ、ポリニャック、コラッツ。"),
    ("logic.html", "logic", "Four-valued logic (D4L)", "4値論理（D4L）",
     "J_norm readout, walls, no explosion.", "J_norm、壁、矛盾の非爆発。"),
    ("lean.html", "lean", "Machine-checked Lean", "Lean による検証",
     "Proof assistant, residuals, further reading.", "証明支援、残差、さらに読む。"),
]

OPEN_DISCLAIMER = """
<aside class="open-disclaimer" aria-labelledby="open-disclaimer-heading">
  <h2 id="open-disclaimer-heading" class="sub"><span class="en">Open conjectures</span><span class="ja">未解決の予想</span></h2>
  <p class="note"><span class="en">Classical Fermat, Beal, abc, the Riemann hypothesis, Goldbach, Polignac, and Collatz remain open in the usual mathematical sense. The DST programme encodes some of them in Lean, but this site does not claim proofs of those classical statements. Model theorems and bridge steps are clearly labelled in the papers and in section 10.</span><span class="ja">古典的なフェルマー、ビール、abc、リーマン予想、ゴールドバッハ、ポリニャック、コラッツは、通常の数学的意味で未解決のままです。DST プログラムはそれらの一部を Lean に符号化しますが、このサイトはそれらの古典的命題の証明を主張しません。モデル内の定理と橋渡しの段階は、論文および第10節で明示されています。</span></p>
</aside>
"""

HASH_REDIRECT = """
<script>
(function(){
  var map={
    top:'index.html',two:'overview.html',gravity:'gravity.html','lean-coords':'gravity.html','weak-field':'gravity.html',
    ceiling:'admissible.html',superposition:'admissible.html',electron:'layers.html',strong:'layers.html',
    rutherford:'layers.html',neutron:'layers.html',shells:'layers.html',coldfusion:'layers.html',
    antiparticle:'antiparticle.html',physics:'physics.html','shield-ceiling':'physics.html',
    'holding-shield':'physics.html','hold-price':'physics.html','circular-hold':'physics.html',
    'field-control':'physics.html',rotation:'rotation.html',numbers:'numbers.html',logic:'logic.html',
    lean:'lean.html',read:'lean.html#read'
  };
  var h=(location.hash||'').replace(/^#/,'');
  if(!h||h==='top')return;
  var t=map[h];
  if(t){location.replace(t.indexOf('#')>=0?t:t+'#'+h);}
})();
</script>
"""


def fix_links(html: str, current_file: str) -> str:
    def repl_href(m):
        anchor = m.group(1)
        if not anchor or anchor == "top":
            target = "index.html"
            frag = "" if anchor in ("", "top") else "#top"
            return f'href="{target}{frag}"'
        page = ANCHOR_TO_PAGE.get(anchor)
        if page:
            if page == current_file:
                return f'href="#{anchor}"'
            return f'href="{page}#{anchor}"'
        return m.group(0)

    html = re.sub(r'href="#([^"]*)"', repl_href, html)
    return html


def make_head(title_en: str, title_ja: str) -> str:
    t = f"{title_en} · {title_ja}"
    h = HEAD_PREFIX
    h = re.sub(r"<title>.*?</title>", f"<title>{t}</title>", h, count=1)
    return h


def header_nav(current_file: str) -> str:
    contents_active = ' aria-current="page"' if current_file == "index.html" else ""
    return f"""<header class="top">
  <a class="brand" href="index.html">DST</a>
  <nav class="site-nav">
    <a href="index.html"{contents_active}><span class="en">Contents</span><span class="ja">目次</span></a>
    <a href="overview.html#two"><span class="en">Overview</span><span class="ja">概観</span></a>
    <a href="gravity.html#gravity"><span class="en">Gravity</span><span class="ja">重力</span></a>
    <a href="admissible.html#ceiling"><span class="en">Cone</span><span class="ja">錐</span></a>
    <a href="layers.html#electron"><span class="en">Layers</span><span class="ja">層</span></a>
    <a href="numbers.html#numbers"><span class="en">Numbers</span><span class="ja">数論</span></a>
    <a href="lean.html#lean"><span class="en">Lean</span><span class="ja">Lean</span></a>
  </nav>
  <button id="lang" class="toggle" type="button" aria-label="Switch language / 言語切替">
    <span class="opt" data-v="en">EN</span><span class="opt" data-v="ja">日本語</span>
  </button>
</header>
"""


def pager(current_file: str) -> str:
    try:
        i = PAGE_ORDER.index(current_file)
    except ValueError:
        return ""
    prev_l = PAGE_ORDER[i - 1] if i > 0 else None
    nxt_l = PAGE_ORDER[i + 1] if i + 1 < len(PAGE_ORDER) else None
    parts = ['<nav class="pager" aria-label="Page navigation / ページ移動">']
    if prev_l:
        parts.append(f'<a class="prev" href="{prev_l}"><span class="en">← Previous</span><span class="ja">← 前へ</span></a>')
    parts.append('<a class="contents" href="index.html"><span class="en">Contents</span><span class="ja">目次</span></a>')
    if nxt_l:
        parts.append(f'<a class="next" href="{nxt_l}"><span class="en">Next →</span><span class="ja">次へ →</span></a>')
    parts.append("</nav>")
    return "\n".join(parts)


def wrap_page(fname: str, body_main: str, extra_scripts: str = "") -> str:
    te, tj = PAGE_TITLES[fname]
    body_main = fix_links(body_main, fname)
    pg = pager(fname)
    return (
        make_head(te, tj)
        + "<body>\n"
        + header_nav(fname)
        + pg
        + f'<main id="top">\n{body_main}\n</main>\n'
        + pg
        + FOOTER_INNER
        + "\n"
        + extra_scripts
        + '<script src="lang.js"></script>\n</body>\n</html>\n'
    )


# Landing
toc_items = []
for href, aid, en, ja, desc_en, desc_ja in TOC:
    toc_items.append(
        f'    <li><a href="{href}#{aid}"><span class="en">{en}</span><span class="ja">{ja}</span></a>'
        f'<p class="toc-desc"><span class="en">{desc_en}</span><span class="ja">{desc_ja}</span></p></li>'
    )
landing = f"""
{hero}
{OPEN_DISCLAIMER}
<section class="toc-section" id="contents">
  <h2><span class="en">Table of contents</span><span class="ja">目次</span></h2>
  <ol class="toc-list">
{chr(10).join(toc_items)}
  </ol>
</section>
"""
index_html = wrap_page("index.html", landing, HASH_REDIRECT + "\n")
(ROOT / "index.html").write_text(index_html, encoding="utf-8")

for fname, ids in PAGE_SECTIONS:
    chunks = []
    for sid in ids:
        if sid not in sections:
            raise SystemExit(f"missing section {sid}")
        chunks.append(sections[sid])
    extra = ""
    if fname == "numbers.html":
        extra = OPEN_DISCLAIMER + "\n"
    body = extra + "\n".join(chunks)
    (ROOT / fname).write_text(wrap_page(fname, body), encoding="utf-8")

print("Wrote", len(PAGE_ORDER), "pages")
