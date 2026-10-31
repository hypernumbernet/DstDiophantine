#!/usr/bin/env python3
"""One-off splitter: index.monolith.html -> multi-page site. Run from site/."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "index.monolith.html"

HEAD_PREFIX = ""
FOOTER_INNER = ""
MAIN_INNER = ""
hero = ""
sections: dict[str, str] = {}

# Composite pages (section id -> filename)
PAGE_SECTIONS = [
    ("overview.html", ["two"]),
    ("gravity.html", ["gravity"]),
    ("admissible.html", ["ceiling"]),
    ("layers.html", ["electron"]),
    ("antiparticle.html", ["antiparticle"]),
    # transport.html, control.html, physics.html (redirect): maintained manually, not from monolith
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
for sub in ("strong", "rutherford", "neutron", "shells", "coldfusion", "two-lengths"):
    ANCHOR_TO_PAGE[sub] = "layers.html"
for sub in ("shield-ceiling", "holding-shield", "hold-price", "circular-hold", "one-scale", "field-control", "mismatch-split"):
    ANCHOR_TO_PAGE[sub] = "control.html"
ANCHOR_TO_PAGE["physics"] = "transport.html"
ANCHOR_TO_PAGE["transport"] = "transport.html"
ANCHOR_TO_PAGE["control"] = "control.html"

PAGE_ORDER = (
    ["index.html"]
    + [p[0] for p in PAGE_SECTIONS[:5]]
    + ["transport.html", "control.html"]
    + [p[0] for p in PAGE_SECTIONS[5:]]
)

PAGE_TITLES = {
    "index.html": ("Contents · Double Spacetime Theory", "目次 · 二重時空理論"),
    "overview.html": ("Two spacetimes · DST", "二つの時空 · DST"),
    "gravity.html": ("Gravity · DST", "重力 · DST"),
    "admissible.html": ("Admissible cone & superposition · DST", "許容錐と重ね合わせ · DST"),
    "layers.html": ("Layers & nuclear physics · DST", "層と原子核 · DST"),
    "antiparticle.html": ("Antiparticles · DST", "反粒子 · DST"),
    "transport.html": ("Parallel transport · DST", "平行移動 · DST"),
    "control.html": ("Gravity control · DST", "重力制御 · DST"),
    "physics.html": ("Redirect · DST", "リダイレクト · DST"),
    "rotation.html": ("Rotation hypothesis · DST", "回転の仮説 · DST"),
    "numbers.html": ("Number theory · DST", "数論 · DST"),
    "logic.html": ("Four-valued logic · DST", "4値論理 · DST"),
    "lean.html": ("Lean verification · DST", "Lean 検証 · DST"),
}

TOC = [
    (1, "overview.html", "two", "Two spacetimes inside one algebra", "一つの代数の中の二つの時空",
     "Biquaternions, dual map, rotors.", "双四元数、双対写像、ローター。"),
    (2, "gravity.html", "gravity", "Gravity as a mismatch", "重力は「ずれ」",
     "Ω, Schwarzschild match, weak fields & galaxies.", "Ω、シュヴァルツシルト一致、弱い場と銀河。"),
    (3, "admissible.html", "ceiling", "A ceiling on the twist", "ねじれには上限がある",
     "Admissible cone, internal sum vs expressed state.", "許容錐、内部の和と表出。"),
    (4, "layers.html", "electron", "A sign-changing force", "符号が入れ替わる力",
     "One γ_s, two lengths; strong force, shells, scattering.", "一つの γ_s、二つの長さ；強い力、電子殻、散乱。"),
    (5, "antiparticle.html", "antiparticle", "Antiparticles from the dual map", "双対写像から見える反粒子",
     "Dual map + charge conjugation; quantum superposition.", "双対写像と荷電共役、量子の重ね合わせ。"),
    (6, "transport.html", "transport", "The geometry of parallel transport", "平行移動の幾何学",
     "Motors, Killing axis, light that returns.", "モーター、キリング軸、戻る光。"),
    (7, "control.html", "control", "Gravity control", "重力制御",
     "Shields, fields, left/right split of J, circular drive, one scale.", "シールド、場、J の左右分解、円偏光駆動、ひとつの物差し。"),
    (8, "rotation.html", "rotation", "A hypothesis: why do things rotate?", "仮説：なぜ回転が生まれるのか",
     "Hypothesis: offset spacetimes.", "仮説：ずれた二つの空間。"),
    (9, "numbers.html", "numbers", "Number theory: equations as geometry", "数論：方程式を幾何に変える",
     "Goldbach, Polignac, Collatz, bridges.", "ゴールドバッハ、ポリニャック、コラッツ。"),
    (10, "logic.html", "logic", "Four-valued logic (D4L)", "4値論理（D4L）",
     "J_norm readout, walls, no explosion.", "J_norm、壁、矛盾の非爆発。"),
    (11, "lean.html", "lean", "Checked by a machine", "機械による検証",
     "Proof assistant, residuals, further reading.", "証明支援、残差、さらに読む。"),
]

CHAPTER_BY_PAGE = {href: (num, en, ja) for num, href, _aid, en, ja, *_ in TOC}


def toc_link_spans(num: int, en: str, ja: str) -> str:
    return (
        f'<span class="en"><span class="ch-num">{num}.</span> {en}</span>'
        f'<span class="ja"><span class="ch-num">{num}.</span> {ja}</span>'
    )


def chapter_nav_spans(num: int, en: str, ja: str, *, prev: bool) -> str:
    if prev:
        return (
            f'<span class="en">← <span class="ch-num">{num}.</span> {en}</span>'
            f'<span class="ja">← <span class="ch-num">{num}.</span> {ja}</span>'
        )
    return (
        f'<span class="en"><span class="ch-num">{num}.</span> {en} →</span>'
        f'<span class="ja"><span class="ch-num">{num}.</span> {ja} →</span>'
    )

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
    rutherford:'layers.html',neutron:'layers.html',shells:'layers.html',coldfusion:'layers.html','two-lengths':'layers.html',
    antiparticle:'antiparticle.html',physics:'transport.html',transport:'transport.html',control:'control.html',
    'shield-ceiling':'control.html','holding-shield':'control.html','hold-price':'control.html',
    'circular-hold':'control.html','one-scale':'control.html','field-control':'control.html','mismatch-split':'control.html',
    rotation:'rotation.html',numbers:'numbers.html',logic:'logic.html',
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
        if prev_l == "index.html":
            parts.append(
                f'<a class="prev" href="{prev_l}"><span class="en">← Previous</span><span class="ja">← 前へ</span></a>'
            )
        else:
            num, en, ja = CHAPTER_BY_PAGE[prev_l]
            parts.append(
                f'<a class="prev" href="{prev_l}">{chapter_nav_spans(num, en, ja, prev=True)}</a>'
            )
    parts.append('<a class="contents" href="index.html"><span class="en">Contents</span><span class="ja">目次</span></a>')
    if nxt_l:
        num, en, ja = CHAPTER_BY_PAGE[nxt_l]
        parts.append(
            f'<a class="next" href="{nxt_l}">{chapter_nav_spans(num, en, ja, prev=False)}</a>'
        )
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
for num, href, aid, en, ja, desc_en, desc_ja in TOC:
    toc_items.append(
        f'    <li><a href="{href}#{aid}">{toc_link_spans(num, en, ja)}</a>'
        f'<p class="toc-desc"><span class="en">{desc_en}</span><span class="ja">{desc_ja}</span></p></li>'
    )


def load_monolith() -> None:
    global HEAD_PREFIX, FOOTER_INNER, MAIN_INNER, hero, sections
    text = SRC.read_text(encoding="utf-8")
    head_match = re.search(r"(?s)^(.+?)<body>\s*", text)
    footer_m = re.search(r"(<footer>.*?</footer>)", text, re.S)
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


def build_from_monolith() -> None:
    load_monolith()
    landing = f"""
{hero}
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


def sync_nav_in_html() -> None:
    """Refresh pager blocks (and index TOC) in existing HTML without the monolith."""
    pager_re = re.compile(
        r'<nav class="pager" aria-label="Page navigation / ページ移動">.*?</nav>',
        re.S,
    )
    for fname in PAGE_ORDER:
        path = ROOT / fname
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        text = pager_re.sub(pager(fname), text)
        path.write_text(text, encoding="utf-8")
    idx = ROOT / "index.html"
    if idx.is_file():
        text = idx.read_text(encoding="utf-8")
        toc_block = f"""<section class="toc-section" id="contents">
  <h2><span class="en">Table of contents</span><span class="ja">目次</span></h2>
  <ol class="toc-list">
{chr(10).join(toc_items)}
  </ol>
</section>"""
        text = re.sub(
            r'<section class="toc-section" id="contents">.*?</section>',
            toc_block,
            text,
            count=1,
            flags=re.S,
        )
        idx.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--sync-nav":
        sync_nav_in_html()
        print("Synced pager + index TOC in HTML")
    else:
        build_from_monolith()
