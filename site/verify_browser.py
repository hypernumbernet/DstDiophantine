#!/usr/bin/env python3
"""Headless smoke test: pages load, lang persists, mobile viewport."""
import asyncio
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PAGES = [
    "index.html",
    "overview.html",
    "gravity.html",
    "admissible.html",
    "layers.html",
    "antiparticle.html",
    "physics.html",
    "rotation.html",
    "numbers.html",
    "logic.html",
    "lean.html",
]


async def main():
    from playwright.async_api import async_playwright

    errors = []
    async with async_playwright() as p:
        browser = await p.chromium.launch()
        for vp_name, vp in [("desktop", {"width": 1280, "height": 800}), ("mobile", {"width": 390, "height": 844})]:
            ctx = await browser.new_context(viewport=vp)
            page = await ctx.new_page()
            for name in PAGES:
                url = (ROOT / name).as_uri()
                try:
                    resp = await page.goto(url, wait_until="networkidle", timeout=60000)
                    if not resp or resp.status >= 400:
                        errors.append(f"{vp_name} {name}: HTTP {getattr(resp,'status',None)}")
                    await page.wait_for_selector("main", timeout=10000)
                    # SVG present
                    svg_count = await page.locator("svg.fig").count()
                    if name != "index.html" and svg_count == 0:
                        errors.append(f"{vp_name} {name}: no svg.fig")
                except Exception as e:
                    errors.append(f"{vp_name} {name}: load failed {e}")
            await ctx.close()

        # Language toggle persistence
        ctx = await browser.new_context(viewport={"width": 1280, "height": 800})
        page = await ctx.new_page()
        await page.goto((ROOT / "index.html").as_uri(), wait_until="networkidle")
        await page.evaluate("() => { localStorage.setItem('dst-lang','en'); document.documentElement.setAttribute('data-lang','en'); }")
        await page.reload(wait_until="networkidle")
        await page.click("#lang")
        await page.wait_for_function("() => document.documentElement.getAttribute('data-lang') === 'ja'", timeout=10000)
        ja = await page.evaluate("() => localStorage.getItem('dst-lang')")
        if ja != "ja":
            errors.append(f"lang toggle: expected ja in localStorage, got {ja!r}")
        await page.goto((ROOT / "gravity.html").as_uri(), wait_until="networkidle")
        lang = await page.evaluate("() => document.documentElement.getAttribute('data-lang')")
        if lang != "ja":
            errors.append(f"lang persist: gravity.html expected ja, got {lang}")
        await ctx.close()
        await browser.close()

    if errors:
        for e in errors:
            print("ERROR:", e)
        sys.exit(1)
    print("OK: playwright smoke tests passed for", len(PAGES), "pages")

if __name__ == "__main__":
    asyncio.run(main())
