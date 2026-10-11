// Persist the TOC collapsed/expanded state across page navigation using localStorage.
//
// The IIFE runs immediately (before body paint) to set data-toc="collapsed" on <html>
// so the CSS suppresses the TOC without a visible flash.  The DOMContentLoaded handler
// then syncs the hidden checkbox and wires up the change listener.

(function () {
    var KEY = 'stil-toc-collapsed';
    if (localStorage.getItem(KEY) === 'true') {
        document.documentElement.setAttribute('data-toc', 'collapsed');
    }
})();

// Theme: set data-theme on <html> before first paint to avoid a flash of the
// wrong theme. Precedence: explicit saved choice → system preference → dark.
// "Default dark" means dark unless the OS explicitly asks for light.
(function () {
    var KEY = 'stil-theme';
    var saved = localStorage.getItem(KEY);
    var theme;
    if (saved === 'dark' || saved === 'light') {
        theme = saved;
    } else if (window.matchMedia &&
               window.matchMedia('(prefers-color-scheme: light)').matches) {
        theme = 'light';
    } else {
        theme = 'dark';
    }
    document.documentElement.setAttribute('data-theme', theme);
})();

// Remove the uninformative "Definition of example" native tooltip that Verso
// generates for every definition link inside a code block.  The Verso JS hover
// popup already shows the docstring, so the browser title attribute is redundant.
document.addEventListener('DOMContentLoaded', function () {
    document.querySelectorAll('a[title="Definition of example"]').forEach(function (a) {
        a.removeAttribute('title');
    });
});

// Theme toggle button + dark/light figure swapping. The pre-paint IIFE above
// has already set data-theme; here we add the floating button, align the figure
// images with the current theme, and let the reader flip it (persisted), while
// still following system changes until they make an explicit choice.
document.addEventListener('DOMContentLoaded', function () {
    var KEY = 'stil-theme';
    var root = document.documentElement;

    // Figures ship in two variants: figures/NAME.svg (light) and
    // figures/dark/NAME.svg (dark). Rewrite <img> src to match the theme.
    function swapFigures(theme) {
        document.querySelectorAll('img').forEach(function (img) {
            var src = img.getAttribute('src') || '';
            if (src.indexOf('figures/') === -1 || !/\.svg(\?|$)/.test(src)) return;
            if (theme === 'dark') {
                if (src.indexOf('figures/dark/') === -1) {
                    img.setAttribute('src', src.replace('figures/', 'figures/dark/'));
                }
            } else {
                img.setAttribute('src', src.replace('figures/dark/', 'figures/'));
            }
        });
    }

    function curTheme() {
        return root.getAttribute('data-theme') === 'light' ? 'light' : 'dark';
    }

    var btn = document.createElement('button');
    btn.className = 'theme-toggle';
    btn.type = 'button';

    function updateButton(theme) {
        var dark = theme === 'dark';
        btn.textContent = dark ? '☀' : '☾';   // ☀ when dark, ☽ when light
        var label = dark ? 'Switch to light theme' : 'Switch to dark theme';
        btn.setAttribute('aria-label', label);
        btn.title = label;
        btn.setAttribute('aria-pressed', String(dark));
    }

    function setTheme(theme, persist) {
        root.setAttribute('data-theme', theme);
        if (persist) localStorage.setItem(KEY, theme);
        swapFigures(theme);
        updateButton(theme);
    }

    document.body.appendChild(btn);
    setTheme(curTheme(), false);   // align figures + button with pre-paint theme

    btn.addEventListener('click', function () {
        setTheme(curTheme() === 'dark' ? 'light' : 'dark', true);
    });

    // Follow OS changes only while the reader hasn't chosen explicitly.
    if (window.matchMedia) {
        window.matchMedia('(prefers-color-scheme: light)').addEventListener('change', function (e) {
            if (localStorage.getItem(KEY)) return;
            setTheme(e.matches ? 'light' : 'dark', false);
        });
    }
});

// Keyboard shortcut: Alt+S toggles every <details class="solutions-spoiler"> on
// the page. If any are closed, the first press opens them all; otherwise it
// closes them all. Skips key events whose target is an editable element so it
// doesn't fire while typing in the search box.
document.addEventListener('keydown', function (e) {
    if (!e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) return;
    if (e.key !== 's' && e.key !== 'S') return;
    var t = e.target;
    if (t && (t.isContentEditable ||
              t.tagName === 'INPUT' ||
              t.tagName === 'TEXTAREA' ||
              t.tagName === 'SELECT')) return;
    var spoilers = document.querySelectorAll('details.solutions-spoiler');
    if (spoilers.length === 0) return;
    var anyClosed = false;
    spoilers.forEach(function (d) { if (!d.open) anyClosed = true; });
    spoilers.forEach(function (d) { d.open = anyClosed; });
    e.preventDefault();
});

document.addEventListener('DOMContentLoaded', function () {
    var KEY = 'stil-toc-collapsed';
    var checkbox = document.getElementById('toggle-toc');
    if (!checkbox) return;

    // Sync checkbox with stored state
    if (localStorage.getItem(KEY) === 'true') {
        checkbox.checked = true;
    }

    checkbox.addEventListener('change', function () {
        if (this.checked) {
            localStorage.setItem(KEY, 'true');
            document.documentElement.setAttribute('data-toc', 'collapsed');
        } else {
            localStorage.removeItem(KEY);
            document.documentElement.removeAttribute('data-toc');
        }
    });

    // In single-page mode, the sidebar TOC only shows chapter titles. Augment it
    // by injecting each chapter's subsections (h2 with id="section-*") under the
    // chapter row, and use an IntersectionObserver to mark the chapter that is
    // currently in view so its subsections expand (CSS controls the visibility).
    var sidebarChapterLinks = document.querySelectorAll('#toc .split-toc.book a[href^="#chapter-"]');
    if (sidebarChapterLinks.length > 0) {
        // Chapter and section IDs live on heading elements (chapters on h2, sections on h3).
        // Build map from chapter id → array of {id, title} for its sections, by walking the
        // headings in document order: each section heading belongs to the most recent chapter.
        var allHeadings = document.querySelectorAll(
            'main h2[id^="chapter-"], main h3[id^="section-"]'
        );
        // Extract a heading's text without the trailing permalink-widget anchor
        // and without the leading section-number prefix (e.g. "1.1. ").
        // Verso uses U+00A0 (NBSP) between number and title, which \s matches in JS.
        function headingText(h) {
            var clone = h.cloneNode(true);
            clone.querySelectorAll('.permalink-widget').forEach(function (n) {
                n.remove();
            });
            return clone.textContent
                .replace(/\s+/g, ' ')
                .replace(/^\s*\d+(\.\d+)*\.?\s*/, '')
                .trim();
        }
        var sectionsByChapter = {};
        var chapterHeadings = [];
        var currentChId = null;
        allHeadings.forEach(function (h) {
            if (h.tagName === 'H2' && h.id.indexOf('chapter-') === 0) {
                currentChId = h.id;
                sectionsByChapter[currentChId] = [];
                chapterHeadings.push(h);
            } else if (currentChId) {
                sectionsByChapter[currentChId].push({
                    id: h.id,
                    title: headingText(h)
                });
            }
        });

        // Inject a nested subsection table inside each chapter's <tr> (the second <td>).
        sidebarChapterLinks.forEach(function (a) {
            var chId = a.getAttribute('href').replace(/^#/, '');
            var secs = sectionsByChapter[chId];
            if (!secs || secs.length === 0) return;
            var tr = a.closest('tr');
            if (!tr) return;
            var td = tr.querySelector('td:last-child');
            if (!td) return;
            var sub = document.createElement('table');
            sub.className = 'sidebar-subsections';
            secs.forEach(function (s) {
                var subTr = document.createElement('tr');
                var numTd = document.createElement('td');
                numTd.className = 'num';
                var linkTd = document.createElement('td');
                var link = document.createElement('a');
                link.href = '#' + s.id;
                link.textContent = s.title;
                linkTd.appendChild(link);
                subTr.appendChild(numTd);
                subTr.appendChild(linkTd);
                sub.appendChild(subTr);
            });
            td.appendChild(sub);
            tr.dataset.chapterId = chId;
        });

        // Mark the chapter whose heading is currently most visible. Use a simple
        // scroll listener (cheap enough — fires only on scroll) that picks the
        // last chapter whose top is above a threshold near the viewport top.
        var chapterSections = chapterHeadings;
        var rowByChapter = {};
        document.querySelectorAll('#toc .split-toc.book tr[data-chapter-id]').forEach(function (tr) {
            rowByChapter[tr.dataset.chapterId] = tr;
        });

        function updateCurrentChapter() {
            var threshold = 120; // pixels from top of viewport
            var current = null;
            for (var i = 0; i < chapterSections.length; i++) {
                var rect = chapterSections[i].getBoundingClientRect();
                if (rect.top <= threshold) current = chapterSections[i].id;
                else break;
            }
            if (!current && chapterSections.length > 0) current = chapterSections[0].id;
            Object.keys(rowByChapter).forEach(function (id) {
                rowByChapter[id].classList.toggle('current-chapter', id === current);
            });
        }

        updateCurrentChapter();
        var scrollTick = false;
        window.addEventListener('scroll', function () {
            if (scrollTick) return;
            scrollTick = true;
            window.requestAnimationFrame(function () {
                updateCurrentChapter();
                scrollTick = false;
            });
        }, { passive: true });
    }

    // In per-chapter mode (html-chapter), the current-chapter sidebar lists the
    // chapter's sections, each carrying a nested (hidden) subsection table that
    // postprocess_chapter_toc.py injected. Reveal only the subsections of the
    // section currently in view, marking its row `current-section` (CSS handles
    // visibility) — mirroring the chapter logic above and html-multi.
    var chapterSectionRows = document.querySelectorAll(
        '#toc .split-toc:not(.book) tr[data-section-id]'
    );
    if (chapterSectionRows.length > 0) {
        var rowBySection = {};
        var sectionHeadings = [];
        chapterSectionRows.forEach(function (tr) {
            var id = tr.dataset.sectionId;
            var heading = document.getElementById(id);
            if (heading) {
                rowBySection[id] = tr;
                sectionHeadings.push(heading);
            }
        });
        // Keep headings in document order so the "last one above the line" scan works.
        sectionHeadings.sort(function (a, b) {
            return (a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING)
                ? -1 : 1;
        });

        function updateCurrentSection() {
            var threshold = 120; // pixels from top of viewport
            var current = null;
            for (var i = 0; i < sectionHeadings.length; i++) {
                if (sectionHeadings[i].getBoundingClientRect().top <= threshold)
                    current = sectionHeadings[i].id;
                else break;
            }
            // When the page is scrolled to the bottom, the final sections —
            // typically short ones with no subsections — can never bring their
            // heading up to the threshold (there isn't enough content below to
            // scroll further), so the scan above stops at the previous section
            // and clicking the TOC link leaves it highlighted. If we're at the
            // bottom and the URL hash points at one of these still-below-the-line
            // sections that is visible, honour that explicit selection instead.
            var atBottom = window.innerHeight + window.scrollY
                >= document.documentElement.scrollHeight - 2;
            if (atBottom) {
                var hashId = decodeURIComponent((location.hash || '').slice(1));
                var hashHeading = hashId && rowBySection[hashId]
                    ? document.getElementById(hashId) : null;
                if (hashHeading) {
                    var top = hashHeading.getBoundingClientRect().top;
                    if (top > threshold && top < window.innerHeight)
                        current = hashId;
                }
            }
            if (!current && sectionHeadings.length > 0)
                current = sectionHeadings[0].id;
            Object.keys(rowBySection).forEach(function (id) {
                rowBySection[id].classList.toggle('current-section', id === current);
            });
        }

        updateCurrentSection();
        var sectionTick = false;
        window.addEventListener('scroll', function () {
            if (sectionTick) return;
            sectionTick = true;
            window.requestAnimationFrame(function () {
                updateCurrentSection();
                sectionTick = false;
            });
        }, { passive: true });
        // A click on a TOC link to a bottom section may not fire a scroll event
        // (the page is already as far down as it goes), so recompute on hashchange.
        window.addEventListener('hashchange', updateCurrentSection);
    }

    // Fix broken links in the main page TOC (section-toc) for single-page mode.
    // In single-page mode, some TOC links are generated with an empty href
    // instead of fragments like #chapter-introduction.
    var sectionTocLinks = document.querySelectorAll('ol.section-toc a[href=""]');
    if (sectionTocLinks.length > 0) {
        // Use the sidebar TOC as a mapping from text to correct fragment URLs.
        var sidebarMapping = {};
        document.querySelectorAll('#toc .split-toc a[href^="#"]').forEach(function(a) {
            sidebarMapping[a.textContent.trim()] = a.getAttribute('href');
        });

        sectionTocLinks.forEach(function(a) {
            // Remove the section number (e.g., "1. ") to match the sidebar text.
            var cleanText = a.textContent.replace(/^\d+(\.\d+)*\.?\s*/, '').trim();
            if (sidebarMapping[cleanText]) {
                a.setAttribute('href', sidebarMapping[cleanText]);
            }
        });
    }
});

// Group the chapter lists into Parts. The book itself stays structurally flat;
// these are purely presentational divider rows injected before the first
// chapter of each part, in (a) the sidebar book ToC shown on every page and
// (b) the book-level table of contents on the landing page. The parts come
// from guide.json's "parts" list, which the generated GuideMain.lean emits as
// `window.STIL_PARTS` ([{anchor: 'chapter-…', label: '…'}, …]; a null label
// renders as a spacing-only separator). No list, no dividers. Registered after
// the handler above so it runs after the single-page href fixup for
// ol.section-toc links.
document.addEventListener('DOMContentLoaded', function () {
    var PARTS = window.STIL_PARTS || [];
    if (!PARTS.length) return;

    // Sidebar book ToC: one <tr> per chapter; insert a label row above the
    // part's first chapter. The direct-child `> table` keeps this away from
    // the injected nested .sidebar-subsections tables.
    document.querySelectorAll('#toc .split-toc.book > table').forEach(function (table) {
        PARTS.forEach(function (p) {
            var a = table.querySelector('a[href$="#' + p.anchor + '"]');
            var tr = a && a.closest('tr');
            if (!tr || !tr.parentNode) return;
            var row = document.createElement('tr');
            row.className = p.label ? 'part-label' : 'part-sep';
            var td = document.createElement('td');
            td.colSpan = 2;
            if (p.label) td.textContent = p.label;
            row.appendChild(td);
            tr.parentNode.insertBefore(row, tr);
        });
    });

    // Landing page / single-page book ToC: top-level <li> per chapter.
    // Chapter landing pages also carry an ol.section-toc, but theirs links to
    // #section-* anchors only, so the #chapter-* match never fires there.
    document.querySelectorAll('ol.section-toc').forEach(function (ol) {
        PARTS.forEach(function (p) {
            var a = ol.querySelector(':scope > li > a[href$="#' + p.anchor + '"]');
            var li = a && a.closest('li');
            if (!li) return;
            var label = document.createElement('li');
            label.className = p.label ? 'part-label' : 'part-sep';
            if (p.label) label.textContent = p.label;
            ol.insertBefore(label, li);
        });
    });
});
