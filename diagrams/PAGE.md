# The page behind the cards

In the light theme, the page of every gov-tla diagram is `#ececec` (92.6% white), not white. This document says
why, how the number was measured, and how to measure it again. The method is riemann-diagrams'
(`diagrams/PAGE.md` there, which chose `#eeeeee` for its posters). The measurement here was made on 2026.11.25 with
[`measure-page.py`](measure-page.py), riemann-diagrams' `tools/measure-page.py` extended to pool several diagrams. If the diagrams change
enough to move the measurement, the `page` token in [`gov-tla/src/lib.py`](gov-tla/src/lib.py) and this document
change together.

## Why not white

A diagram is cards on a page. On a white page, a card's white interior and the page are the same colour, and only
the card's border shows where it ends. The rule riemann-diagrams adopted, and this family follows, is that the page
should match the average luminance of what sits on it. Then the page is neither lighter nor darker than the diagram
as a whole, and the cards stand off it by their borders and tints at the smallest contrast that still separates
them.

## The measurement

For each diagram, `measure-page.py` does four things:

1. It renders the diagram as it is, in the light theme, 1700 pixels wide.
2. It renders the diagram again with its full-page rectangle painted magenta. A magenta pixel in that render is
   page; every other pixel is content.
3. Over the content pixels of the first render, it averages relative luminance (sRGB linearised, Rec. 709
   weights) and converts the mean back to an sRGB grey.
4. For comparison, it also reports the plain mean of the sRGB values.

As measured on the committed diagrams, on their new page:

| Diagram | Pixels | Page | Content luminance | As a grey |
|---|---|---|---|---|
| A1 | 1700 × 1394 | 51.9% | 0.788 | 90.0%, `#e6e6e6` |
| B1 | 1700 × 4175 | 32.2% | 0.847 | 92.9%, `#ededed` |
| B2 | 1700 × 4516 | 27.4% | 0.846 | 92.9%, `#ededed` |
| B3 | 1700 × 3441 | 35.9% | 0.822 | 91.7%, `#eaeaea` |
| B4 | 1700 × 6189 | 27.4% | 0.867 | 93.9%, `#f0f0f0` |
| B5 | 1700 × 4973 | 28.9% | 0.833 | 92.3%, `#ebebeb` |
| B6 | 1700 × 2461 | 40.9% | 0.792 | 90.2%, `#e6e6e6` |
| **All seven, pooled** | 31,393,910 content px | | **0.840** | **92.6%, `#ececec`** |

riemann-diagrams measured one representative poster. This family has no map poster to stand for the rest, so the
number is the pooled mean, over every content pixel of the seven diagrams together. The choice was made on the
diagrams as they were, on white, where the pooled mean was 0.843, sRGB 236.5, also `#ececec`. Against the grey
page, the anti-aliased edges of cards count a little darker, which moves each figure by a few tenths of a percent
and the choice not at all.

## One number for every diagram

The diagrams share one library and one palette. A page that changed shade from one diagram to the next would make
the family look like seven designs. The diagrams measure from 90.0% (A1) to 93.9% (B4). Following riemann-diagrams, a diagram that measures more than a few percent
away from the page is a reason to look at that diagram, not to change the page.

## What changed in the generator

The canvas rectangle used the `bg` token, which card interiors, label tabs and table rows also use. It now has a
token of its own, `page`:

| Token | Light | Dark |
|---|---|---|
| `bg` | `#ffffff` | `#12151b` |
| `page` | `#ececec` | `#12151b` |

The dark theme is unchanged: its page and its cards were already different shades (`#12151b` against the panels'
`#1a1e26`). In each SVG, only the first rectangle and the style's variable lists changed. No diagram's content,
anchors or links moved, and the manifest is unchanged.

## Measuring again

```bash
uv run --no-project --with pillow python diagrams/measure-page.py diagrams/gov-tla/*.svg
```

It prints each diagram, then the pooled figure. Given one diagram, it prints that diagram alone, as
riemann-diagrams' script does.

The script needs `rsvg-convert` on the path. It measures the content against whatever page the diagram has now,
because the mask repaints the page rectangle, and only the as-is render's content pixels count. `rsvg-convert`
ignores `prefers-color-scheme`, so it always renders the light theme.
