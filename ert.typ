#import "@preview/polylux:0.2.0": *

#import themes.simple: *

#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

#title-slide[
  = Explicit Refinement Types
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami
  
  September 7

  ICFP'23 -- Seattle
]

#slide[
    = Overview
    #line-by-line[
        - We introduce the language #ert:
        - We take a simply typed, effectful lambda calculus #stlc and add refinements 
        - We support a rich logic of properties:
            - Full first-order quantifiers
            - Ghost variables/arguments
        - We support explicit proofs of all properties
        - We give everything a denotational semantics, and prove it sound
        - Everything is mechanized in ∼15,000 lines of Lean 4
    ]
]

#centered-slide[
    = But Why?
]

#let pro = text(olive, "✔")
#let con = text(red, "✘")

#polylux-slide(max-repetitions: 20)[
    = Dependent Types vs Refinement Types
    #set text(size: 20pt)
    #grid(
        columns: 2,
        column-gutter: 3em,
        row-gutter: 1em,
        [*Dependent Types:*],
        uncover("8-")[*Refinement Types#only("16-")[ #text(olive)[in Utopia]]:*],
        uncover("2-")[#pro Expressive logic of properties],
        {
            only("9-15")[#con Restricted logic of properties]
            only("16-")[#pro #text(olive)[*Expressive*] logic of properties]
        },
        uncover("3-")[#pro Support for manual proofs],
        {
            only("10-15")[#con Limited support for manual proofs]
            only("16-")[#pro #text(olive)[*Support*] for manual proofs]
        },
        uncover("4-")[#pro Support for re-use of theorems],
        {
            only("11-15")[#con Limited support for re-use of theorems]
            only("16-")[#pro #text(olive)[*Support*] for re-use of theorems]
        },
        uncover("5-")[#pro Small trusted codebase],
        {
            only("12-15")[#con Large trusted codebase]
            only("16-")[#pro #text(olive)[*Small*] trusted codebase]
        },
        uncover("6-")[#con Limited support for implicit proofs],
        uncover("13-")[#pro Support for implicit proofs],
        uncover("7-")[#con Limited, unreliable type inference],
        uncover("14-")[#pro Robust, predictable type inference],
        [],
        {
            only("15-16")[*Idea: what if we added support for explicit proofs?*]
            only("17-")[*In #text(olive)[utopia], programmers prove interesting things, and computers do the bookkeeping!*]
        }
    )
] 

#centered-slide[
    = But How?
]

#let changed(ctx) = text(red, ctx)

#slide[
    = Explicit Refinement Types

    #v(1em)

    #text(size: 40pt)[
        $
        sans("Vec") med a med n := {ℓ: sans("List") med A | sans("len") med ℓ = n}
        $
    ]
    #alternatives[
        #text(size: 30pt)[
            $sans("Vec").sans("len") &: ∀n: ℕ, sans("Vec") med A med n -> {m: ℕ | m = n}$

            $sans("Vec").sans("len") &:= 
                hat(λ)n: ℕ, λ v: sans("Vec") med A med n, sans("let") {ℓ, p} = v sans("in") med {sans("len") ℓ, p}$
        ]
    ][
        $|sans("Vec").sans("len")| &: |∀n: ℕ, sans("Vec") med A med n -> {m: ℕ | m = n}|$

        $|sans("Vec").sans("len")| &:= 
            |hat(λ)n: ℕ, λ v: sans("Vec") med A med n, sans("let") {ℓ, p} = v sans("in") med {sans("len") ℓ, p}|$
    ][
        $|sans("Vec").sans("len")| &: changed(bold(1) ->) |sans("Vec") med A med n -> {m: ℕ | m = n}|$

        $|sans("Vec").sans("len")| &:= 
            changed(#$λ n: bold(1),$) |λ v: sans("Vec") med A med n, sans("let") {ℓ, p} = v sans("in") med {sans("len") ℓ, p}|$
    ][
        $|sans("Vec").sans("len")| &: bold(1) -> changed(|sans("Vec") med A med n| -> |{m: ℕ | m = n}|)$

        $|sans("Vec").sans("len")| &:= 
            λ n: bold(1), changed(#$λ v: |sans("Vec") med A med n|,$) |sans("let") {ℓ, p} = v sans("in") med {sans("len") ℓ, p}|$
    ][
        $|sans("Vec").sans("len")| &: bold(1) -> changed(sans("List") med |A|) -> changed(ℕ)$

        $|sans("Vec").sans("len")| &:= 
            λ n: bold(1), λ v: changed(sans("List") med |A|), |sans("let") {ℓ, p} = v sans("in") med {sans("len") ℓ, p}|$
    ][
        $|sans("Vec").sans("len")| &: bold(1) -> sans("List") med |A| -> ℕ$

        $|sans("Vec").sans("len")| &:= 
            λ n: bold(1), λ v: sans("List") med |A|, changed(#$sans("let") ℓ = v, sans("in")$) med |{sans("len") ℓ, p}|$
    ][
        $|sans("Vec").sans("len")| &: bold(1) -> sans("List") med |A| -> ℕ$

        $|sans("Vec").sans("len")| &:= 
            λ n: bold(1), λ v: sans("List") med |A|, sans("let") ℓ = v sans("in") med changed(sans("len") ℓ)$
    ]
]