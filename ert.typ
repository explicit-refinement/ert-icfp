#import "@preview/polylux:0.3.1": *

#import themes.simple: *

#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

#title-slide[
  = Explicit Refinement Types
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami

  University of Cambridge
  
  September 7

  ICFP'23 -- Seattle
]

#slide[
    #one-by-one[
        #only("4-")[
            ```haskell
            -- the output length is the sum of the input lengths
            ```
        ]
        #only("-6")[
            ```haskell
            append :: [a] -> [a] -> [a]
            ```
        ]
        #only("7-")[
            ```haskell
            append :: l:[a] -> r:[a] -> {v: [a] | len v == len l + len r}
            ```
        ]
    ][
        ```haskell
        append [] ys = ys
        ```
    ][
        ```haskell
        append (x:xs) ys = x:(append xs ys)
        ```
    ]

    #only(5)[
        #align(center + horizon)[
            #grid(columns: 3, column-gutter: 1em,
                image("liquid-haskell.png", height: 30%),
                $∨$,
                image("agda.svg", height: 30%)
            )
        ]
    ]

    #only(8, align(center + horizon, text(green,
        ```
        **** LIQUID: SAFE (2 constraints checked) ****
        ```
    )))

    #align(bottom + right, [
            #only("-5", image("haskell.svg", height: 20%))
            #only("6-", image("liquid-haskell.png", height: 30%))
    ])
]

#slide[
    #align(center + horizon)[
        ```haskell
        data Vec (A : Set) : ℕ → Set where
            []  : Vec A 0
            _∷_ : ∀ (x : A) (xs : Vec A n) → Vec A (s n)
        ```
    ]
    #align(bottom + right, image("agda.svg", height: 30%))
]

#slide[
    ```haskell
    -- the output length is the sum of the input lengths
    ```
    #only("1-")[
        `append : (m n : ℕ) -> Vec A m -> Vec A n -> Vec A `
        #only("-4")[`(m + n)`]
        #only("5", text(red, `(n + m)`))
        #only("6-", `(n + m)`)
    ]
    #only("2-6")[
        ```haskell
        append 0 n [] ys = ys
        ```
    ]
    #only("3-6")[
        ```haskell
        append (s m) n (x ∷ xs) ys = x ∷ (append xs ys)
        ```
    ]
    #only("8-")[
        ```haskell
        append 0 n [] ys = subst (Vec _) (sym (+-identityʳ _)) ys
        ```
        ```haskell
        append (s m) n (x ∷ xs) ys = subst (λ t → t) 
            (cong (Vec _) (sym (+-suc _ _))) 
            (x ∷ (append xs ys))
        ```
        //TODO: fill in underscores
    ]
    #align(center + horizon)[
        #only("4", text(blue, $sans("*All Done*")$))
        #only("6", text(red, 
            ```
            n != n + 0 of type ℕ
            when checking that the expression ys has type Vec A (n + 0)
            ```
        ))
        #only("7",
            ```
            0 + n = 0
            s m + n = s (m + n)
            ```
        )
    ]
    #align(bottom + right, image("agda.svg", height: 30%))
]

#slide[
    ```haskell
    -- the output length is the sum of the input lengths
    append :: l:[a] -> r:[a] -> {v: [a] | len v == len r + len l}
    ```
    ```haskell
    append [] ys = ys
    ```
    ```haskell
    append (x:xs) ys = x:(append xs ys)
    ```

    #only(2, align(center + horizon, text(green,
        ```
        **** LIQUID: SAFE (2 constraints checked) ****
        ```
    )))
    
    #align(bottom + right, image("liquid-haskell.png", height: 30%))
]

#focus-slide[
    = Why _not_ refinement types?
]

#slide[
    #one-by-one[][
        = Quantifiers
    ][$
        ∀x, y. x ≤ y ==> f(x) ≤ f(y) "(Monotonicity)"
    $][$
        ∀x, y, z. R(x, y) ∧ R(y, z) ==> R(x, z) "(Transitivity)"
    $][
        = Multiplication
    ][$
        3x dot 5y = 2y dot 5x + 4x dot y + x dot y
    $]
]

#slide[
    = Reliability
    #align(center, box(align(left, one-by-one[][
    ][
        ```
        (assert (forall ((a Int))
                (exists ((b Int))
                (= (* 2 b) a))))
        ```
    ][
        ```
        (check-sat)
        ```
    ][
        #text(olive, `sat`)
    ])))

    #align(bottom)[
        #cite("fuzz", style: "chicago-author-title")
    ]
]

#slide[
    = Folklore

    #v(0.5em)

    #let pro(txt) = align(left, [#text(olive, "✓") #txt])
    #let con(txt) = align(left, [#text(red, "✗") #txt])

    #align(center, grid(
        columns: 2,
        column-gutter: 6em,
        row-gutter: 1em,
        [*Refinement Types*],
        [*Dependent Types*],
        only("2-", pro[High automation]),
        only("3-", con[Low automation]),
        only("4-", con[Low expressivity]),
        only("5-", pro[High expressivity]),
        only("6-", con[Big TCB]),
        only("7-", pro[Small TCB])
    ))

    #only("8-", align(bottom, 
        cite("ftrs", style: "chicago-author-title")))
]

#slide[
    LOGIC GOES HERE
]

#let gst(x) = text(gray, x)

#slide[
    #only("1-")[
        ```
        append : ∀m n: ℕ -> Array A m -> Array A n -> Array A (m + n)
        ```
    ]
    #only("3-")[
        `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#text(gray,{
            only("3", `, _: len ys = 0 + n}`)
            only("4", [`, `

            `   trans[len ys =(q) n =(?) 0 + n]}`]
            )
            only("5-", [`, `
            
            `   trans[len ys =(q) n =(β) 0 + n]}`]
            )
        })
    ]

    #only("6-")[
        `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

        `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
        #gst(`n m {`)`xs`#gst(`, _: len xs = n}`)` in `

        `       `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = (s m) + n}`)
    ]
    #align(bottom)[
        #only("2-")[
            #v(1em)
            ```haskell
            Array A n := { l : List A | len l = n }
            ```
        ]
    ]
]

//TODO: EXPLAIN GHOSTS HERE

//Make stuff go poof

//Reappear, and do stuff here

#slide[
    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`, _: len xs = m}`)` in `

    #gst(`     {`)`x:zs`#gst(`, _: len(x:zs) = (s m) + n}`)
]

#slide[
    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (_: s (len xs) = s m)}`)
    
    `   in `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = (s m) + n}`)
]

#slide[
    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (trans[s (len xs) = (β) len (x:xs) =(p) s m])}`)


    `   in `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = (s m) + n}`)
]

#slide[
    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (trans[s (len xs) = (β) len (x:xs) =(p) s m])}`)


    `   in `#gst(`{`)`x:zs`#gst([
        `, trans[(s m) + n ` 
        
        #only("2-", `                             =(β) s(m + n)`)
        
        #only("3-", `                             =(r) s(len zs)`)

        #only("4-")[
            `                             =(β) len (x:zs)`

            `   ]}`
        ]
        ])
]

//TODO: going to write a signature and implementation which superficially resembles our Agda program
//TODO: I have a type that says ∀m n, it says what it says
//TODO: At this point, want to then give def and can mention that the gray stuff will be explained soon

//TODO: Vec be Array

#slide[
    ```
    append : ∀m n: ℕ -> Vec A m -> Vec A n -> Vec A (m + n)
    ```
    `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
        `   trans[len ys =(q) n =(β) 0 + n]`]
    )

    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (trans[s (len xs) = (β) len (x:xs) =(p) s m])}`)

    `   in `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = (s m) + n}`)
]

#slide[
    `append : ∀m n: ℕ -> Vec A m -> Vec A n -> Vec A `#text(red, `(n + m)`)

    `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
        `   _: len ys = m + 0]`]
    )

    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (trans[s (len xs) = (β) len (x:xs) =(p) s m])}`)

    `   in `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = m + (s n)}`)
]

#slide[
    `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
        #only("-4")[`   _: len ys = m + 0]`]
        #only("5-")[`   trans[len ys =(q) m =(zero-right-id m) m + 0`]]
    )

    #align(bottom)[
        #uncover("2-")[
            #v(1em)
            ```
            zero-right-id : ∀n: ℕ -> n + 0 = n 
            ```
        ]
        #uncover("3-")[
            ```
            zero-right-id 0 = β
            ```
        ]
        #uncover("4-")[
            ```
            zero-right-id (s n) = trans [
                (s n) + 0 =(β) s (n + 0) =(zero-right-id n) (s n)
            ]
            ```
        ]
    ]
]

#slide[
    `append : ∀m n: ℕ -> Vec A m -> Vec A n -> Vec A (n + m)`

    
    `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
        `   trans[len ys =(q) m =(zero-right-id m) m + 0]`]
    )

    `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

    `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
    #gst(`n m {`)`xs`#gst(`,`)

    #gst(`       s_inj (trans[s (len xs) = (β) len (x:xs) =(p) s m])}`)

    `   in `#gst(`{`)`x:zs`#gst(`, _: len(x:zs) = m + (s n)}`)

    #align(bottom)[
        ```
        zero-right-id : ∀n: ℕ -> n + 0 = n 
        ```
        #uncover("2")[
            ```
            succ-right : ∀m n: ℕ -> m + (s n) = s (m + n)
            ```
        ]
    ]
]

//TODO: reinforce by disappearing ghosts again

//TODO: Make underscores ...

//TODO: make lemmas gray

#slide[
    ```
    mul-comm: ∀{m n: ℕ} -> m * n = n * m
    ```
    #only("2-")[
        ```
        mul-comm 0 n = trans[0 * n 
            =(β) 0 =(mul-zero-right n) n * 0]
        ```
    ]
    #only("4-")[
        ```
        mul-comm (s m) n = trans[(s m) * n =(β) (m * n) + n 
            =(mul-comm m (s n)) (n * m) + n
            =(mul-succ (s n) m) n * (s m)]
        ```
    ]
    #align(bottom)[
        #uncover("3-")[
            ```
            mul-zero-right : ∀n: ℕ -> n * 0 = 0
            ```
        ]
        #uncover("5-")[
            ```
            mul-succ : ∀m n: ℕ -> m * (s n) = m * n + m
            ```
        ]
    ]
]

#focus-slide[
    = Semantics
]

#let sep = $med | med$
#let dnt(tm) = $[|tm|]$
#let tstlc = $scripts(⊢)_λ$

#slide[
    #align(center + horizon)[
        $#uncover("2-", $|$)sans("Array") med A med n#uncover("2-", $|$) #uncover("3-", $quad = quad sans("List") med |A|$)$
        #uncover("4-")[
            $
            sans("len") v < n
            $
        ]
        #uncover("5-")[
            $
            ∀n ∈ ℕ, #uncover("6-", $∃m ∈ ℕ,$) #uncover("7-", $m sans("prime") ∧ m ≥ n$)
            $
        ]
    ]
]

#polylux-slide(max-repetitions: 20)[
    #grid(
        row-gutter: 1em,
        column-gutter: 0.5em,
        columns: 6,
        $X, Y :=$,
        uncover("2-", $bold(1)$),
        uncover("2-", $| ℕ$), 
        uncover("3-", $| X + Y$),
        uncover("4-", $| X × Y$),
        uncover("5-", $| X -> Y$),
        uncover("6-", $A, B :=$),
        uncover("7-", $bold(1)$),
        uncover("7-", $| ℕ$), 
        uncover("8-", $| A + B$),
        uncover("9-", $| (a: A) × B$),
        uncover("10-", $| (a: A) → B$),
        $$, $$, $$, $$,
        uncover("11-", $| ∃a: A, B$),
        uncover("12-", $| ∀a: A, B$),
        $$, $$, $$, $$,
        uncover("13-", $| {a: A | φ}$),
        uncover("14-", $| (p: φ) => A$),
        uncover("15-", $φ, ψ :=$),
        uncover("16-", $⊤$),
        uncover("16-", $| ⊥$),
        uncover("17-", $| φ ∨ ψ$),
        uncover("17-", $| (p: φ) ∧ ψ$),
        uncover("18-", $| (p: φ) => ψ$),
        $$, $$, $$, uncover("20-", $| a scripts(=)_A b$),
        uncover("19-", $| ∃a: A, φ$),
        uncover("19-", $| ∀a: A, φ$),
    )
    #only("7-14")[
        #align(center + horizon, rect(inset: 0.5em)[
            #only(7, $|bold(1)| = bold(1), quad |ℕ| = ℕ$)
            #only(8, $|A + B| = |X| + |Y|$)
            #only(9, $|(a: A) × B| = |A| × |B|$)
            #only(10, $|(a: A) → B| = |A| → |B|$)
            #only(11, $|∃a: A, B| = |B|$)
            #only(12, $|∀a: A, B| = bold(1) -> |B|$)
            #only(13, $|{a: A | φ}| = |A|$)
            #only(14, $|(p: φ) => A| = bold(1) -> |A|$)
        ])
    ]

    // #only("24-")[
    //     $Γ := quad dot 
    //         #only("24-", $sep Γ, x: A$)
    //         #only("25-", $sep Γ, p: φ$)
    //         #only("26-", $sep Γ, ||x: A||$) 
    //         quad quad
    //         #only("24-26")[
    //             #rect(inset: 0.5em)[
    //                 #only("24", $|Γ, x: A| = |Γ|, x: |A|$)
    //                 #only("25", $|Γ, p: φ| = |Γ|, p: bold(1)$)
    //                 #only("26", $|Γ, ||x: A||| = |Γ|, x: bold(1)$)
    //             ]
    //         ]
    //     $
    // ]

    // #align(center + horizon)[
    //     #uncover("22-", $Γ ⊢ a: A$)
    //     #uncover("23-", $quad ==> quad $)
    //     #alternatives-match((
    //         "21-22": $Δ tstlc t: X$,
    //         "23-": $|Γ| tstlc |a|: |A|$
    //     ))

    //     #grid(columns: 2, 
    //         column-gutter: 3em,
    //         only("27-")[$Γ ⊢ A sans("ty")$],
    //         only("28-")[$Γ ⊢ φ sans("pr")$]
    //     )
    // ]
]

//TODO: contexts and judgements

#slide[
    $
    #rect(inset: 0.5em, $
        dnt(X): sans("Set")
    $)
    $
    $
    #uncover("2-", $dnt(bold(1)) = {()},$) 
    quad #uncover("3-", $dnt(ℕ) = ℕ,$) 
    quad #uncover("4-", $dnt(X + Y) = dnt(X) ⊔ dnt(Y),$)
    $
    $
    #uncover("5-", $dnt(X × Y) = dnt(X) × dnt(Y),$) 
    quad #uncover("6-", $dnt(X → Y) = dnt(X) → 
        #alternatives(start: 7, repeat-last: true, 
            $sans("Error")$,
            text(red, $sans("Error")$)
        )dnt(Y)$)
    $
    #only("9-")[
        $
        #rect(inset: 0.5em, $
            dnt(Δ): sans("Set")
        $)
        $
        $
        dnt(dot) = {()}, quad
        dnt(#$Δ, x: A$) = dnt(Γ) × sans("Error")A
        $
    ]
]

#polylux-slide(max-repetitions: 25)[
    #only("-10")[
        $
            #rect(inset: 0.5em, $dnt(X): sans("Set")$) quad
            #rect(inset: 0.5em, $dnt(Γ): sans("Set")$)
            #only("3-", $
                quad #rect(inset: 0.5em, 
                    $dnt(Δ tstlc t: X): dnt(Γ) -> sans("Error")dnt(X)$)
            $)
        $
        #only("2")[
            $
            #rect(inset: 0.5em, 
                $dnt(Δ tstlc t: X): dnt(Δ) -> sans("Error")dnt(X)$) 
            $
        ]
    ]
    #only("3-")[
        $
        #rect(inset: 0.5em, $dnt(Γ ⊢ A sans("ty")) med γ ⊆ sans("Error")dnt(|A|)$)
        #only("15-", $
            quad #rect(inset: 0.5em, 
                $dnt(Γ tstlc φ sans("pr")): dnt(|Γ^↑|) -> sans("Prop")$)
        $)
        $
    ]
    #only("20-")[
        $
        #rect(inset: 0.5em, 
                $dnt(Γ sans("ok")): dnt(|Γ^↑|) -> sans("Prop")$)
        $
    ]
    #only("4-7")[
        $
        γ ∈ dnt(Γ^↑)
        $
    ]
    #align(center + horizon)[
        #only("5-7")[
            $
            dot^↑ &= dot \
            #only("6-", $(Γ, x: A)^↑ &= Γ^↑, x: A$) \ 
            #only("6-", $(Γ, p: φ)^↑ &= Γ^↑, p: φ$) \
            #only("7-", $(Γ, ||x: A||)^↑ &= Γ^↑, x: A$) \
            $
        ]
        #only("8-10")[
            $
            dnt({x: ℕ | x < n})
            $
        ]
        #only("9-10")[
            $
            dnt({x: ℕ | x < 3}) med γ = {0, 1, 2}
            $
        ]
        #only("10")[
            $
            dnt({x: ℕ | x < 5}) med γ = {0, 1, 2, 3, 4}
            $
        ]
        #only("11")[
            $
            dnt(#$Γ ⊢ (x: A) -> B sans("ty")$) med γ
            & = {f: dnt(|A|) -> sans(M)dnt(|B|) 
            \ & #h(2em) | ∀ a ∈ dnt(Γ ⊢ A sans("ty")) med γ,
            \ & #h(3em)  f med a ∈ cal(E)dnt(#$Γ, x: A ⊢ B sans("ty")$)(γ, sans("ret") x) 
            }
            $
        ]
        #only("12")[
            $
            dnt(#$Γ ⊢ ∀x: A, B sans("ty")$) med γ
            & = {f: bold(1) -> sans(M)dnt(|B|) 
            \ & #h(2em) | ∀ a ∈ dnt(Γ ⊢ A sans("ty")) med γ,
            \ & #h(3em)  f med () ∈ cal(E)dnt(#$Γ, x: A ⊢ B sans("ty")$)(γ, sans("ret") x) 
            }
            $
        ]
        #only("13")[
            $
            dnt(#$Γ ⊢ ∃x: A, B sans("ty")$) med γ &
            = ⋃_(x ∈ dnt(Γ ⊢ A sans("ty")) med γ)dnt(#$Γ, x: A ⊢ B sans("ty")$) med (γ, sans("ret") x)
            $
        ]
        #only("14")[
            $
            dnt(#$Γ ⊢ {x: A | φ} sans("ty")$) med γ &
            = {x ∈ dnt(Γ ⊢ A sans("ty")) med γ 
            \ & #h(2em) | dnt(#$Γ, x: A ⊢ φ: sans("pr")$) med (γ, sans("ret") x)}
            $
        ]    
        #only("16")[
            $
            dnt(Γ ⊢ ⊤ sans("pr")) med γ = ⊤ quad
            dnt(Γ ⊢ ⊥ sans("pr")) med γ = ⊥
            $
        ]
        #only("17")[
            $
            dnt(Γ ⊢ a scripts(=)_A b sans("pr")) γ
                = [dnt(|Γ^↑ ⊢ a: A|) med γ = dnt(|Γ^↑ ⊢ b: A|) med γ]
            $
        ]
        #only("18-19")[
            $
            dnt(#$Γ ⊢ ∃x: A, φ sans("pr")$) γ
            & = ∃x ∈ dnt(Γ ⊢ A sans("ty")) med γ, 
            \ & #h(4em) dnt(#$Γ, x: A ⊢ φ sans("pr")$ (γ, sans("ret") x))
            $
        ]
        #only("19")[
            $
            dnt(#$Γ ⊢ ∀x: A, φ sans("pr")$) γ
            & = ∀x ∈ dnt(Γ ⊢ A sans("ty")) med γ, 
            \ & #h(4em) dnt(#$Γ, x: A ⊢ φ sans("pr")$ (γ, sans("ret") x))
            $
        ]    
    ]
    #only("21")[
        $
        dnt(dot sans("ok")) med γ 
            &= ⊤ \
        $
    ]
    #only("22")[
        $
        dnt(dot sans("ok")) med γ 
            &= ⊤ \
        dnt(#$Γ, p: φ sans("ok")$) med γ 
            &= dnt(Γ sans("ok")) med γ ∩ dnt(Γ ⊢ φ: sans("pr")) med γ \
        $
    ]
    #only("23")[
        $
        dnt(dot sans("ok")) med γ 
            &= ⊤ \
        dnt(#$Γ, p: φ sans("ok")$) med γ 
            &= dnt(Γ sans("ok")) med γ ∩ dnt(Γ ⊢ φ: sans("pr")) med γ \
        dnt(#$Γ, x: A$) med (γ, sans("ret") x)
            &= dnt(#$Γ, ||x: A||$) med (γ, sans("ret") x) \
            &= dnt(Γ sans("ok")) med γ ∧ x ∈ dnt(Γ ⊢ A sans("ty")) med γ
        $
    ]
]

#slide[
    = Semantic Regularity

    #align(center + horizon, [
        #uncover("2-")[
            $
            ∀G ∈ dnt(Γ sans("ok")),
                dnt(|Γ| tstlc |a|: |A|) med γ^↓
                ∈ dnt(Γ ⊢ a sans("ty")) med γ
            $
        ]
        #uncover("3-")[
            $
            dnt(Γ ⊢ ⊥ sans("pr")) med γ = ⊥
            $
        ]
    ])
]

#slide[
    = Recap
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

#slide[
    #align(center + horizon)[
        = Thank you for listening!
        Contact: #text(olive, link("mailto:jeg74@cam.ac.uk"))
    ]
]

#bibliography("references.bib")