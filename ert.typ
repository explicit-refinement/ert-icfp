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
    #one-by-one[
        #only("4-6")[
            ```haskell
            -- the output length is the sum of the input lengths
            ```
        ]
        #only("7-")[
            ```haskell
            {-@ append :: l:[a] -> r:[a] -> 
                {v: [a] | len v == len l + len r} @-}
            ```
        ]
        ```haskell  
        append :: [a] -> [a] -> [a]
        ```
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
    ```haskell
    -- the output length is the sum of the input lengths
    ```
    #only("1")[
        `append : List A -> List A -> List A`
    ]
    #only("2-")[
        `append : ∀{m n : ℕ} -> Vec A m -> Vec A n -> Vec A `
        #only("-3")[`(m + n)`]
        #only("4", text(red, `(n + m)`))
        #only("5-", `(n + m)`)
    ]
    #only("-6")[
        ```haskell
        append [] ys = ys
        ```
        ```haskell
        append (x ∷ xs) ys = x ∷ (append xs ys)
        ```
    ]
    #only("7-")[
        ```haskell
        append [] ys = subst (Vec _) (sym (+-identityʳ _)) ys
        ```
        ```haskell
        append (x ∷ xs) ys = subst (λ t → t) 
            (cong (Vec _) (sym (+-suc _ _))) 
            (x ∷ (append xs ys))
        ```
    ]
    #align(center + horizon)[
        #only("3", text(blue, $sans("*All Done*")$))
        #only("5", text(red, 
            ```
            n != n + zero of type ℕ
            when checking that the expression ys has type Vec A (n + zero)
            ```
        ))
        #only("6",
            ```
            zero + n = zero
            succ m + n = succ (m + n)
            ```
        )
    ]
    #align(bottom + right, image("agda.svg", height: 30%))
]

#slide[
    ```haskell
    {-@ append :: l:[a] -> r:[a] -> 
        {v: [a] | len v == len r + len l} @-}
    ```
    ```haskell  
    append :: [a] -> [a] -> [a]
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
    = Quantifiers
    #one-by-one[$
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
    #align(center, box(align(left, one-by-one[
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
        [
            #only("-7", [*Dependent Types*])
            #only("8-", [*#text(olive, [Explicit]) Refinement*])
        ],
        only("2-", pro[High automation]),
        only("3-", con[Low automation]),
        only("4-", con[Weak properties]),
        only("5-", pro[Strong properties]),
        only("6-", con[Big TCB]),
        only("7-", pro[Small TCB])
    ))
]

#focus-slide[
    = ⚠ Disclaimer ⚠
]

#slide[
    #only(1)[
        ```haskell
        -- the output length is the sum of the input lengths
        append :: [a] -> [a] -> [a]
        ```
    ]
    #only("2-7")[
        ```haskell
        append : ∀{m n: ℕ} -> Vec A m -> Vec A n -> Vec A (m + n)
        ```
    ]
    #only("-4")[
        ```haskell
        append [] ys = ys
        ```
        ```haskell
        append (x:xs) ys = x:(append xs ys)
        ```
    ]
    #only("3-4")[
        #v(1em)
        ```haskell
        Vec A n := { l : List A | len l = n }
        ```
    ]
    #only("4")[
        vs.
        ```haskell
        data Vec (A : Set a) : ℕ → Set a where
        []  : Vec A zero
        _∷_ : ∀ (x : A) (xs : Vec A n) → Vec A (suc n)
        ```
    ]
    #only("5")[
        ```haskell
        append {0 n} {[], p} {ys, q} = {ys, (_: len ys = 0 + n)}
        ```
    ]
    #only("6-7")[
        ```haskell
        append {0 n} {[], p} {ys, q} = {ys, 
            trans[ len ys =(q) n =(β) 0 + n ]}
        ```
    ]
    #only("5-6")[
        ```haskell
        append {(s m) n} {(x∷xs), p} {ys, q} 
            = let {zs, r} = append {xs, (_: len xs = m)} {ys, q} in 
                {x∷zs, (_: len (x∷zs) = (s m) + n)}
        ```
    ]
    #only("7")[
        ```haskell
        append {(s m) n} {(x∷xs), p} {ys, q} 
            = let {zs, r} = append 
                {xs, s_inj 
                    (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
                {ys, q} in 
                {x∷zs, trans[len (x∷zs) 
                    =(β) s(len zs) 
                    =(r) s(n + m)
                    =(β) s(n) + m]}
        ```
    ]
]

#polylux-slide(max-repetitions: 20)[
    #only("-7, 11-")[
        ```haskell
        append' : ∀{m n: ℕ} -> Vec A m -> Vec A n -> Vec A (n + m)
        ```
    ]
    #only("1-5")[
        ```haskell
        append' {0 n} {[], p} {ys, q} = {ys, (_: len ys = n + 0)}
        ```
    ]
    #only("6-7, 11-")[
        ```haskell
        append' {0 n} {[], p} {ys, q} = {ys, 
            trans[len ys =(q) n =(zero-right-id {n}) n + 0]}
        ```
    ]
    #only("1-11")[
        ```haskell
        append' {(s m) n} {(x∷xs), p} {ys, q} 
            = let {zs, r} = append' {xs, (_: len xs = m} {ys, q} in 
                {x∷zs, (_: len (x∷zs) = n + (s m))}
        ```
    ]
    #only("12")[
        ```haskell
        append' {(s m) n} {(x∷xs), p} {ys, q} 
            = let {zs, r} = append' 
                {xs, s_inj 
                        (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
                {ys, q} in 
                {x∷zs, trans[len(x∷zs)
                    =(β) s (len zs)
                    =(r) s (n + m)
                    =(succ-right {n} {m}) n + (s m)]}
        ```
    ]
    #only("2-11")[
        #v(1em)
        ```haskell
        zero-right-id : ∀{n: ℕ} -> n + 0 = n 
        ```
    ]
    #only("3-4")[
        ```haskell
        zero-right-id {0} = β
        ```
    ]
    #only("4")[
        ```haskell
        zero-right-id {s n} = trans [
            (s n) + 0 =(β) s (n + 0) =(zero-right-id {n}) (s n)
        ]
        ```
    ]
    #only("8-11")[
        ```haskell
        succ-right : ∀{m n: ℕ} -> m + (s n) = s (m + n)
        ```
    ]
    #only("9-10")[
        ```haskell
        succ-right {0} {n} = β
        ```
    ]
    #only("10")[
        ```haskell
        succ-right {s m} {n} = trans[(s m) + (s n) 
            =(β) s (m + (s n))
            =(succ-right {m} {n}) s (s (m + n))
            =(β) s ((s m) + n)]
        ```
    ]
]

#slide[
    ```haskell
    zero-right-id : ∀{n: ℕ} -> n + 0 = n 
    succ-right : ∀{m n: ℕ} -> m + (s n) = s (m + n)
    ```
    #only("2-")[
    ```haskell
    add-comm : ∀{m n: ℕ} -> m + n = n + m
    ```
    ]
    #only("3-")[
    ```haskell
    add-comm m 0 = trans[m + 0 =(zero-right-id {m}) m =(β) 0 + m]
    ```
    ]
    #only("4-")[
    ```haskell
    add-comm m (s n) = trans[m + (s n) 
        =(succ-right {m n}) s (m + n) 
        =(add-comm {m n}) s (n + m)
        =(β) (s n) + m]
    ```
    ]
]

#slide[
    ```haskell
    zero-right-id : ∀{n: ℕ} -> n + 0 = n 
    succ-right : ∀{m n: ℕ} -> m + (s n) = s (m + n)
    add-comm : ∀{m n: ℕ} -> m + n = n + m
    ```
    #only("2-")[
        ```haskell
        _*_ : ℕ -> ℕ -> ℕ
        0 * n = 0
        (s m) * n = (m * n) + n
        ```
    ]
    #only("3-")[
        ```
        mul-zero-right : ∀{n: ℕ} -> n * 0 = 0
        ```
    ]
    #only("4-")[
        ```
        mul-zero-right {0} = β
        ```
    ]
    #only("5-")[
        ```
        mul-zero-right {s n} = trans[(s n) * 0
            =(β) (n * 0) + 0 
            =(mul-zero-right {n}) 0 + 0
            =(β) 0]
        ```
    ]
]

#slide[
    #only("-4")[
    ```haskell
    zero-right-id : ∀{n: ℕ} -> n + 0 = n 
    succ-right : ∀{m n: ℕ} -> m + (s n) = s (m + n)
    add-comm : ∀{m n: ℕ} -> m + n = n + m
    mul-zero-right : ∀{n: ℕ} -> n * 0 = 0
    ```
    ]
    #only("4-")[
        ```haskell
        add-assoc : ∀{m n l: ℕ} -> m + (n + l) = (m + n) + l
        ```
    ]
    #only("2-4")[
        ```
        mul-succ : ∀{m n: ℕ} -> m * (s n) = m * n + m
        ```
    ]
    #only("3")[
        ```
        mul-succ {0} {n} = β
        ```
    ]
    #only("5-")[
        ```
        mul-succ {s m} {n} = trans[(s m) * (s n)
            =(β) m * (s n) + (s n)
            =(mul-succ {m} {n}) (m * n + m) + (s n)
            =(add-assoc {m * n} {n} {s n}) m * n + (m + (s n))
            =(succ-right {m} {n}) m * n + (s (m + n))
            =(β) m * n + ((s m) + n)
            =(add-comm {s m} {n})  m * n + (n + (s m))
            =(add-assoc {m * n} {n} {s m}) (m * n + n) + (s m)
            =(β) (s m) * n + (s m)
        ```
    ]
]

#slide[
    ```haskell
    zero-right-id : ∀{n: ℕ} -> n + 0 = n 
    succ-right : ∀{m n: ℕ} -> m + (s n) = s (m + n)
    add-comm : ∀{m n: ℕ} -> m + n = n + m
    add-assoc: ∀{m n l: ℕ} -> (m + n) + l = m + (n + l)
    mul-zero-right : ∀{n: ℕ} -> n * 0 = 0
    mul-succ : ∀{m n: ℕ} -> m * (s n) = m * n + m
    ```
    #only("2-4")[
        ```
        mul-comm: ∀{m n: ℕ} -> m * n = n * m
        ```
    ]
    #only("3-")[
        ```
        mul-comm {0} {n} = trans[0 * n 
            =(β) 0 =(mul-zero-right {n}) n * 0]
        ```
    ]
    #only("4-")[
        ```
        mul-comm {s m} {n} = trans[(s m) * n =(β) (m * n) + n 
            =(mul-comm {m} {s n}) (n * m) + n
            =(mul-succ {(s n)} {m}) n * (s m)]
        ```
    ]
]

#focus-slide[
    = Erasure
]

#slide[
    ```haskell
    append' : ∀{m n: ℕ} -> Vec A m -> Vec A n -> Vec A (n + m)
    ```
    ```haskell
    append' {0 n} {[], p} {ys, q} = {ys, 
        trans[len ys =(q) n =(zero-right-id {n}) n + 0]}
    ```
    ```haskell 
    append' {(s m) n} {(x∷xs), p} {ys, q} 
        = let {zs, r} = append' 
            {xs, s_inj 
                    (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
            {ys, q} in 
            {x∷zs, trans[len(x∷zs)
                =(β) s (len zs)
                =(r) s (n + m)
                =(succ-right {n} {m}) n + (s m)]}
    ```
]
#slide[
    #only("1-7")[
        ```haskell
        |append'| : () -> () -> List |A| -> List |A| -> List |A|
        ```
    ]
    #only(1)[
        ```haskell
        |append' {0 n} {[], p} {ys, q}| = |{ys, 
            trans[len ys =(q) n =(symm (zero-right-id {n})) n + 0]}|
        ```
        ```haskell
        |append' {(s m) n} {(x∷xs), p} {ys, q}| 
            = |let {zs, r} = append' 
                {xs, s_inj 
                        (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
                {ys, q} in 
                {x∷zs, trans[len(x∷zs)
                    =(β) s (len zs)
                    =(r) s (n + m)
                    =(succ-right {n} {m}) n + (s m)]}|
        ```
    ]
    #only(2)[
        ```haskell
        |append'| () () [] ys = |{ys, 
            trans[len ys =(q) n =(symm (zero-right-id {n})) n + 0]}|
        ```
    ]
    #only("3-7")[
        ```haskell
        |append'| () () [] ys = ys
        ```
    ]
    #only("2-3")[
        ```haskell
        |append'| () () ys 
            = |let {zs, r} = append' 
                {xs, s_inj 
                        (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
                {ys, q} in 
                {x∷zs, trans[len(x∷zs)
                    =(β) s (len zs)
                    =(r) s (n + m)
                    =(succ-right {n} {m}) n + (s m)]}|
        ```
    ]
    #only(4)[
        ```haskell
        |append'| () () {ys, q} 
            = let zs = |append' 
                {xs, s_inj 
                        (trans[s m =(p) len (x∷xs) =(β) s (len x)])} 
                {ys, q}| in 
                |{x∷zs, trans[len(x∷zs)
                    =(β) s (len zs)
                    =(r) s (n + m)
                    =(succ-right {n} {m}) n + (s m)]}|
        ```
    ]
    #only(5)[
        ```haskell
        |append'| () () {ys, q} 
            = let zs = |append'| xs ys in 
                |{x∷zs, trans[len(x∷zs)
                    =(β) s (len zs)
                    =(r) s (n + m)
                    =(succ-right {n} {m}) n + (s m)]}|
        ```
    ]
    #only(6)[
        ```haskell
        |append'| () () {ys, q} = let zs = |append'| xs ys in |x∷zs|
        ```
    ]
    #only(7)[
        ```haskell
        |append'| () () {ys, q} = let zs = |append'| xs ys in x∷zs
        ```
    ]
]

#slide[
    ```haskell
    |append'| : () -> () -> List |A| -> List |A| -> List |A|
    |append'| () () {ys, q} = let zs = |append'| xs ys in |x∷zs|
    |append'| () () {ys, q} = let zs = |append'| xs ys in x∷zs
    ```
    #v(0.5em)
    ```haskell
    |append| : () -> () -> List |A| -> List |A| -> List |A|
    |append| () () {ys, q} = let zs = |append| xs ys in |x∷zs|
    |append| () () {ys, q} = let zs = |append| xs ys in x∷zs
    ```
    #v(2em)
    #align(center, only(2)[
        #set text(size: 40pt)
        `|append| ≡ |append'|`
    ])
]

#focus-slide[
    = Semantics
]

#let sep = $med | med$
#let dnt(tm) = $[|tm|]$
#let tstlc = $scripts(⊢)_λ$

#polylux-slide(max-repetitions: 25)[
    = Erasure, Actually

    #v(1em)

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
        uncover("15-", $| (p: φ) => A$),
        uncover("14-", $φ, ψ :=$),
        uncover("16-", $⊤$),
        uncover("16-", $| ⊥$),
        uncover("17-", $| φ ∨ ψ$),
        uncover("17-", $| (p: φ) ∧ ψ$),
        uncover("18-", $| (p: φ) => ψ$),
        $$, $$, $$, uncover("20-", $| a scripts(=)_A b$),
        uncover("19-", $| ∃a: A, φ$),
        uncover("19-", $| ∀a: A, φ$),
    )

    #only("7-13, 15")[
        #align(center + horizon, rect(inset: 0.5em)[
            #only(7, $|bold(1)| = bold(1), quad |ℕ| = ℕ$)
            #only(8, $|A + B| = |X| + |Y|$)
            #only(9, $|(a: A) × B| = |A| × |B|$)
            #only(10, $|(a: A) → B| = |A| → |B|$)
            #only(11, $|∃a: A, B| = |B|$)
            #only(12, $|∀a: A, B| = bold(1) -> |B|$)
            #only(13, $|{a: A | φ}| = |A|$)
            #only(15, $|(p: φ) => A| = bold(1) -> |A|$)
        ])
    ]
    #only("21-24")[
        $Γ := quad dot 
            #only("22-", $sep Γ, x: A$)
            #only("23-", $sep Γ, ||x: A||$) 
            #only("24-", $sep Γ, p: φ$)
            #only("22", $quad (|Γ, x: A| = |Γ|, x: |A|)$)
            #only("23", $quad (|Γ, ||x: A||| = |Γ|, x: bold(1))$)
            #only("24", $quad (|Γ, p: φ| = |Γ|, p: bold(1))$)
        $
    ]
    #only("25")[
        #align(center + horizon,
            $
            Γ ⊢ a: A ==> |Γ| tstlc |a|: |A|
            $
        )
    ]
]

#slide[
    = Erasure, Actually

    $
    #rect(inset: 0.5em, $
        dnt(X): sans("Set")
    $)
    $
    $
    dnt(bold(1)) = {*}, quad dnt(ℕ) = ℕ, quad dnt(X + Y) = dnt(X) ⊔ dnt(Y),
    $
    $
    dnt(X × Y) = dnt(X) × dnt(Y), quad dnt(X → Y) = dnt(X) → 
    #only("3-", $sans(M)$)#only("2", text(red, $sans(M)$))dnt(Y)
    $
    #only("3-")[
        $
        #rect(inset: 0.5em, $
            dnt(Δ): sans("Set")
        $)
        $
        $
        dnt(dot) = {*}, quad
        dnt(#$Δ, x: A$) = dnt(Γ) × sans(M)A
        $
    ]
]

#polylux-slide(max-repetitions: 20)[
    = Erasure, Actually
    $
        #rect(inset: 0.5em, $dnt(X): sans("Set")$) quad
        #rect(inset: 0.5em, $dnt(Γ): sans("Set")$)
        #only("3-", $
            quad #rect(inset: 0.5em, 
                $dnt(Γ tstlc t: X): dnt(Γ) -> sans(M) dnt(X)$)
        $)
    $
    #only("2")[
        $
        #rect(inset: 0.5em, $dnt(Γ tstlc t: X): dnt(Γ) -> sans(M) dnt(X)$) 
        $
    ]
    #only("3-")[
        $
        #rect(inset: 0.5em, $dnt(Γ ⊢ A sans("ty")): dnt(|Γ^(#only("4", text(red, $↑$))#only("5-", $↑$))|) -> cal(P)(dnt(|A|))$)
        #only("7-", $
            quad #rect(inset: 0.5em, 
                $dnt(Γ tstlc φ sans("pr")) ⊆ dnt(|Γ^↑|)$)
        $)
        $
    ]
    #only("4")[
        $
        dot^↑ &= dot \
        (Γ, x: A)^↑ &= Γ^↑, x: A \ 
        (Γ, ||x: A||)^↑ &= Γ^↑, x: A \
        (Γ, p: φ)^↑ &= Γ^↑, p: φ \
        $
    ]
    #only("5")[
        $
        dnt(#$Γ ⊢ ∃x: A, B sans("ty")$) med G &
        = ⋃_(x ∈ dnt(Γ ⊢ A sans("ty")) med G)dnt(#$Γ, x: A ⊢ B sans("ty")$) med (G, sans("ret") x)
        $
    ]
    #only("6")[
        $
        dnt(#$Γ ⊢ ∀x: A, B sans("ty")$) med G 
        & = {f: bold(1) -> sans(M)dnt(|B|) 
        \ & #h(2em) | ∀ a ∈ dnt(Γ ⊢ A sans("ty")) med G,
        \ & #h(3em)  f med () ∈ cal(E)dnt(#$Γ, x: A ⊢ B sans("ty")$)(G, sans("ret") x) 
        }
        $
    ]
    #only("8-9")[
        $
        dnt(Γ ⊢ a scripts(=)_A b sans("pr")) 
            = {G | dnt(|Γ^↑ ⊢ a: A|) med G = dnt(|Γ^↑ ⊢ b: A|) med G}
        $
    ]
    #only("9")[
        $
        dnt(Γ ⊢ ⊤ sans("pr")) = dnt(|Γ^↑|) quad
        dnt(Γ ⊢ ⊥ sans("pr")) = {}
        $
    ]
    #only("10-11")[
        $
        dnt(#$Γ ⊢ ∃x: A, φ sans("pr")$) 
        & = {G | ∃x ∈ dnt(Γ ⊢ A sans("ty")) med G, 
        \ & #h(4em) (G, sans("ret") x) ∈ dnt(#$Γ, x: A ⊢ φ sans("pr")$)}
        $
    ]
    #only("11")[
        $
        dnt(#$Γ ⊢ ∀x: A, φ sans("pr")$) 
        & = {G | ∀x ∈ dnt(Γ ⊢ A sans("ty")) med G, 
        \ & #h(4em) (G, sans("ret") x) ∈ dnt(#$Γ, x: A ⊢ φ sans("pr")$)}
        $
    ]
    #only("12")[
        $
        dnt(#$Γ ⊢ {x: A | φ} sans("ty")$) med G 
        &= {a ∈ dnt(Γ ⊢ A sans("ty")) med G 
        \ & #h(4em) | (G, a) ∈ dnt(#$Γ, x: A ⊢ φ sans("pr")$)}
        $
    ]
    #only("13-")[
        $
        #rect(inset: 0.5em, 
                $dnt(Γ sans("ok")) ⊆ dnt(|Γ^↑|)$)
        $
    ]
    #only("14")[
        $
        dnt(dot sans("ok")) = {*} quad
        dnt(#$Γ, p: φ sans("ok")$) = dnt(Γ sans("ok")) ∩ dnt(Γ ⊢ φ: sans("pr"))
        $
    ]
    #only("15")[
        $
        dnt(#$Γ, x: A$) =
        dnt(#$Γ, ||x: A||$) &= {(G, sans("ret") x) 
            \ & #h(2em) | G ∈ dnt(Γ sans("ok")) ∧ x ∈ dnt(Γ ⊢ A sans("ty")) med G}
        $
    ]
]

#slide[
    = Semantic Regularity

    #align(center + horizon, [
        #uncover("2-")[
            $
            ∀G ∈ dnt(Γ sans("ok")),
                dnt(|Γ| tstlc |a|: |A|) med G^↓
                ∈ dnt(Γ ⊢ a sans("ty")) med G
            $
        ]
        #uncover("3-")[
            $
            dnt(Γ ⊢ ⊥ sans("pr")) = {}
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
    = Future Work
    #line-by-line[
        - *Automation and solver integration*
        - Function extensionality
        - Recursion
        - Effects
        - Higher order logic
    ]
    #only("6-", align(center + horizon)[
        == Thank you for listening!
        Contact: #text(olive, link("mailto:jeg74@cam.ac.uk"))
    ])
]