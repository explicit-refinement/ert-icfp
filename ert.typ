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
        #only("3, 8", text(blue, $sans("*All Done*")$))
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