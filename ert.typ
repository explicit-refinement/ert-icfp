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

    #align(bottom + right, [
            #only("-5", image("haskell.svg", height: 20%))
            #only("6-", image("liquid-haskell.png", height: 30%))
    ])
]