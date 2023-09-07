- Hello, I'm Jad Ghalayini from Cambridge, and I'm going to talk to you about explicit refinement types
- Consider the following simple program, which appends the left list to the front of the right
- Appending an empty list to the front is just the identity
- Whereas, to append a list starting with x to the front, we first stick x at the front, and then recursively append the rest
- Now, this program has many properties; which ones we're interested in depends on our application
- Here's a simple one that might be relevant: the length of the output is the sum of the input lengths
- We could put that in a comment, but it might not be true; or if it is true now, it might rot
- Typically, this is the type of thing you'd put into a property test
- But what if we could statically _prove_ this was the case?
- There are two standard techniques to do this:
    - Refinement types, here illustrated by Liquid Haskell
    - Dependent types, here illustrated by Agda
- Let's start with Liquid Haskell
- All we have to do is take our assertion, and stick it in the signature, likeso
- As you can see, we've replaced the return type with a _subtype_ which is logically guaranteed to satisfy our desired property; the particular subtype depends on the value of the inputs, so there's a measure of type dependency
- Anyways, let's run the compiler
- Yey
- OK, let's do it in Agda
- To write out our desired signature, we're going to need to introduce the type family _Vec_, which contains, for each natural number _n_, the type of lists of length _n_
- This is defined inductively about how you'd expect:
    - The lists of length 0 consist of the empty list
    - To make a list of length (n + 1), stick an element at the front of a list of length n
- Alright, with that, we're ready to write out our Agda signature
- We've got to add two _indices_, which we've highlighted here, which we can use to essentially tell the vectors what length they are
- As we can see, for each case, the definition is otherwise the same: we've just got to pass in the length at the front
- Let's typecheck it... Yay!
- Alright, let's try something a little different
- This should be the same, right? I mean, we know that `m + n = n + m`, since addition is commutative
- Let's try running the typechecker...
- Alas! But we know that `n = n + 0`, in arithmetic, so what's going on here
- Well, when typechecking, Agda is only allowed to use _definitional_ equality
- Taking a look at the definition of equality, it's allowed to rewrite using these, and only these rules, and there's no way to use these rules to derive our desired fact
- Alas! That means we have to use... casts...
- Eww
- Alright, let's try it using refinement types
- Much better
- So... why would we ever _not_ use refinement types
- Well, refinement types have excellent support for reasoning about simple properties, as we've seen before. But say, for example, we want to talk about slightly more complex properties, like
    - Monotonicity
    - Transitivity
- These properties make use of _quantifiers_, and so can't be reliably inferred by the SMT solvers which make refinement types go.
- Even worse, let's say I simply need to multiply two integers. 
- I can't, since integer arithmetic becomes undecidable pretty quickly!
- That's why many refinement type systems are restricted to only _quantifier free_, _linear_ integer arithmetic. So multiplying an integer by a constant is OK, but multiplying two integers is a no-go.
- Furthermore, SMT solvers are extremely complicated pieces of software, with a lot of moving parts. Even worse, they are often implemented in C++.
- As we know, that means they contain bugs, _especially_ in experimental support for more expressive logical constructs like quantifiers. For example, let's say we went up to our friendly neighborhood Z3 instance `n` years ago and asserted
    - for all integers a, there exists an integer b such that 2*b = a
    - in other words, all integers are even
- I ask the solver, "is this formula satisfiable"
- Alas, it was going through a bit of a people-pleaser phase, so it replies, "sure thing!"
- That's no good!
- So, at this point, I've reiterated some common folklore
    - Refinement types have high automation, dependent types have low automation
    - Refinement types can express only limited properties, dependent types can express essentially all of modern mathematics
    - Refinement types have a big TCB, dependent types, satisfying the de-Bruijn criteria, have a small TCB
- This, however, is nothing more than an empirical statement. For example, Melliès and Zeilberger show that even very rich systems such as Hoare Logic can be viewed as refinement type systems
- Our goal is to build a refinement type system capable of reasoning about complicated properties which
    - Use quantifiers, like commutativity
    - Arithmetic, like the following bound
    - Or even things like schemes, primarily for the memes
- Let's illustrate with everyone's favorite example: append
- Superficially, we can see that this signature looks almost exactly like the corresponding Agda code
- It's not quite the same, however: our `Array` type, in particular, is quite different, because instead of an inductively defined type, it's simply a _subtype_ of regular old lists
- The base case is about the same as always, except that the _inputs_ contain a proof that they satisfy the desired properties
    - Here, `p` being a proof the empty list of length 0
    - And `q` being a proof `ys` is of length `n`
- The _result_, similarly, needs to be annotated with _some_ proof that `ys` is of length `0 + n`
- We know it's of length `n`, so we can start a proof by transitivity, but now we somehow need to figure out that `0 + n = n`
- That, however, is just true by β, so we can write that in. β-reduction, then, is simply an axiom like any other!
- Let's do the successor case now
- We destructure the arguments again, with
    - `p` a proof `xs` is of length `succ n`
    - `q` a proof `ys` is of length `m`
- As before, we make a recursive call to append on `xs` and `ys`, _but_ we need to destructure that call, since it returns not only a result list, but also a proof it's of length `n + m`. We've also, of course, got proof obligations on the arguments to our recursive call
- Then, we just return our appropriately modified result, with, of course, a proof the result satisfies our desired property
- So far so good!
- You'll notice that a lot of this text is greyed out
- To understand that, we have to understand the fancy ∀ binder all the way back in the signature: it indicates that `m` and `n` are _ghost variables_; in other words, that for runtime purposes, they might as well not exist, since they are _only_ usable for specification
- So as we can see, their values are greyed out
- More than that, all the proof values are _also_ greyed out, since they are also guaranteed to be erased at runtime. Indeed, if they weren't, we wouldn't be allowed to refer to ghost variables inside them!
- And we can go ahead and do that erasure, to recover a simply typed term...
- That's the core property of our type system, which makes it a refinement type system: we can _always_ safely erasre all our fancy type information, to get back a pile of simple types
- Back to our example, let's again try flipping `m` and `n` in the signature
- As we can see, our proof obligations change, but the _shape_ of our program remains the same
- Let's try filling in our obligation for the base case:
- We can start a proof by transitivity using `q`
- But, we now need to prove that `n` is the same as `n + 0`, but that's _not_ true by β
- So we need a lemma saying just that!
- We can prove it by induction, of course:
    - The base case holds by β
    - And the successor case by β, followed by induction
- We can now just plug our lemma in, just like β:
    - This is one of the major design features of our calculus: type equality is just up to α-conversion, with β-equality simply an proposition like any other
- Returning to our completed program, we can erase it...
- And it's the same thing as before!
- However, while our proof by induction was suggestive, we haven't yet done anything a traditional SMT-based refinement type system couldn't do.
- So let's try proving a slightly more nontrivial lemma; namely, that multiplication commutes
- We've got the base case, using the following lemma
- And the successor case, again using the following lemma
- We could do some more math, but I hope that gives the flavor of it
- So... let's recap what we've done so far:
    - We've got fancy types
    - We can erase them to simple types
    - We refine our _higher order_ types with _first order_ predicates, like
        - The length of `v` is less than `n`
        - Or, for all naturals `n`, there exists a natural `m` greater than or equal to `n` such that `m` is prime; that is, there are infinitely many prime numbers
- More specifically, we've got the simple types you'd expect:
    - Units and nats
    - Coproducts
    - Products
    - And of course, functions
- We refine these into _fancy_ types:
    - Units and nats erase to themselves
    - Coproducts, which erasure distributes over
    - _Dependent_ products, which erasure distributes over, eliminating the dependency
    - And similarly, _dependent_ functions, which erasure also distributes over
- We now throw in _existentially quantified types_, which are a pair of a ghost variable and a variable of a refined type which may contain that ghost. To erase these, just throw out the ghost and erase the refined type
- Similarly, we've got _universally quantified types_, which are like dependent functions, except the first argument is a ghost and so erases to a unit
- We've got probably the core component of any refinement type system, _subset types_, which just erase to the underlying type
- As well as _precondition types_, which take a predicate argument that erases to unit
- As for the predicates themselves, these are about what you'd expect
    - True, false
    - Or, and
    - And implication
- Note, however, that _and_ and _implication_ are both _dependent_: this is because the proposition on the right-hand-side might not be well-formed without the proposition on the left-hand-side holding; for example, it might contain a safe-division requiring a proof that the denominator is nonzero
- We then provide existential and universal quantifiers, giving us a first order logic
- Finally, we throw in propositional equality so we can say things which aren't simply tautologies

... judgements

... renotational pedantics

... error stop

... contexts are what you expect

... simply-typed terms are as usual

... refined types are subsets of the erased type's denotation; allowing us to interpret refined terms using the erasure

... a note on ghosts, due to subsets

... some examples

... props are props, bro

... we've now got a very special prop: a context is valid

... big theorem: semantic regularity

... since false is false, implies consistency

... we did stuff

... it's Lean!