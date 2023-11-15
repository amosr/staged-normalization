# Staged normalization proposal

I have a half-suggestion / half-question about a more predictable variant of normalization for my use-case. I haven't worked out all of the details yet, but I was hoping to get feedback on whether it's worth trying, or if it's possible to achieve something similar with the existing normalization machinery.

In my project, I've defined a translation from a deeply-embedded language to a shallow embedding, and I'm relying on the normalizer, with a carefully-chosen set of names, to simplify away the translation. This is nice when it works, but it can be a bit fragile. If I remember correctly, I believe @protz mentioned that the Noise* implementation, which uses strictness annotations and `inline_for_extraction` to control normalization, ran into similar fragility problems.

I was wondering whether it would be possible / useful to introduce a sort of lightweight staging. I was imagining introducing a type `later` that represents values that are not yet available, as well as a normalizer mode that eagerly evaluates any non-later values. We could represent the type `later` as an applicative functor, so we can defer values until later, and combine later values, but we can't use them or pattern match on them "now". (Perhaps it could be a monad too but I don't think it's necessary.)

The normalizer mode I'm imagining will eagerly evaluate non-later values, but leave laters more-or-less as-is. The intuition is that we want to specialise the values we have now, but not speculate too much about values that won't be known until the future. I am imagining a normalizer mode that assumes that every non-later variable in the environment has a concrete value. When it encounters an abstraction, it only descends if the argument type is a later; non-later abstractions are left as-is, because we don't have a concrete value for the argument (yet). Pattern matches can only match on non-later values, so they can be matched away.

## Proposal

I will now describe the concrete proposal.

I am imagining a small user-space module that contains the `later` modality.
Conceptually, `later t` means that we will have a `t` in the future, but we can't inspect it yet.
We can implement it as just a `t` and hide the definition.
Crucially, there's no *executable* way to go from a `later t` to a `t`, as that would let user code pattern match on non-concrete values.
For specifications, however, we probably do want a ghost function that extracts the value from a `later t`.
A minimal implementation really just needs `return` and applicative functor operations `<$>` and `<*>`.

```
module FStar.Staging.Later

// NOTE: type definition is not exported so that outside code cannot look unwrap laters
type later (t: Type) = t

let extract (#t: Type) (l: later t):
  Ghost t (requires True) (ensures (fun r -> True)) =
  l

let return (#t: Type) (value: t):
  (res: later t { extract r == value }) =
  value

let (<*>) (#t #u: Type) (fn: later (t -> u)) (value: later t): u: later u { extract u == extract fn (extract value) } = fn value

let (<$>) (#t #u: Type) (fn: (t -> u)) (value: later t): u: later u { extract u == fn (extract value) } =
  fn value
```

I am also imagining a tactic or normalization option to perform staged normalization.
I don't think the normalization has to be very different from the existing one: most of the 
Specialisation / staged normalisation mode:
```
stage: expr -> expr

// Explicit staging operators are left as-is
stage (Later.return e) = Later.return e
stage (f Later.<*>  e) = f Later.<*> e

stage (x: later t) = x
stage (x:       t) = unfold x
stage Type#u       = Type#u
stage (a -> b)     = stage a -> stage b
stage (fun (x: later t) -> e) =
  fun (x: later t) -> stage e
stage (fun (x:       t) -> e) =
  fun (x:       t) ->       e
stage (e1 $ e2) =
  match stage e1 with
  | (fun x -> e1') -> e1'[x := stage e2]
  | e1' -> e1' $ stage e2

stage (let x = e1 in e2) =
  let x = stage e1 in stage e2

stage (match s with | c_n -> e_n... ) =
  match stage s with
  | C_i e_a' -> stage e_i
```

## Questions

Can this be implemented with current normalizer options?

Can (and should) this be implemented as a tactic rather than a new normalizer option or plugin?
