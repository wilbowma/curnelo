# curnelo

An implementation of the Curnel of [Cur, a dependently typed programming language](https://github.com/wilbowma/cur), in miniKanren.

Curnelo forms the basis for a new user-defined language layer on top of Cur's trusted core language.
Currently, it is a relational implementation of the Calculus of Constructions with an infinite
universe hierarchy and one impredicative universe.
It aims to add a general purposes unification framework atop Cur, enabling features like type inference,
proof search/program synthesis (holes), and universe constraint solving.

Code by William J. Bowman, Michael Ballantyne, and Will Byrd.

Run queries like the following, which generates two lists of numbers.
```racket
(run 2 (e)
  (fresh (gamma)
    (typeo '((cons . (Pi (a : Nat) (Pi (cdr : NatList) NatList)))
             (nil . NatList)
             (NatList . (Type lz))
             (z . Nat)
             (s . (Pi (x : Nat) Nat))
             (Nat . (Type lz)))
      e gamma 'NatList)))
```