import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import Mathlib.RingTheory.Artinian.Ring

/-!
# Example 9.5.2: Blocks of specific algebras

(i) For a semisimple algebra A, the blocks of A-fmod correspond to the simple summands.
Each block is equivalent to the category of vector spaces (since every module is a direct
sum of copies of one simple).

(ii) If A is a commutative local artinian algebra, then A has only one block (since there
is only one simple module — the residue field).

(iii) The algebra from Problem 9.3.2 has one block.
-/

universe v u

open CategoryTheory

/-- For a semisimple ring, any two non-isomorphic simple modules have
`Ext¹ = 0` in both directions, so each simple module forms its own block.
(Etingof Example 9.5.2 (i)) -/
theorem Etingof.semisimple_blocks_singleton
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (hlinked : Etingof.AreLinked R X Y) :
    Nonempty (X ≅ Y) := by
  sorry

/-- For a commutative local artinian ring, there is only one simple module (up to
isomorphism), so all modules belong to a single block.
(Etingof Example 9.5.2 (ii)) -/
theorem Etingof.local_artinian_single_block
    (R : Type u) [CommRing R] [Small.{v} R] [IsLocalRing R] [IsArtinianRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) :
    Etingof.AreLinked R X Y := by
  sorry
