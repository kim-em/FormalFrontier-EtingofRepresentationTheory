import Mathlib

/-!
# Example 4.1.3: Representations of ℤ/pℤ in Characteristic p

If G = ℤ/pℤ and k has characteristic p, then every irreducible representation of G
over k is trivial (1-dimensional with trivial action).

The argument: any irreducible representation is 1-dimensional, and the generator g must
act by a p-th root of unity. But over a field of characteristic p, xᵖ - 1 = (x - 1)ᵖ,
so the only p-th root of unity is 1.

This shows that the hypothesis in Maschke's theorem (char k ∤ |G|) is essential.

## Mathlib correspondence

Uses `ZMod p` for the cyclic group and `CharP k p` for characteristic p.
-/

/-- In characteristic p, every irreducible representation of ℤ/pℤ is trivial.
(Etingof Example 4.1.3) -/
theorem Etingof.Example4_1_3
    (k : Type*) (p : ℕ) [Field k] [hp : Fact (Nat.Prime p)] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Multiplicative (ZMod p)) V)
    (hirr : IsSimpleModule k V) :
    -- Every irreducible rep is trivial: ρ(g) = id for all g
    ∀ g : Multiplicative (ZMod p), ρ g = LinearMap.id := by
  intro g
  -- Step 1: g^p = 1 since |Multiplicative (ZMod p)| = p
  have hgp : g ^ p = 1 := by
    have h := pow_card_eq_one (x := g)
    rwa [Fintype.card_multiplicative, ZMod.card] at h
  -- Step 2: ρ(g)^p = id
  have hρp : (ρ g) ^ p = 1 := by
    rw [← map_pow, hgp, map_one]
  -- Step 3: (ρ(g) - 1)^p = 0 by freshman's dream in char p
  have hnil : (ρ g - 1) ^ p = 0 := by
    haveI : Nontrivial V := IsSimpleModule.nontrivial k (M := V)
    haveI : CharP (Module.End k V) p :=
      charP_of_injective_algebraMap' k p
    rw [sub_pow_char_of_commute p (Commute.one_right _)]
    rw [one_pow, hρp, sub_self]
  -- Step 4: ρ(g) - 1 is nilpotent
  have hIsNil : IsNilpotent (ρ g - 1) := ⟨p, hnil⟩
  -- Step 5: nilpotent endomorphism on simple module must be zero
  -- By Schur: ker(ρ g - 1) is either ⊥ or ⊤. If ⊥, the map is injective hence
  -- bijective (finite-dim), contradicting nilpotency. So ker = ⊤, meaning ρ g - 1 = 0.
  haveI : Nontrivial V := IsSimpleModule.nontrivial k (M := V)
  have hzero : ρ g - 1 = 0 := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker (ρ g - 1)) with hbot | htop
    · -- ker = ⊥ means injective. f^p is also injective (iterate).
      -- But f^p = 0 has ker = ⊤, contradiction.
      exfalso
      have hinj := LinearMap.ker_eq_bot.mp hbot
      have hinj_iter : Function.Injective (⇑(ρ g - 1))^[p] := hinj.iterate p
      rw [← Module.End.coe_pow] at hinj_iter
      rw [hnil] at hinj_iter
      -- hinj_iter : Function.Injective ⇑(0 : Module.End k V)
      obtain ⟨a, b, hab⟩ := exists_pair_ne V
      exact hab (hinj_iter (by simp))
    · exact LinearMap.ker_eq_top.mp htop
  -- ρ g - 1 = 0 implies ρ g = 1 = LinearMap.id
  rwa [sub_eq_zero] at hzero

