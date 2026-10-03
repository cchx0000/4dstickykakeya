import Theorems.Thm_StickyKakeya4_rich_witness_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace RichWitnessRealCore

open RichWitnessCore

variable {Ω ν : Type*} [DecidableEq ν]

/-- A REAL finite potential constructs the exact real-threshold core. No floor,
large-degree premise, or assumed count symmetry is used. All witnesses remain
original labels, and incoming/outgoing equality is the proved swap bijection. -/
theorem exists_rich_core (W : Finset Ω) (V : Finset ν) (left right : Ω → ν)
    (swap : Ω → Ω) (hswap : Function.Involutive swap)
    (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (hV : ∀ w ∈ W, left w ∈ V ∧ right w ∈ V)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ S ⊆ V,
      (∀ v ∈ S, q ≤ ((outgoing (retained W left right S) left v).card : ℝ)) ∧
      (W.card : ℝ) + 2 * q * (S.card : ℝ) ≤
        ((retained W left right S).card : ℝ) + 2 * q * (V.card : ℝ) ∧
      (W.card : ℝ) ≤ ((retained W left right S).card : ℝ) + 2 * q * (V.card : ℝ) ∧
      (W.card : ℝ) - 2 * q * (V.card : ℝ) ≤ ((retained W left right S).card : ℝ) := by
  classical
  let potential : Finset ν → ℝ := fun S =>
    ((retained W left right S).card : ℝ) - 2 * q * (S.card : ℝ)
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image V.powerset potential ⟨∅, by simp⟩
  have hSV : S ⊆ V := Finset.mem_powerset.mp hS
  have hdegree : ∀ v ∈ S, q ≤ ((outgoing (retained W left right S) left v).card : ℝ) := by
    intro v hv
    have herase := hmax (S.erase v)
      (Finset.mem_powerset.mpr ((Finset.erase_subset v S).trans hSV))
    have hcard : ((S.erase v).card : ℝ) + 1 = (S.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hv
    have hloss := erase_vertex_loss W left right S v
    rw [← outgoing_card_eq_incoming W left right swap hswap hW hends S v] at hloss
    have hlossR : ((retained W left right S).card : ℝ) ≤
        ((retained W left right (S.erase v)).card : ℝ) +
          2 * ((outgoing (retained W left right S) left v).card : ℝ) := by
      exact_mod_cast (show (retained W left right S).card ≤
        (retained W left right (S.erase v)).card +
          2 * (outgoing (retained W left right S) left v).card by omega)
    dsimp [potential] at herase
    nlinarith
  have hmaxV := hmax V (by simp)
  dsimp [potential] at hmaxV
  rw [retained_eq_of_endpoints W left right V hV] at hmaxV
  have hstrong : (W.card : ℝ) + 2 * q * (S.card : ℝ) ≤
      ((retained W left right S).card : ℝ) + 2 * q * (V.card : ℝ) := by linarith
  have hterm : 0 ≤ 2 * q * (S.card : ℝ) := by positivity
  have hret : (W.card : ℝ) ≤
      ((retained W left right S).card : ℝ) + 2 * q * (V.card : ℝ) := by linarith
  exact ⟨S, hSV, hdegree, hstrong, hret, by linarith⟩

/-- The exact real budget gives a nonempty core and at least half the original
ordered witnesses, including when the real threshold is below one. -/
theorem exists_half_mass_rich_core (W : Finset Ω) (V : Finset ν) (left right : Ω → ν)
    (swap : Ω → Ω) (hswap : Function.Involutive swap)
    (hW : ∀ w ∈ W, swap w ∈ W)
    (hends : ∀ w ∈ W, left (swap w) = right w ∧ right (swap w) = left w)
    (hV : ∀ w ∈ W, left w ∈ V ∧ right w ∈ V)
    (q : ℝ) (hq : 0 ≤ q)
    (hbudget : 4 * q * (V.card : ℝ) ≤ (W.card : ℝ)) (hpositive : 0 < W.card) :
    ∃ S ⊆ V, S.Nonempty ∧ (retained W left right S).Nonempty ∧
      (∀ v ∈ S, q ≤ ((outgoing (retained W left right S) left v).card : ℝ)) ∧
      (W.card : ℝ) + 2 * q * (S.card : ℝ) ≤
        ((retained W left right S).card : ℝ) + 2 * q * (V.card : ℝ) ∧
      (W.card : ℝ) ≤ 2 * ((retained W left right S).card : ℝ) ∧
      (W.card : ℝ) - 2 * q * (V.card : ℝ) ≤ ((retained W left right S).card : ℝ) := by
  obtain ⟨S, hSV, hdegree, hstrong, hret, hsub⟩ :=
    exists_rich_core W V left right swap hswap hW hends hV q hq
  have hhalf : (W.card : ℝ) ≤ 2 * ((retained W left right S).card : ℝ) := by linarith
  have hWpos : (0 : ℝ) < W.card := Nat.cast_pos.mpr hpositive
  have hposR : (0 : ℝ) < (retained W left right S).card := by linarith
  have hpos : 0 < (retained W left right S).card := Nat.cast_pos.mp hposR
  have hne : (retained W left right S).Nonempty := Finset.card_pos.mp hpos
  have hS : S.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨left w, (Finset.mem_filter.mp hw).2.1⟩
  exact ⟨S, hSV, hS, hne, hdegree, hstrong, hhalf, hsub⟩

/-- The Section 19 ordered-collision specialization uses actual pair exchange,
so the exact real threshold requires no caller-supplied symmetry certificate. -/
theorem exists_half_mass_collision_core {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (label : α → β) (endpoint : α → ν) (V : Finset ν)
    (hV : ∀ a ∈ A, endpoint a ∈ V) (q : ℝ) (hq : 0 ≤ q)
    (hbudget : 4 * q * (V.card : ℝ) ≤
      ((TwoTubePathCollisionCount.collisions A label).card : ℝ))
    (hpositive : 0 < (TwoTubePathCollisionCount.collisions A label).card) :
    ∃ S ⊆ V, S.Nonempty ∧
      (retained (TwoTubePathCollisionCount.collisions A label)
        (fun w => endpoint w.1) (fun w => endpoint w.2) S).Nonempty ∧
      (∀ v ∈ S, q ≤ ((outgoing
        (retained (TwoTubePathCollisionCount.collisions A label)
          (fun w => endpoint w.1) (fun w => endpoint w.2) S)
        (fun w => endpoint w.1) v).card : ℝ)) ∧
      ((TwoTubePathCollisionCount.collisions A label).card : ℝ) ≤
        2 * ((retained (TwoTubePathCollisionCount.collisions A label)
          (fun w => endpoint w.1) (fun w => endpoint w.2) S).card : ℝ) := by
  obtain ⟨S, hSV, hS, hWS, hdeg, _, hmass, _⟩ := exists_half_mass_rich_core
    (TwoTubePathCollisionCount.collisions A label) V
    (fun w => endpoint w.1) (fun w => endpoint w.2) Prod.swap
    (fun w => Prod.swap_swap w) (fun _ hw => collision_swap_mem A label hw)
    (fun _ _ => ⟨rfl, rfl⟩) (by
      intro w hw
      obtain ⟨hl, hr, _⟩ := (TwoTubePathCollisionCount.mem_collisions A label w).mp hw
      exact ⟨hV w.1 hl, hV w.2 hr⟩) q hq hbudget hpositive
  exact ⟨S, hSV, hS, hWS, hdeg, hmass⟩

end RichWitnessRealCore
