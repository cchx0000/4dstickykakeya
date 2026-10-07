import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFinitePointCoherence
open Classical Finset SelfUniform CompatibleTupleSelection
open scoped BigOperators

/-- The fixed Fin K menu acts on ORIGINAL points with their unchanged
weights. No relation between K and a source-dependent depth is introduced. -/
theorem weighted_finite_selection {X C B : Type*} [DecidableEq X] [DecidableEq C] [DecidableEq B]
    (weight : X → ℕ) : ∀K : ℕ,∀A : Finset X,
    ∀cell : Fin K → X → C,∀offset : Fin K → X → B,∀cost : Fin K → ℕ,
    (∀j c,((A.filter (fun x => cell j x=c)).image (offset j)).card ≤ cost j) →
    ∃P⊆A,mass weight A ≤ (∏j,cost j)*mass weight P ∧
      ∀j x y,x∈P → y∈P → cell j x=cell j y → offset j x=offset j y := by
  intro K
  induction K with
  | zero =>
    intro A cell offset cost _hcap
    refine ⟨A,Subset.refl _,?_,?_⟩
    · simp
    · intro j
      exact Fin.elim0 j
  | succ K ih =>
    intro A cell offset cost hcap
    obtain ⟨P1,hP1,hMass1,hCompat1⟩ := weighted_spatial_selection weight A (cell 0) (offset 0) (cost 0) (hcap 0)
    have htail (j : Fin K) (c : C) :
        ((P1.filter (fun x => cell j.succ x=c)).image (offset j.succ)).card ≤ cost j.succ :=
      (card_le_card (image_subset_image (filter_subset_filter _ hP1))).trans (hcap j.succ c)
    obtain ⟨P,hPP1,hMass,hCompat⟩ := ih P1 (fun j => cell j.succ) (fun j => offset j.succ)
      (fun j => cost j.succ) htail
    refine ⟨P,hPP1.trans hP1,?_,?_⟩
    · calc
        _ ≤ cost 0*mass weight P1 := hMass1
        _ ≤ cost 0*((∏j : Fin K,cost j.succ)*mass weight P) := Nat.mul_le_mul_left _ hMass
        _ = _ := by rw [Fin.prod_univ_succ]; ring
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro x y hx hy hxy
        exact hCompat1 x y (hPP1 hx) (hPP1 hy) hxy
      · exact hCompat k

def pointWeight {A X : Type*} [DecidableEq X] (S : Finset A) (point : A → X) (x : X) : ℕ :=
  (S.filter (fun z => point z=x)).card

def lift {A X : Type*} [DecidableEq X] (S : Finset A) (point : A → X) (P : Finset X) : Finset A :=
  S.filter (fun z => point z∈P)

lemma lift_fiber {A X : Type*} [DecidableEq A] [DecidableEq X]
    (S : Finset A) (point : A → X) (P : Finset X) (x : X) (hx : x∈P) :
    (lift S point P).filter (fun z => point z=x)=S.filter (fun z => point z=x) := by
  ext z
  simp only [lift,mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2.symm ▸ hx⟩,h.2⟩

lemma lift_card {A X : Type*} [DecidableEq A] [DecidableEq X]
    (S : Finset A) (point : A → X) (P : Finset X) :
    (lift S point P).card=mass (pointWeight S point) P := by
  have hcard := card_eq_sum_card_fiberwise (f:=point) (s:=lift S point P) (t:=P)
    (fun z hz => (mem_filter.mp hz).2)
  rw [hcard]
  unfold mass pointWeight
  apply sum_congr rfl
  intro x hx
  rw [lift_fiber S point P x hx]

lemma support_mass {A X : Type*} [DecidableEq X] (S : Finset A) (point : A → X) :
    mass (pointWeight S point) (S.image point)=S.card := (card_eq_sum_card_image point S).symm

lemma cell_offset_image {A X C B : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq C] [DecidableEq B]
    (S : Finset A) (point : A → X) (cell : X → C) (offset : X → B) (c : C) :
    (((S.image point).filter (fun x => cell x=c)).image offset)=
      ((S.filter (fun z => cell (point z)=c)).image (fun z => offset (point z))) := by
  ext b
  simp only [mem_image,mem_filter]
  constructor
  · rintro ⟨x,⟨⟨z,hz,rfl⟩,hc⟩,hb⟩
    exact ⟨z,⟨hz,hc⟩,hb⟩
  · rintro ⟨z,⟨hz,hc⟩,hb⟩
    exact ⟨point z,⟨⟨z,hz,rfl⟩,hc⟩,hb⟩

/-- The selected original points are lifted to ALL their original source
incidences. Exact fiber equality preserves every actual angular menu. -/
theorem select_original_point_fibers {A X C B : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq C] [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (point : A → X) (K : ℕ)
    (cell : Fin K → X → C) (offset : Fin K → X → B) (cost : Fin K → ℝ)
    (hcap : ∀j c,(((S.filter (fun z => cell j (point z)=c)).image
      (fun z => offset j (point z))).card:ℝ) ≤ cost j) :
    ∃P⊆S.image point,let T := lift S point P
      T.Nonempty ∧ S.card ≤ (∏j,⌈cost j⌉₊)*T.card ∧
      (∀j z w,z∈T → w∈T → cell j (point z)=cell j (point w) → offset j (point z)=offset j (point w)) ∧
      (∀x∈P,T.filter (fun z => point z=x)=S.filter (fun z => point z=x)) := by
  have hpointcap (j : Fin K) (c : C) :
      ((((S.image point).filter (fun x => cell j x=c)).image (offset j)).card:ℕ) ≤ ⌈cost j⌉₊ := by
    rw [cell_offset_image]
    exact_mod_cast (hcap j c).trans (Nat.le_ceil (cost j))
  obtain ⟨P,hP,hMass,hCompat⟩ := weighted_finite_selection (pointWeight S point) K (S.image point)
    cell offset (fun j => ⌈cost j⌉₊) hpointcap
  rw [support_mass,←lift_card] at hMass
  refine ⟨P,hP,?_,hMass,?_,fun x hx => lift_fiber S point P x hx⟩
  · by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,card_empty,mul_zero] at hMass
    have hp := card_pos.mpr hS
    omega
  · intro j z w hz hw hzw
    exact hCompat j (point z) (point w) (mem_filter.mp hz).2 (mem_filter.mp hw).2 hzw

end NativeFinitePointCoherence
