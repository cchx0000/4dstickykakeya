import Theorems.Thm_StickyKakeya4_native_retained_slice_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRetainedGrainDensityTransfer
open Classical Finset SelfUniform NativeJointUniformCoarseRelations
open NativeFiniteSliceHomogeneity
open scoped BigOperators

/-- The original parent-specific grain lower controls its own occupied
grain count. No global mixed-label count is substituted. -/
theorem original_grain_count_cross {A Y : Type*} [DecidableEq Y]
    (H : Finset A) (grain : A → Y) (t : ℝ)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ)) :
    t*(H.image grain).card ≤ (H.card:ℝ) := by
  have hsum : (H.card:ℝ)=∑g∈H.image grain,((H.filter (fun z => grain z=g)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image grain H
  calc
    _ = ∑_g∈H.image grain,t := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := (sum_le_sum hgrain).trans_eq hsum.symm

/-- Retained original incidence mass and the new old-grain degree
comparison reconstruct density in EVERY surviving old grain. -/
theorem retained_grain_density {A Y : Type*} [DecidableEq A] [DecidableEq Y]
    (H T : Finset A) (hTH : T⊆H) (grain : A → Y) (Q : ℕ)
    (HU : HasUniformFibers T Q grain) (t C : ℝ) (hC : 0 ≤ C)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (hret : (H.card:ℝ) ≤ C*T.card) (g : Y) (hg : g∈T.image grain) :
    t ≤ C*(Q:ℝ)^2*(T.filter (fun z => grain z=g)).card := by
  have havg := (fiber_card_average_cross T grain (Q^2) HU g hg).2
  have hlabels : (T.image grain).card ≤ (H.image grain).card :=
    card_le_card (image_subset_image hTH)
  have hmass : (T.card:ℝ) ≤ (Q:ℝ)^2*(T.filter (fun z => grain z=g)).card*(H.image grain).card := by
    have hh := havg.trans (Nat.mul_le_mul_left _ hlabels)
    exact_mod_cast hh
  have hGn : (0:ℝ)<(H.image grain).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨g,image_subset_image hTH hg⟩)
  apply (mul_le_mul_iff_left₀ hGn).mp
  calc
    _ ≤ (H.card:ℝ) := original_grain_count_cross H grain t hgrain
    _ ≤ C*T.card := hret
    _ ≤ C*((Q:ℝ)^2*(T.filter (fun z => grain z=g)).card*(H.image grain).card) :=
      mul_le_mul_of_nonneg_left hmass hC
    _ = _ := by ring

/-- The quotient selection and third refinement pay their exact two
retention factors; the original threshold t remains parent-specific. -/
theorem retained_grain_density_two_stage {A Y : Type*} [DecidableEq A] [DecidableEq Y]
    (H S T : Finset A) (hSH : S⊆H) (hTS : T⊆S) (grain : A → Y) (Q : ℕ)
    (HU : HasUniformFibers T Q grain) (t Cq F : ℝ) (hCq : 0 ≤ Cq) (hF : 0 ≤ F)
    (hgrain : ∀g∈H.image grain,t ≤ ((H.filter (fun z => grain z=g)).card:ℝ))
    (hquotient : (H.card:ℝ) ≤ Cq*S.card) (hrefine : (S.card:ℝ) ≤ F*T.card)
    (g : Y) (hg : g∈T.image grain) :
    t ≤ Cq*F*(Q:ℝ)^2*(T.filter (fun z => grain z=g)).card := by
  apply retained_grain_density H T (hTS.trans hSH) grain Q HU t (Cq*F)
    (mul_nonneg hCq hF) hgrain _ g hg
  exact hquotient.trans ((mul_le_mul_of_nonneg_left hrefine hCq).trans_eq (by ring))

/-- Decode a grain equality relation already included in the SAME retained
slice core. This theorem selects no additional set. -/
theorem extra_relation_grain_uniformity {A Y : Type*} [DecidableEq A] [DecidableEq Y]
    {d : ℕ} (T : Finset A) (Q : ℕ) (grain : A → Y)
    (Rel : Fin d → A → A → Prop) (j : Fin d)
    (hRel : ∀x y,Rel j x y ↔ grain x=grain y)
    (HU : ∀x y,x∈T → y∈T → degree (fun _ : A => 1) (Rel j) T x ≤
      Q^2*degree (fun _ : A => 1) (Rel j) T y) :
    HasUniformFibers T Q grain := by
  have he : Rel j=(fun x y => grain x=grain y) := by
    funext x y
    exact propext (hRel x y)
  intro x hx y hy
  simpa only [he,unit_degree_eq_fiber] using HU x y hx hy

end NativeRetainedGrainDensityTransfer
