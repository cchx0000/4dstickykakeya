import Theorems.Thm_StickyKakeya4_native_point_menu_transfer
import Theorems.Thm_StickyKakeya4_native_coarse_uniform_image_degrees
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeBoundedParentPointTransfer
open Classical Finset NativeIncidenceMultiplicityTower
open scoped BigOperators

/-- Finite point-degree transfer for two images of the SAME original E.
The parent map need not agree: at most K old parents lie over one new parent.
Only a forward point menu is required. -/
theorem image_point_degree_le {A P X Q Y : Type*}
    [DecidableEq A] [DecidableEq P] [DecidableEq X] [DecidableEq Q] [DecidableEq Y]
    (E : Finset A) (f : A → P × X) (g : A → Q × Y) (K H : ℕ) (M : ℝ)
    (hparent : ∀ q : Q, ((E.filter (fun a => (g a).1=q)).image (fun a => (f a).1)).card ≤ K)
    (hmenu : ∀ x : X, ((E.filter (fun a => (f a).2=x)).image (fun a => (g a).2)).card ≤ H)
    (hM : 0 ≤ M)
    (hdegree : ∀ y : Y, (((E.image g).filter (fun b => b.2=y)).card : ℝ) ≤ M)
    (x : X) :
    (((E.image f).filter (fun b => b.2=x)).card : ℝ) ≤ (K:ℝ)*(H:ℝ)*M := by
  let S := E.filter (fun a => (f a).2=x)
  have hcard : ((S.image f).card : ℝ) ≤ (K:ℝ)*(S.image g).card := by
    apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    intro b _hb
    have hc : ((S.filter (fun a => g a=b)).image f).card ≤
        ((E.filter (fun a => (g a).1=b.1)).image (fun a => (f a).1)).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro u hu
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
        obtain ⟨haS,hab⟩ := mem_filter.mp ha
        exact mem_image.mpr ⟨a,mem_filter.mpr ⟨(mem_filter.mp haS).1,by rw [hab]⟩,rfl⟩
      · intro u hu v hv he
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
        obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
        exact Prod.ext he (((mem_filter.mp (mem_filter.mp ha).1).2).trans
          ((mem_filter.mp (mem_filter.mp hb).1).2).symm)
    exact_mod_cast hc.trans (hparent b.1)
  have hs := NativePointMenuTransfer.subset_card_le_support_mul_degree
    (S.image g) (E.image g) (image_subset_image (filter_subset _ _)) M hdegree
  have hsupport : ((S.image g).image Prod.snd).card ≤ H := by
    simpa only [S,image_image,Function.comp_def] using hmenu x
  have hs' : ((S.image g).card : ℝ) ≤ (H:ℝ)*M :=
    hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsupport) hM)
  have himage : (E.image f).filter (fun b => b.2=x)=S.image f := by
    rw [filter_image]
  rw [himage]
  exact hcard.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg K))

/-- Average multiplicity follows from the old point-degree estimate. No
bounded inverse point menu or monotonicity under restriction is used. -/
theorem multiplicity_le_menu_mul_degree {A P X Q Y : Type*}
    [DecidableEq A] [DecidableEq P] [DecidableEq X] [DecidableEq Q] [DecidableEq Y]
    (E : Finset A) (f : A → P × X) (g : A → Q × Y) (K H : ℕ) (M : ℝ)
    (hparent : ∀ q : Q, ((E.filter (fun a => (g a).1=q)).image (fun a => (f a).1)).card ≤ K)
    (hmenu : ∀ x : X, ((E.filter (fun a => (f a).2=x)).image (fun a => (g a).2)).card ≤ H)
    (hM : 0 ≤ M)
    (hdegree : ∀ y : Y, (((E.image g).filter (fun b => b.2=y)).card : ℝ) ≤ M) :
    multiplicity (E.image f) ≤ (K:ℝ)*(H:ℝ)*M := by
  have hc := NativePointMenuTransfer.subset_card_le_support_mul_degree
    (E.image f) (E.image f) (Subset.refl _) ((K:ℝ)*(H:ℝ)*M)
    (image_point_degree_le E f g K H M hparent hmenu hM hdegree)
  by_cases hE : E.Nonempty
  · have hs : (0:ℝ) < ((E.image f).image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((hE.image f).image Prod.snd)
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_comm] using hc
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp only [NativeIncidenceMultiplicityTower.multiplicity,image_empty,card_empty,Nat.cast_zero,div_zero]
    positivity

/-- The relative image's original pair/point degree uniformity supplies its
maximum point degree. Both relations concern the same literal old E. -/
theorem uniform_images_multiplicity {A P X Q Y : Type*}
    [DecidableEq A] [DecidableEq P] [DecidableEq X] [DecidableEq Q] [DecidableEq Y]
    (E : Finset A) (f : A → P × X) (g : A → Q × Y) (K H rad : ℕ)
    (hparent : ∀ q : Q, ((E.filter (fun a => (g a).1=q)).image (fun a => (f a).1)).card ≤ K)
    (hmenu : ∀ x : X, ((E.filter (fun a => (f a).2=x)).image (fun a => (g a).2)).card ≤ H)
    (hpair : ∀ a∈E,∀ b∈E,(E.filter (fun z => g z=g a)).card ≤
      rad^2*(E.filter (fun z => g z=g b)).card)
    (hpoint : ∀ a∈E,∀ b∈E,(E.filter (fun z => (g z).2=(g a).2)).card ≤
      rad^2*(E.filter (fun z => (g z).2=(g b).2)).card) :
    multiplicity (E.image f) ≤ (K:ℝ)*(H:ℝ)*(rad:ℝ)^4*multiplicity (E.image g) := by
  have hM : 0 ≤ (rad:ℝ)^4*multiplicity (E.image g) := by
    unfold NativeIncidenceMultiplicityTower.multiplicity
    positivity
  have hh := multiplicity_le_menu_mul_degree E f g K H
    ((rad:ℝ)^4*multiplicity (E.image g)) hparent hmenu hM (by
      intro y
      have hc := NativeCoarseUniformImageDegrees.image_point_degree_le_multiplicity
        E g (rad^2) (rad^2) hpair hpoint y
      have he : (((rad^2:ℕ):ℝ)*((rad^2:ℕ):ℝ))=(rad:ℝ)^4 := by push_cast; ring
      simpa only [he] using hc)
  simpa only [mul_assoc] using hh

end NativeBoundedParentPointTransfer
