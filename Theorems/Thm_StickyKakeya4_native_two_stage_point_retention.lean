import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeTwoStagePointRetention
open Classical Finset NativeJointUniformCoarseRelations NativeCoarseUniformImageDegrees
open scoped BigOperators

/-- Global original-incidence retention and the two actual point-uniformity
relations imply a quantitative retention bound at EVERY surviving point.
The source support is only restricted; no conditional measure is normalized. -/
theorem point_retention_of_two_uniformities {T X : Type*} [DecidableEq T] [DecidableEq X]
    (I E : Finset (T × X)) (hEI : E ⊆ I) (Qref Qnew : ℕ)
    (HI : HasUniformFibers I Qref Prod.snd) (HE : HasUniformFibers E Qnew Prod.snd)
    (lambda G : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G)
    (hret : lambda*(I.card:ℝ) ≤ G*E.card)
    (z : T × X) (hz : z∈E) :
    lambda*((I.filter (fun a => a.2=z.2)).card:ℝ) ≤
      G*(Qref:ℝ)^2*(Qnew:ℝ)^2*((E.filter (fun a => a.2=z.2)).card:ℝ) := by
  have hIne : I.Nonempty := ⟨z,hEI hz⟩
  have hs : (0:ℝ) < (I.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hIne.image Prod.snd)
  have hOld := point_fiber_card_cross I (fun a => a) (Qref^2) HI z.2
  simp only [image_id'] at hOld
  have hOldR : ((I.filter (fun a => a.2=z.2)).card:ℝ)*(I.image Prod.snd).card ≤
      (Qref:ℝ)^2*I.card := by exact_mod_cast hOld
  have hNew : E.card ≤ Qnew^2*(I.image Prod.snd).card*(E.filter (fun a => a.2=z.2)).card := by
    calc
      _ = ∑x∈E.image Prod.snd,(E.filter (fun a => a.2=x)).card := card_eq_sum_card_image Prod.snd E
      _ ≤ ∑_x∈E.image Prod.snd,Qnew^2*(E.filter (fun a => a.2=z.2)).card := by
        apply sum_le_sum
        intro x hx
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
        exact HE a ha z hz
      _ = Qnew^2*(E.image Prod.snd).card*(E.filter (fun a => a.2=z.2)).card := by simp; ring
      _ ≤ Qnew^2*(I.image Prod.snd).card*(E.filter (fun a => a.2=z.2)).card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (card_le_card (image_subset_image hEI)))
  have hNewR : (E.card:ℝ) ≤
      (Qnew:ℝ)^2*(I.image Prod.snd).card*(E.filter (fun a => a.2=z.2)).card := by exact_mod_cast hNew
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = lambda*(((I.filter (fun a => a.2=z.2)).card:ℝ)*(I.image Prod.snd).card) := by ring
    _ ≤ lambda*((Qref:ℝ)^2*I.card) := mul_le_mul_of_nonneg_left hOldR hlambda
    _ = (Qref:ℝ)^2*(lambda*(I.card:ℝ)) := by ring
    _ ≤ (Qref:ℝ)^2*(G*E.card) := mul_le_mul_of_nonneg_left hret (sq_nonneg _)
    _ = ((Qref:ℝ)^2*G)*(E.card:ℝ) := by ring
    _ ≤ ((Qref:ℝ)^2*G)*((Qnew:ℝ)^2*(I.image Prod.snd).card*(E.filter (fun a => a.2=z.2)).card) :=
      mul_le_mul_of_nonneg_left hNewR (mul_nonneg (sq_nonneg _) hG)
    _ = _ := by ring

end NativeTwoStagePointRetention
