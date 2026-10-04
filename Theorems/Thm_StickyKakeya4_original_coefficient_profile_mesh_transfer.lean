import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalCoefficientProfileMeshTransfer
open Classical GKZOriginalGapEnergy

/-- A literal injective coefficient map inherits the original interval
profile down to a specified new mesh. The enlargement pays BOTH inverse
geometry and the original minimum test radius. -/
theorem original_inverse_profile_at_finer_mesh (C : Finset ℝ) (f : ℝ → ℝ)
    (delta sigma K u L B : ℝ) (_hd : 0 < delta) (hs : 0 < sigma)
    (hK : 1 ≤ K) (hu : 0 ≤ u) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgeom : 2*L ≤ B) (hmesh : delta ≤ B*sigma)
    (hinj : Set.InjOn f C)
    (hinverse : ∀ c∈C,∀ d∈C,|c-d| ≤ L*|f c-f d|)
    (hprofile : ScalarFrostman C delta K u) :
    ScalarFrostman (C.image f) sigma (K*B^u) u := by
  intro z r hr _hr1
  let E := C.filter (fun c => |f c-z| ≤ r)
  have heq : (C.image f).filter (fun x => |x-z| ≤ r)=E.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC,hxr⟩ := Finset.mem_filter.mp hx
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hxC
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hxr⟩,rfl⟩
    · intro hx
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
  rw [heq,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),Finset.card_image_of_injOn hinj]
  have hr0 : 0 ≤ r := hs.le.trans hr
  have hBr : delta ≤ B*r := hmesh.trans (mul_le_mul_of_nonneg_left hr hB)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  change (E.card : ℝ) ≤ K*B^u*r^u*C.card
  by_cases hE : E.Nonempty
  · obtain ⟨c0,hc0⟩ := hE
    have hc0C := (Finset.mem_filter.mp hc0).1
    have hc0z := (Finset.mem_filter.mp hc0).2
    have hsub : E⊆C.filter (fun c => |c-c0| ≤ B*r) := by
      intro c hc
      obtain ⟨hcC,hcz⟩ := Finset.mem_filter.mp hc
      refine Finset.mem_filter.mpr ⟨hcC,?_⟩
      have hdiff : |f c-f c0| ≤ 2*r := by
        have hx := abs_sub (f c-z) (f c0-z)
        rw [show (f c-z)-(f c0-z)=f c-f c0 by ring] at hx
        linarith only [hx,hcz,hc0z]
      have h1 := mul_le_mul_of_nonneg_left hdiff hL
      have h2 := mul_le_mul_of_nonneg_right hgeom hr0
      have hi := hinverse c hcC c0 hc0C
      nlinarith only [hi,h1,h2]
    by_cases hB1 : B*r ≤ 1
    · have hn := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hprofile c0 (B*r) hBr hB1)
      rw [Real.mul_rpow hB hr0] at hn
      simpa only [mul_assoc] using hn
    · have hp : 1 ≤ (B*r)^u := Real.one_le_rpow (le_of_not_ge hB1) hu
      have hcoef : 1 ≤ K*(B*r)^u := by nlinarith only [hK,hp]
      have hn : (E.card : ℝ) ≤ C.card := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hm := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg C.card)
      rw [one_mul,Real.mul_rpow hB hr0] at hm
      exact hn.trans (by simpa only [mul_assoc] using hm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE,Finset.card_empty,Nat.cast_zero]
    positivity

end OriginalCoefficientProfileMeshTransfer
