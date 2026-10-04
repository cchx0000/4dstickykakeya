import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped BigOperators
noncomputable section

namespace OriginalBinLabelLift
open DyadicOriginalFiberSelection

def originalLift {P Q : Type*} [DecidableEq Q]
    (W : Finset P) (f : P → Q) (T : Finset Q) : Finset P :=
  W.filter (fun p => f p∈T)

/-- Lift selected bin labels to ALL matching ORIGINAL points, and retain the
actual relative mass with at most the dyadic factor two. -/
theorem original_bin_lift
    {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (W : Finset P) (f : P → Q) (j : ℕ) (T : Finset Q)
    (hT : T⊆(bin W f j).image f) :
    originalLift W f T⊆bin W f j ∧
    (originalLift W f T).image f=T ∧
    (bin W f j).card*T.card≤2*((bin W f j).image f).card*(originalLift W f T).card := by
  have hsub : originalLift W f T⊆bin W f j := by
    intro p hp
    obtain ⟨hpW,hpf⟩ := Finset.mem_filter.mp hp
    obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp (hT hpf)
    exact bin_saturated W f j hw hpW heq.symm
  have him : (originalLift W f T).image f=T := by
    ext s
    constructor
    · intro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      exact (Finset.mem_filter.mp hp).2
    · intro hs
      obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp (hT hs)
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1,heq.symm ▸ hs⟩,heq⟩
  have hsum : (∑ s∈T,(fiber W f s).card)=(originalLift W f T).card := by
    unfold fiber originalLift
    exact Finset.sum_card_fiberwise_eq_card_filter W T f
  have hlower : 2^j*T.card≤(originalLift W f T).card := by
    rw [← hsum]
    have hpoint (s : Q) (hs : s∈T) : 2^j≤(fiber W f s).card := by
      have h := (bin_fiber_bounds W f j (hT hs)).1
      rwa [fiber_bin_eq W f j (hT hs)] at h
    have hh := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm] using hh
  have hupper : (bin W f j).card≤2*((bin W f j).image f).card*2^j := by
    rw [← fiber_sum (bin W f j) f]
    have hh := Finset.sum_le_sum (fun s (hs : s∈(bin W f j).image f) => (bin_fiber_bounds W f j hs).2.le)
    simpa only [Finset.sum_const,Nat.nsmul_eq_mul,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh
  have h1 := Nat.mul_le_mul_right T.card hupper
  have h2 := Nat.mul_le_mul_left (2*((bin W f j).image f).card) hlower
  exact ⟨hsub,him,by nlinarith only [h1,h2]⟩

/-- Relative cardinal retention in the selected label set returns to the
original pair graph, rather than retaining just one representative per label. -/
theorem original_bin_lift_density
    {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (W : Finset P) (f : P → Q) (j : ℕ) (T : Finset Q)
    (hbin : (bin W f j).Nonempty) (hT : T⊆(bin W f j).image f)
    (alpha : ℝ) (hret : alpha*(((bin W f j).image f).card : ℝ)≤T.card) :
    alpha*((bin W f j).card : ℝ)≤2*(originalLift W f T).card := by
  have hpos : (0:ℝ)<((bin W f j).image f).card := by exact_mod_cast (hbin.image f).card_pos
  have hcross : ((bin W f j).card : ℝ)*T.card≤
      2*(((bin W f j).image f).card : ℝ)*(originalLift W f T).card := by
    exact_mod_cast (original_bin_lift W f j T hT).2.2
  have hlow := mul_le_mul_of_nonneg_left hret (Nat.cast_nonneg (bin W f j).card)
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith only [hlow.trans hcross]

end OriginalBinLabelLift
