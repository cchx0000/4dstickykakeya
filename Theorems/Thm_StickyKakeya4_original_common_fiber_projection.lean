import Theorems.Thm_StickyKakeya4_original_scalar_line_cover
import Theorems.Thm_StickyKakeya4_original_line_collision_collapse
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Finset
open scoped Pointwise
noncomputable section
open Classical
namespace OriginalCommonFiberProjection
open OriginalScalarLineCover OriginalScalarCollisionCounts OriginalLineCollisionCollapse
open OriginalScalarCollisionGeometry OriginalCommonScalarFibers VectorGraphCollisionEnergy
open PlanarShiftedNearEnergy TwoTubePathCollisionCount
abbrev Point := ℝ × ℝ
abbrev PairLabel := Point × ℝ

/-- Literal separated ordered A pairs with the directional relation forced
by an original scalar-line collision. -/
def projectedPairs (A : Finset Point) (v : Point) (eta s : ℝ) : Finset (Point × Point) :=
  (A ×ˢ A).filter (fun aa => s ≤ ‖aa.1-aa.2‖ ∧ |det v (aa.1-aa.2)| ≤ 2*eta*‖v‖)

/-- Remove close original scalar pairs, then collapse the retained ORIGINAL
collisions to separated original A pairs using scalar separation. -/
theorem original_line_projected_pairs (A : Finset Point) (C D : Finset ℝ) (v : Point)
    {eta delta d t s nu chi : ℝ} (heta : 0 < eta) (hdelta : 0 < delta)
    (hd : 0 < d) (ht : 0 ≤ t) (_hnu : 0 < nu) (hchi : 0 ≤ chi)
    (hC : C.Nonempty) (hDC : D ⊆ C) (hv : d ≤ ‖v‖) (hscale : s+eta ≤ d*t)
    (hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → eta ≤ ‖a-a'‖)
    (hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|)
    (hCcap : ∀ c ∈ C, ((C.filter (fun c' => |c'-c| ≤ t)).card : ℝ) ≤ chi*C.card)
    (hbudget : 32*chi ≤ nu)
    (henergy : nu*A.card*(C.card : ℝ)^2 ≤ (lineCollisions A D v eta).card) :
    (nu/(2*(2*((eta/d)/delta)+2)))*A.card*C.card ≤ (projectedPairs A v eta s).card := by
  let E := lineCollisions A D v eta
  let Bad := closeScalarCollisions A D v eta t
  let Good := E \ Bad
  let M := 2*((eta/d)/delta)+2
  have hM : 0 < M := by dsimp [M]; positivity
  have hCc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hBad : Bad ⊆ E := Finset.filter_subset _ _
  have hGood : Good ⊆ lineCollisions A D v eta := Finset.sdiff_subset
  have hb := close_scalar_collision_card A C D v heta hchi hDC hAsep hCcap
  have hsum : (Good.card : ℝ)+Bad.card=E.card := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_sdiff_add_card_eq_card hBad)
  have hbud := mul_le_mul_of_nonneg_right hbudget
    (show 0 ≤ (A.card : ℝ)*(C.card : ℝ)^2 by positivity)
  have hGoodMass : (nu/2)*A.card*(C.card : ℝ)^2 ≤ Good.card := by
    nlinarith only [henergy,hb,hsum,hbud]
  have hcollapse := original_A_pair_collision_bound A C D v heta hdelta hd hv hDC hCsep Good hGood
  have him : Good.image (fun e => (e.1.1,e.2.1)) ⊆ projectedPairs A v eta s := by
    intro aa haa
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp haa
    obtain ⟨heE,heBad⟩ := Finset.mem_sdiff.mp he
    obtain ⟨he1,he2,hgrid⟩ := (mem_collisions _ _ _).mp heE
    have hct : t ≤ |e.1.2-e.2.2| := by
      apply le_of_lt
      exact lt_of_not_ge (fun h => heBad (Finset.mem_filter.mpr ⟨heE,h⟩))
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp he1).1,(Finset.mem_product.mp he2).1⟩,?_,?_⟩
    · exact original_collision_separation heta hd.le ht hv hct hscale hgrid
    · exact original_collision_det heta hgrid
  have hcount : ((Good.image (fun e => (e.1.1,e.2.1))).card : ℝ) ≤
      (projectedPairs A v eta s).card := Nat.cast_le.mpr (Finset.card_le_card him)
  have hupper := hcollapse.trans (mul_le_mul_of_nonneg_left hcount
    (show 0 ≤ M*(C.card : ℝ) by positivity))
  apply (mul_le_mul_iff_left₀ (show 0 < M*(C.card : ℝ) by positivity)).mp
  have hid : (M*(C.card : ℝ))*((nu/(2*M))*A.card*C.card) =
      (nu/2)*A.card*(C.card : ℝ)^2 := by field_simp
  change (nu/(2*M))*A.card*C.card*(M*C.card) ≤
    (projectedPairs A v eta s).card*(M*C.card)
  calc
    _ = (M*(C.card : ℝ))*((nu/(2*M))*A.card*C.card) := by ring
    _ = (nu/2)*A.card*(C.card : ℝ)^2 := hid
    _ ≤ _ := by
      simpa only [M,mul_comm,mul_left_comm,mul_assoc] using hGoodMass.trans hupper

/-- Exact source form of the p91 projected-A-pair lower bound. The energy is
constructed from Eq169 and the actual common-C fiber, not assumed here. -/
theorem common_fiber_projected_pairs (A : Finset Point) (C : Finset ℝ)
    (F : Finset (Point × ℝ)) (b b' : Point)
    {eta delta d t s r Q N q chi : ℝ} (heta : 0 < eta) (hdelta : 0 < delta)
    (hd : 0 < d) (ht : 0 ≤ t) (hr : 0 < r) (hQ : 0 < Q) (hq : 0 < q) (hchi : 0 ≤ chi)
    (hA : A.Nonempty) (hC : C.Nonempty) (hv : d ≤ ‖b-b'‖) (hscale : s+eta ≤ d*t)
    (hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → eta ≤ ‖a-a'‖)
    (hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|)
    (hCcap : ∀ c ∈ C, ((C.filter (fun c' => |c'-c| ≤ t)).card : ℝ) ≤ chi*C.card)
    (hret : r*N ≤ A.card) (hcommon : q*C.card ≤ (commonFiber F C b b').card)
    (hcover : (((A+F.image productValue-F.image productValue).image (roundPoint eta)).card : ℝ) ≤ Q*N)
    (hbudget : 32*chi ≤ r*q^2/Q) :
    ((r*q^2/Q)/(2*(2*((eta/d)/delta)+2)))*A.card*C.card ≤
      (projectedPairs A (b-b') eta s).card := by
  have he := common_line_collision_energy A C F b b' hA hr hQ hq.le hret hcommon hcover
  exact original_line_projected_pairs A C (commonFiber F C b b') (b-b') heta hdelta hd ht
    (by positivity) hchi hC (commonFiber_subset F C b b') hv hscale hAsep hCsep hCcap hbudget he
end OriginalCommonFiberProjection
