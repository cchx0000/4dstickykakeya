import Theorems.Thm_StickyKakeya4_original_scalar_affine_packing
import Theorems.Thm_StickyKakeya4_original_scalar_collision_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
open Finset
noncomputable section
open Classical
namespace OriginalLineCollisionCollapse
open OriginalScalarAffinePacking OriginalScalarCollisionCounts OriginalScalarCollisionGeometry
open OriginalSeparatedPacking PlanarShiftedNearEnergy TwoTubePathCollisionCount
abbrev Point := ℝ × ℝ
abbrev PairLabel := Point × ℝ

/-- Fixing both original A points and the first original scalar leaves only
an original scalar in a short affine preimage interval. -/
lemma fixed_points_scalar_fiber_card (A : Finset Point) (C D : Finset ℝ) (v : Point)
    {eta delta d : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) (hd : 0 < d)
    (hv : d ≤ ‖v‖) (hDC : D ⊆ C)
    (hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|)
    (E : Finset (PairLabel × PairLabel)) (hE : E ⊆ lineCollisions A D v eta)
    (q : (Point × Point) × ℝ) :
    ((E.filter (fun e => ((e.1.1,e.2.1),e.1.2)=q)).card : ℝ) ≤ 2*((eta/d)/delta)+2 := by
  have hcard : (E.filter (fun e => ((e.1.1,e.2.1),e.1.2)=q)).card ≤
      (C.filter (fun c' => ‖c' • v-(q.1.1+q.2 • v-q.1.2)‖ ≤ eta)).card := by
    apply Finset.card_le_card_of_injOn (fun e => e.2.2)
    · intro e he
      obtain ⟨heE,heq⟩ := Finset.mem_filter.mp he
      obtain ⟨_he1,he2,hgrid⟩ := (mem_collisions _ _ _).mp (hE heE)
      have ha : e.1.1=q.1.1 := congrArg (fun z : (Point × Point) × ℝ => z.1.1) heq
      have ha' : e.2.1=q.1.2 := congrArg (fun z : (Point × Point) × ℝ => z.1.2) heq
      have hc : e.1.2=q.2 := congrArg Prod.snd heq
      have hid : e.2.2 • v-(q.1.1+q.2 • v-q.1.2)=
          (e.2.1+e.2.2 • v)-(e.1.1+e.1.2 • v) := by rw [ha,ha',hc]; abel
      refine Finset.mem_filter.mpr ⟨hDC (Finset.mem_product.mp he2).2,?_⟩
      rw [hid,norm_sub_rev]
      exact same_grid_norm_le heta hgrid
    · intro e he f hf hef
      have hsame := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      have ha := congrArg (fun z : (Point × Point) × ℝ => z.1.1) hsame
      have ha' := congrArg (fun z : (Point × Point) × ℝ => z.1.2) hsame
      have hc := congrArg Prod.snd hsame
      exact Prod.ext (Prod.ext ha hc) (Prod.ext ha' hef)
  exact (Nat.cast_le.mpr hcard).trans
    (planar_affine_card C v (q.1.1+q.2 • v-q.1.2) hdelta heta.le hd hv hCsep)

/-- Collapse actual output collisions to their original ordered A pairs.
The loss is one original C population times an explicit separation packing
factor, not a supplied multiplicity certificate. -/
theorem original_A_pair_collision_bound (A : Finset Point) (C D : Finset ℝ) (v : Point)
    {eta delta d : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) (hd : 0 < d)
    (hv : d ≤ ‖v‖) (hDC : D ⊆ C)
    (hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|)
    (E : Finset (PairLabel × PairLabel)) (hE : E ⊆ lineCollisions A D v eta) :
    (E.card : ℝ) ≤ (2*((eta/d)/delta)+2)*C.card*
      (E.image (fun e => (e.1.1,e.2.1))).card := by
  let M := 2*((eta/d)/delta)+2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hfib : ∀ aa ∈ E.image (fun e => (e.1.1,e.2.1)),
      ((E.filter (fun e => (e.1.1,e.2.1)=aa)).card : ℝ) ≤ M*C.card := by
    intro aa _
    let P := E.filter (fun e => (e.1.1,e.2.1)=aa)
    have hsmall : ∀ c ∈ P.image (fun e => e.1.2),
        ((P.filter (fun e => e.1.2=c)).card : ℝ) ≤ M := by
      intro c _
      have hh := fixed_points_scalar_fiber_card A C D v heta hdelta hd hv hDC hCsep E hE (aa,c)
      simpa only [P,Finset.filter_filter,Prod.mk.injEq] using hh
    have hc := card_le_real_mul_image P (fun e => e.1.2) hsmall
    have him : P.image (fun e => e.1.2) ⊆ C := by
      intro c hc
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
      have heE := (Finset.mem_filter.mp he).1
      exact hDC (Finset.mem_product.mp ((mem_collisions _ _ _).mp (hE heE)).1).2
    exact hc.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card him)) hM)
  exact card_le_real_mul_image E (fun e => (e.1.1,e.2.1)) hfib
end OriginalLineCollisionCollapse
