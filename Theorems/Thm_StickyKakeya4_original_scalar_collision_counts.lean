import Theorems.Thm_StickyKakeya4_original_separated_packing
import Theorems.Thm_StickyKakeya4_original_scalar_collision_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
open Finset
noncomputable section
open Classical
namespace OriginalScalarCollisionCounts
open PlanarShiftedNearEnergy TwoTubePathCollisionCount OriginalScalarCollisionGeometry
open OriginalSeparatedPacking
abbrev Point := ℝ × ℝ
abbrev PairLabel := Point × ℝ

def lineCollisions (A : Finset Point) (D : Finset ℝ) (v : Point) (eta : ℝ) :=
  collisions (A ×ˢ D) (fun e => roundPoint eta (e.1+e.2 • v))

def closeScalarCollisions (A : Finset Point) (D : Finset ℝ) (v : Point) (eta t : ℝ) :=
  (lineCollisions A D v eta).filter (fun e => |e.1.2-e.2.2| ≤ t)

/-- Fixing the first original label and both scalars leaves an actual A point
inside one eta-box. -/
lemma collision_fiber_le_ball (A : Finset Point) (D : Finset ℝ) (v : Point)
    {eta : ℝ} (heta : 0 < eta) (E : Finset (PairLabel × PairLabel))
    (hE : E ⊆ lineCollisions A D v eta) (q : PairLabel × ℝ) :
    (E.filter (fun e => (e.1,e.2.2)=q)).card ≤
      (A.filter (fun a => ‖a-(q.1.1+(q.1.2-q.2) • v)‖ ≤ eta)).card := by
  apply Finset.card_le_card_of_injOn (fun e => e.2.1)
  · intro e he
    obtain ⟨heE,heq⟩ := Finset.mem_filter.mp he
    obtain ⟨he1,he2,hgrid⟩ := (mem_collisions _ _ _).mp (hE heE)
    have hfirst : e.1=q.1 := congrArg Prod.fst heq
    have hlast : e.2.2=q.2 := congrArg Prod.snd heq
    have hid : e.2.1-(q.1.1+(q.1.2-q.2) • v)=
        (e.2.1+e.2.2 • v)-(e.1.1+e.1.2 • v) := by
      rw [hfirst,hlast]
      simp only [sub_smul]
      abel
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp he2).1,?_⟩
    rw [hid,norm_sub_rev]
    exact same_grid_norm_le heta hgrid
  · intro e he f hf hef
    have heq := (Finset.mem_filter.mp he).2
    have hfq := (Finset.mem_filter.mp hf).2
    have hsame := heq.trans hfq.symm
    have hfirst : e.1=f.1 := congrArg (fun q : PairLabel × ℝ => q.1) hsame
    have hlast : e.2.2=f.2.2 := congrArg (fun q : PairLabel × ℝ => q.2) hsame
    exact Prod.ext hfirst (Prod.ext hef hlast)

/-- The original C cap bounds the bad close-scalar part of the actual output
collision set. Original A separation supplies the factor 16. -/
theorem close_scalar_collision_card (A : Finset Point) (C D : Finset ℝ) (v : Point)
    {eta t chi : ℝ} (heta : 0 < eta) (hchi : 0 ≤ chi) (hDC : D ⊆ C)
    (hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → eta ≤ ‖a-a'‖)
    (hCcap : ∀ c ∈ C, ((C.filter (fun c' => |c'-c| ≤ t)).card : ℝ) ≤ chi*C.card) :
    ((closeScalarCollisions A D v eta t).card : ℝ) ≤
      16*chi*A.card*(C.card : ℝ)^2 := by
  let E := closeScalarCollisions A D v eta t
  let f : PairLabel × PairLabel → PairLabel × ℝ := fun e => (e.1,e.2.2)
  let Q := E.image f
  have hE : E ⊆ lineCollisions A D v eta := Finset.filter_subset _ _
  have hfirst : ∀ q ∈ Q, q.1 ∈ A ×ˢ D := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
    exact ((mem_collisions _ _ _).mp (hE he)).1
  have hfiber : ∀ q ∈ Q, ((E.filter (fun e => f e=q)).card : ℝ) ≤ 16 := by
    intro q _
    have hb := collision_fiber_le_ball A D v heta E hE q
    have hp := planar_ball_card A heta heta.le hAsep (q.1.1+(q.1.2-q.2) • v)
    have hcard := (Nat.cast_le.mpr hb).trans hp
    norm_num only [div_self heta.ne'] at hcard
    exact hcard
  have hEc : (E.card : ℝ) ≤ 16*Q.card := card_le_real_mul_image E f hfiber
  have hQfiber : ∀ p ∈ Q.image Prod.fst,
      ((Q.filter (fun q => q.1=p)).card : ℝ) ≤ chi*C.card := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp
    have hpC : p.2 ∈ C := hDC (Finset.mem_product.mp (hqp ▸ hfirst q hq)).2
    have hsubcard : (Q.filter (fun q => q.1=p)).card ≤
        (C.filter (fun c' => |c'-p.2| ≤ t)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro q hqf
        obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hqf
        obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hq
        obtain ⟨hecoll,heclose⟩ := Finset.mem_filter.mp he
        obtain ⟨_he1,he2,_⟩ := (mem_collisions _ _ _).mp hecoll
        have hlast : e.2.2=q.2 := congrArg Prod.snd heq
        have hfirstq : e.1=q.1 := congrArg Prod.fst heq
        refine Finset.mem_filter.mpr ⟨hlast ▸ hDC (Finset.mem_product.mp he2).2,?_⟩
        rw [hfirstq,hlast,hqp,abs_sub_comm] at heclose
        exact heclose
      · intro q hq q' hq' hqq'
        exact Prod.ext ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm) hqq'
    exact (Nat.cast_le.mpr hsubcard).trans (hCcap p.2 hpC)
  have hQc : (Q.card : ℝ) ≤ (chi*C.card)*(Q.image Prod.fst).card :=
    card_le_real_mul_image Q Prod.fst hQfiber
  have hPsub : Q.image Prod.fst ⊆ A ×ˢ D := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hfirst q hq
  have hPc : ((Q.image Prod.fst).card : ℝ) ≤ (A.card : ℝ)*C.card := by
    have hh := (Finset.card_le_card hPsub).trans
      (show (A ×ˢ D).card ≤ A.card*C.card by
        rw [Finset.card_product]
        exact Nat.mul_le_mul_left _ (Finset.card_le_card hDC))
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_left hPc (show 0 ≤ chi*(C.card : ℝ) by positivity)
  have hlast := hEc.trans (mul_le_mul_of_nonneg_left (hQc.trans hm) (by norm_num : (0:ℝ) ≤ 16))
  nlinarith only [hlast]
end OriginalScalarCollisionCounts
