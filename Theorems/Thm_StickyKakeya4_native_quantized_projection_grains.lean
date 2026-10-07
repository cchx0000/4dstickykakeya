import Theorems.Thm_StickyKakeya4_native_approximate_fiber_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeQuantizedProjectionGrains
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeApproximateFiberCount
open scoped BigOperators

def normal (P : Submodule ℝ E4) : E4 →L[ℝ] E4 := Pᗮ.starProjection

def label (P : Submodule ℝ E4) (H : ℝ) (x : E4) : Index :=
  fun j => ⌊normal P x j/H⌋

def vertexLabel (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (k : Index) : Index :=
  label P H (cellCenter mesh k)

lemma normal_norm_le_of_near (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (x : E4) (hx : Metric.infDist x (P:Set E4) ≤ H) : ‖normal P x‖ ≤ 2*H := by
  obtain ⟨u,hu,hxu⟩ := (Metric.infDist_lt_iff (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mp
    (hx.trans_lt (by linarith : H < 2*H))
  have hzero : normal P u=0 := P.starProjection_orthogonal_apply_eq_zero hu
  have he : normal P (x-u)=normal P x := by rw [map_sub,hzero,sub_zero]
  calc
    _ = ‖normal P (x-u)‖ := congrArg norm he.symm
    _ ≤ ‖x-u‖ := Pᗮ.norm_starProjection_apply_le _
    _ ≤ _ := by simpa only [dist_eq_norm] using hxu.le

lemma infDist_le_normal_norm (P : Submodule ℝ E4) (x : E4) :
    Metric.infDist x (P:Set E4) ≤ ‖normal P x‖ := by
  have hh := Metric.infDist_le_dist_of_mem (x:=x) (P.starProjection_apply_mem x)
  simpa only [normal,Submodule.starProjection_orthogonal_val,dist_eq_norm] using hh

/-- A true H-fiber can meet only the five neighboring integer labels in
each projection coordinate. This is an actual geometric overlap bound. -/
theorem label_mem_box_of_near (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (x y : E4) (hxy : Metric.infDist (x-y) (P:Set E4) ≤ H) :
    label P H x∈indexBox (label P H y) 2 := by
  have hn := normal_norm_le_of_near P H hH (x-y) hxy
  apply Fintype.mem_piFinset.mpr
  intro j
  have hcoord : |normal P x j-normal P y j| ≤ 2*H := by
    simpa only [map_sub,PiLp.sub_apply] using (coordinate_abs_le_norm (normal P (x-y)) j).trans hn
  have hscaled : |normal P x j/H-normal P y j/H| ≤ 2 := by
    rw [←sub_div,abs_div,abs_of_pos hH]
    exact (div_le_iff₀ hH).mpr (by nlinarith)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hscaled
  change ⌊normal P x j/H⌋∈Icc (⌊normal P y j/H⌋-2) (⌊normal P y j/H⌋+2)
  refine mem_Icc.mpr ⟨?_,?_⟩
  · simpa only [Int.floor_sub_ofNat] using Int.floor_mono
      (show normal P y j/H-2 ≤ normal P x j/H by linarith)
  · simpa only [Int.floor_add_ofNat] using Int.floor_mono
      (show normal P x j/H ≤ normal P y j/H+2 by linarith)

/-- Equal quantized normal coordinates give a genuine parallel 2H-thick
affine slab through either of the actual points. -/
theorem same_label_near (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (x y : E4) (hlabel : label P H x=label P H y) :
    Metric.infDist (x-y) (P:Set E4) ≤ 2*H := by
  have hcoord (j : Fin 4) : |normal P (x-y) j| ≤ H := by
    have he := congrFun hlabel j
    change ⌊normal P x j/H⌋=⌊normal P y j/H⌋ at he
    have hxl := Int.floor_le (normal P x j/H)
    have hxu := Int.lt_floor_add_one (normal P x j/H)
    have hyl := Int.floor_le (normal P y j/H)
    have hyu := Int.lt_floor_add_one (normal P y j/H)
    rw [he] at hxl hxu
    have hd : |normal P x j/H-normal P y j/H| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    rw [←sub_div,abs_div,abs_of_pos hH] at hd
    have hh := (div_le_iff₀ hH).mp hd
    simpa only [map_sub,PiLp.sub_apply,one_mul] using hh
  have hsq : ‖normal P (x-y)‖^2 ≤ 4*H^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑_j : Fin 4,H^2 := by
        apply sum_le_sum
        intro j _hj
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
      _ = _ := by simp
  have hn : ‖normal P (x-y)‖ ≤ 2*H := by nlinarith [norm_nonneg (normal P (x-y))]
  exact (infDist_le_normal_norm P (x-y)).trans hn

/-- One original occurrence label is selected for each occupied grain label. -/
def representative {α : Type*} (B : Finset α) (f : α → Index)
    (c : {c : Index // c∈B.image f}) : α := Classical.choose (mem_image.mp c.property)

lemma representative_mem {α : Type*} (B : Finset α) (f : α → Index)
    (c : {c : Index // c∈B.image f}) : representative B f c∈B :=
  (Classical.choose_spec (mem_image.mp c.property)).1

lemma representative_label {α : Type*} (B : Finset α) (f : α → Index)
    (c : {c : Index // c∈B.image f}) : f (representative B f c)=c.val :=
  (Classical.choose_spec (mem_image.mp c.property)).2

theorem representatives_cover {α : Type*} (B : Finset α) (loc : α → Index)
    (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H) :
    let f := fun b => vertexLabel mesh P H (loc b)
    ∀c : {c : Index // c∈B.image f},representative B f c∈B ∧
      f (representative B f c)=c.val ∧
      ∀b∈B,f b=c.val → Metric.infDist
        (cellCenter mesh (loc b)-cellCenter mesh (loc (representative B f c))) (P:Set E4) ≤ 2*H := by
  intro f c
  refine ⟨representative_mem B f c,representative_label B f c,?_⟩
  intro b _hb hb
  apply same_label_near P H hH
  change f b=f (representative B f c)
  exact hb.trans (representative_label B f c).symm

/-- The minimum counts actual original A vertices, even when several final
occurrence labels have the same vertex. It may be zero. -/
def minimumFiber {α : Type*} (A : Finset Index) (B : Finset α) (loc : α → Index)
    (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) : ℕ :=
  minimumPredecessor mesh A (B.image loc) P H

/-- Geometry supplies the 625 overlap factor, rather than an assumed
affine quotient or an assumed bound on the number of grains. -/
theorem grain_count_mul {α : Type*} (A : Finset Index) (B : Finset α) (loc : α → Index)
    (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H) (q : ℕ)
    (hgrain : ∀b∈B,q ≤ (fiber mesh A P (cellCenter mesh (loc b)) H).card) :
    (B.image (fun b => vertexLabel mesh P H (loc b))).card*q ≤ 625*A.card := by
  let f := fun b => vertexLabel mesh P H (loc b)
  let R := (B.image f).attach
  let r := fun (c : {c : Index // c∈B.image f}) (a : Index) =>
    a∈fiber mesh A P (cellCenter mesh (loc (representative B f c))) H
  have hlower : ∀c∈R,q ≤ (A.bipartiteAbove r c).card := by
    intro c _hc
    have he : A.bipartiteAbove r c=fiber mesh A P (cellCenter mesh (loc (representative B f c))) H := by
      ext a
      simp [bipartiteAbove,r,fiber]
    rw [he]
    exact hgrain _ (representative_mem B f c)
  have hupper : ∀a∈A,(R.bipartiteBelow r a).card ≤ 625 := by
    intro a _ha
    calc
      _ ≤ (indexBox (vertexLabel mesh P H a) 2).card := by
        apply card_le_card_of_injOn (fun c : {c : Index // c∈B.image f} => c.val)
        · intro c hc
          have hnear := (mem_filter.mp (mem_filter.mp hc).2).2
          have hnear' : Metric.infDist
              (cellCenter mesh (loc (representative B f c))-cellCenter mesh a) (P:Set E4) ≤ H := by
            rw [infDist_sub_comm]
            exact hnear
          have hh := label_mem_box_of_near P H hH (cellCenter mesh (loc (representative B f c)))
            (cellCenter mesh a) hnear'
          change f (representative B f c)∈indexBox (vertexLabel mesh P H a) 2 at hh
          rw [representative_label B f c] at hh
          exact hh
        · intro c _hc d _hd he
          exact Subtype.ext he
      _ = _ := by rw [indexBox_card]; norm_num
  have hh := card_mul_le_card_mul r hlower hupper
  simpa only [R,card_attach,Nat.mul_comm] using hh

/-- Source-facing count using the computed minimum, with no positivity or
richness certificate among the inputs. -/
theorem grain_count_computed {α : Type*} (A : Finset Index) (B : Finset α) (loc : α → Index)
    (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H) :
    (B.image (fun b => vertexLabel mesh P H (loc b))).card*minimumFiber A B loc mesh P H ≤ 625*A.card := by
  apply grain_count_mul A B loc mesh P H hH
  intro b hb
  exact minimumPredecessor_le mesh A (B.image loc) P H (loc b) (mem_image_of_mem loc hb)

end NativeQuantizedProjectionGrains
