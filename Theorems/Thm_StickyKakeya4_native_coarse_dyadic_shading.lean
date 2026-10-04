import Theorems.Thm_StickyKakeya4_native_coarse_shading_capacity
import Theorems.Thm_StickyKakeya4_native_coarse_ancestor_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCoarseDyadicShading
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseShadingCapacity NativeDyadicParentCells
open scoped BigOperators

def block (level m : ℕ) : ℕ := 4096*2^(level-m)
lemma block_pos (level m : ℕ) : 0 < block level m := by dsimp [block]; positivity

lemma block_scale {delta : ℝ} {level m : ℕ} (hdy : delta=(2:ℝ)⁻¹^level) (hm : m≤level) :
    (block level m:ℝ)=4096*(1/((2^m:ℕ):ℝ))/delta := by
  have hd : 0 < delta := by rw [hdy]; positivity
  have hp : (2:ℝ)^m*(2:ℝ)^(level-m)=(2:ℝ)^level := by
    rw [←pow_add,Nat.add_sub_of_le hm]
  have hscale := dyadic_fine_scale hdy
  rw [Nat.cast_pow,Nat.cast_ofNat] at hscale
  apply (eq_div_iff hd.ne').mpr
  dsimp [block]
  push_cast
  rw [mul_one_div]
  apply (eq_div_iff (show (2:ℝ)^m≠0 by positivity)).mpr
  have he : ((2:ℝ)^(level-m)*delta)*(2:ℝ)^m=1 := by
    calc
      _ = ((2:ℝ)^m*(2:ℝ)^(level-m))*delta := by ring
      _ = 1 := by rw [hp]; exact hscale
  nlinarith only [he]

lemma block_mesh {delta : ℝ} {level m : ℕ} (hdy : delta=(2:ℝ)⁻¹^level) (hm : m≤level) :
    (block level m:ℝ)*delta/128=32/((2^m:ℕ):ℝ) := by
  rw [block_scale hdy hm]
  have hd : delta≠0 := by rw [hdy]; positivity
  field_simp [hd]
  ring

lemma block_thickness {delta : ℝ} {level m : ℕ} (hdy : delta=(2:ℝ)⁻¹^level) (hm : m≤level) :
    (block level m:ℝ)*delta/64=64/((2^m:ℕ):ℝ) := by
  calc
    _ = 2*((block level m:ℝ)*delta/128) := by ring
    _ = 2*(32/((2^m:ℕ):ℝ)) := by rw [block_mesh hdy hm]
    _ = _ := by ring

/-- The coarse thickness is a genuine dyadic scale with the explicit six
level padding margin. The cube mesh is exactly half this thickness. -/
lemma block_thickness_dyadic {delta : ℝ} {level m : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hm : m≤level) (h6 : 6 ≤ m) :
    IsWZDyadicScale ((block level m:ℝ)*delta/64) := by
  refine ⟨m-6,?_⟩
  rw [block_thickness hdy hm,Nat.cast_pow,Nat.cast_ofNat]
  have hp : (2:ℝ)^m=64*(2:ℝ)^(m-6) := by
    calc
      _ = (2:ℝ)^(6+(m-6)) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  rw [hp,inv_pow]
  field_simp

/-- Consume the genuine original ancestor UPPER population at the requested
coarse dyadic level. Every original shading cell of every retained label is
used in the output image, so this is an aggregate source law. -/
theorem original_dyadic_shading_transfer {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀ell : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3)
    (m : ℕ) (hm : m≤level) (rep : Parent → Fin n) :
    (∑i∈R,(volume (D.shading i)).toReal) ≤ 43*D.thickness^(-zeta)*
      (∑p∈R.image (parentLabel D a (2^m)),
        (volume (wzCellShading ((block level m:ℝ)*D.thickness/128)
          (fun _ : Fin 1 => rows D a (2^m) (block level m) rep (retained original R) p) 0)).toReal) := by
  apply actual_aggregate_shading_transfer h original horiginal ha R (2^m) (block level m)
    (block_pos level m) rep (by positivity : 0 < 1/((2^m:ℕ):ℝ)) (block_scale hdy hm)
  intro p hp
  obtain ⟨i,hi,hip⟩ := mem_image.mp hp
  exact H ⟨m,by omega⟩ p ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩

end NativeCoarseDyadicShading
