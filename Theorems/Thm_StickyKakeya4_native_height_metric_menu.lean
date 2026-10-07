import Theorems.Thm_StickyKakeya4_native_coarse_height_slope_variation
import Theorems.Thm_StickyKakeya4_native_height_residue_selection
import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeHeightMetricMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCompatibleAngularCandidates
open NativeRetainedQueryMenu NativeMiddleGrainParentBudget
open scoped BigOperators Matrix.Norms.Elementwise

def meshWidth (m : ℕ) : ℝ := 64/((2^m:ℕ):ℝ)

lemma meshWidth_pos (m : ℕ) : 0 < meshWidth m := by unfold meshWidth; positivity

lemma meshWidth_ratio {a b : ℕ} (hab : a ≤ b) :
    meshWidth a=((2^(b-a):ℕ):ℝ)*meshWidth b := by
  have hpow : (2:ℕ)^a*2^(b-a)=2^b := by rw [←pow_add,Nat.add_sub_of_le hab]
  have hpowR : ((2^a:ℕ):ℝ)*((2^(b-a):ℕ):ℝ)=((2^b:ℕ):ℝ) := by exact_mod_cast hpow
  unfold meshWidth
  field_simp
  nlinarith only [hpowR]

/-- Raw time-grid coordinates of height labels, before the physical map's1/512 contraction. -/
def rawHeightCoordinate (fine : ℕ) (t : ℤ) : ℝ := meshWidth fine*(t:ℝ)

lemma rawHeightCoordinate_distance (fine : ℕ) (x y : ℤ) :
    |rawHeightCoordinate fine x-rawHeightCoordinate fine y|=
      meshWidth fine*((x-y).natAbs:ℝ) := by
  rw [rawHeightCoordinate,rawHeightCoordinate,←mul_sub,abs_mul,abs_of_pos (meshWidth_pos fine)]
  congr 1
  norm_cast
  rw [Int.abs_eq_natAbs,Int.cast_natCast]

/-- Any common fine representative offset is absorbed by shift and cancels. -/
def chartHeightCoordinate (fine : ℕ) (shift : ℝ) (t : ℤ) : ℝ :=
  (rawHeightCoordinate fine t-shift)/512

lemma chartHeightCoordinate_distance (fine : ℕ) (shift : ℝ) (x y : ℤ) :
    |rawHeightCoordinate fine x-rawHeightCoordinate fine y|=
      512*|chartHeightCoordinate fine shift x-chartHeightCoordinate fine shift y| := by
  unfold chartHeightCoordinate
  rw [←sub_div,sub_sub_sub_cancel_right,abs_div]
  norm_num
  ring

/-- Select a just-coarser installed menu depth using the ACTUAL integer
height distance. No logarithmic scale or adaptive query is added. -/
lemma menu_crossing (J fine D : ℕ) (_hJ : 0 < J) (hD : 0 < D)
    (depth : Fin (J+1) → ℕ) (hzero : depth 0=6) (hlast : depth (Fin.last J)=fine)
    (hclose : D<2^(fine-6)) :
    ∃i : Fin J,D<2^(fine-depth i.castSucc) ∧ 2^(fine-depth i.succ)≤D := by
  let A := univ.filter (fun j : Fin (J+1) => D<2^(fine-depth j))
  have hA : A.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,by simpa only [hzero] using hclose⟩⟩
  obtain ⟨j,hj,hmax⟩ := exists_max_image A (fun j => j.val) hA
  have hjclose := (mem_filter.mp hj).2
  have hjJ : j.val<J := by
    by_contra hh
    have heq : j=Fin.last J := by
      apply Fin.ext
      have hjlt := j.isLt
      change j.val=J
      omega
    rw [heq,hlast,Nat.sub_self,pow_zero] at hjclose
    omega
  let i : Fin J := ⟨j.val,hjJ⟩
  have hij : i.castSucc=j := Fin.ext rfl
  refine ⟨i,by simpa only [hij] using hjclose,?_⟩
  by_contra hh
  have hn : i.succ∈A := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hmax' := hmax i.succ hn
  dsimp [i] at hmax'
  omega

/-- The first half of an even fixed grain schedule ends at its literal middle grain. -/
def halfDepth (K stop : ℕ) (i : Fin (K+1)) : ℕ :=
  grainDepth (2*K) stop ⟨i.val,by omega⟩

lemma halfDepth_zero (K stop : ℕ) (hs : 6 ≤ stop) : halfDepth K stop 0=6 := by
  change grainDepth (2*K) stop 0=6
  rw [grainDepth_zero,min_eq_left hs]

lemma halfDepth_last (K stop : ℕ) (hK : 0 < K) (hs : 6 ≤ stop) :
    halfDepth K stop (Fin.last K)=middleDepth stop := grainDepth_middle K stop hK hs

lemma halfDepth_mono (K stop : ℕ) : Monotone (halfDepth K stop) := by
  intro i j hij
  exact grainDepth_mono (2*K) stop _ _ hij

lemma halfDepth_le_middle (K stop : ℕ) (hK : 0 < K) (hs : 6 ≤ stop) (i : Fin (K+1)) :
    halfDepth K stop i ≤ middleDepth stop := by
  rw [←halfDepth_last K stop hK hs]
  exact halfDepth_mono K stop (Fin.le_last i)

lemma halfDepth_gap (K stop : ℕ) (hK : 0 < K) (hs : 6 ≤ stop) (i : Fin K) :
    halfDepth K stop i.succ-halfDepth K stop i.castSucc ≤ (stop-6)/(2*K)+1 := by
  let j : Fin (2*K) := ⟨i.val,by omega⟩
  have hh := (grainDepth_succ_gap (2*K) stop (by omega) j).1
  rw [min_eq_left hs] at hh
  exact hh

/-- The precise metric constant; the first term pays distances beyond the root mesh. -/
def metricConstant (G : ℕ) (C : ℝ) : ℝ := max (1/2) ((9/8)*((2^G:ℕ):ℝ)*C)

lemma metricConstant_nonneg (G : ℕ) (C : ℝ) : 0 ≤ metricConstant G C :=
  le_trans (by norm_num) (le_max_left _ _)

/-- Exact finite-menu interpolation. Its local input will be produced by
actual residue alignment and the proved original-tuple matrix variation. -/
theorem metric_from_menu {V : Type*} [NormedAddCommGroup V]
    (F : ℤ → V) (x y : ℤ) (fine J G : ℕ) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hzero : depth 0=6) (hlast : depth (Fin.last J)=fine)
    (hdepth : ∀j,depth j≤fine) (hmono : Monotone depth)
    (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc≤G)
    (C : ℝ) (hC : 0 ≤ C) (hFx : ‖F x‖≤1/4) (hFy : ‖F y‖≤1/4)
    (Hlocal : ∀j : Fin (J+1),(x-y).natAbs<2^(fine-depth j)→
      ‖F x-F y‖≤(72/((2^(depth j):ℕ):ℝ))*C) :
    ‖F x-F y‖ ≤ metricConstant G C*|rawHeightCoordinate fine x-rawHeightCoordinate fine y| := by
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,norm_zero,abs_zero,mul_zero,le_refl]
  let D := (x-y).natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr (sub_ne_zero.mpr hxy)
  have hdist : |rawHeightCoordinate fine x-rawHeightCoordinate fine y|=meshWidth fine*(D:ℝ) :=
    rawHeightCoordinate_distance fine x y
  by_cases hclose : D<2^(fine-6)
  · obtain ⟨i,hi,hnext⟩ := menu_crossing J fine D hJ hD depth hzero hlast hclose
    have hlocal := Hlocal i.castSucc hi
    have hstep : depth i.castSucc≤depth i.succ := hmono (by exact Fin.castSucc_le_succ i)
    have hwidth : meshWidth (depth i.castSucc) ≤ ((2^G:ℕ):ℝ)*(meshWidth fine*(D:ℝ)) := by
      calc
        _ = ((2^(depth i.succ-depth i.castSucc):ℕ):ℝ)*meshWidth (depth i.succ) := meshWidth_ratio hstep
        _ ≤ ((2^G:ℕ):ℝ)*(meshWidth fine*(D:ℝ)) := by
          apply mul_le_mul
          · exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (hgap i)
          · rw [meshWidth_ratio (hdepth i.succ)]
            have hh : ((2^(fine-depth i.succ):ℕ):ℝ)≤D := by exact_mod_cast hnext
            simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (meshWidth_pos fine).le
          · exact (meshWidth_pos _).le
          · positivity
    have hlocal' : ‖F x-F y‖≤((9/8:ℝ)*meshWidth (depth i.castSucc))*C := by
      convert hlocal using 1
      unfold meshWidth
      ring
    calc
      _ ≤ ((9/8:ℝ)*meshWidth (depth i.castSucc))*C := hlocal'
      _ ≤ ((9/8:ℝ)*(((2^G:ℕ):ℝ)*(meshWidth fine*(D:ℝ))))*C :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (by norm_num)) hC
      _ = ((9/8:ℝ)*((2^G:ℕ):ℝ)*C)*|rawHeightCoordinate fine x-rawHeightCoordinate fine y| := by rw [hdist]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  · have hlarge : (1:ℝ)≤|rawHeightCoordinate fine x-rawHeightCoordinate fine y| := by
      have hs : 6≤fine := by simpa only [hzero] using hdepth 0
      calc
        1 = meshWidth 6 := by norm_num [meshWidth]
        _ = ((2^(fine-6):ℕ):ℝ)*meshWidth fine := meshWidth_ratio hs
        _ ≤ (D:ℝ)*meshWidth fine := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2^(fine-6)≤D)) (meshWidth_pos fine).le
        _ = _ := by rw [hdist]; ring
    have hnorm : ‖F x-F y‖ ≤ (1/2:ℝ) := (norm_sub_le _ _).trans (by linarith only [hFx,hFy])
    calc
      _ ≤ (1/2:ℝ) := hnorm
      _ ≤ (1/2:ℝ)*|rawHeightCoordinate fine x-rawHeightCoordinate fine y| := le_mul_of_one_le_right (by norm_num) hlarge
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)

/-- Exact conversion to translated normalized time coordinates. -/
theorem metric_from_menu_chart {V : Type*} [NormedAddCommGroup V]
    (F : ℤ → V) (x y : ℤ) (fine G : ℕ) (C shift : ℝ)
    (H : ‖F x-F y‖ ≤ metricConstant G C*|rawHeightCoordinate fine x-rawHeightCoordinate fine y|) :
    ‖F x-F y‖ ≤ (512*metricConstant G C)*|chartHeightCoordinate fine shift x-chartHeightCoordinate fine shift y| := by
  rw [chartHeightCoordinate_distance fine shift x y] at H
  convert H using 1
  ring

end NativeHeightMetricMenu
