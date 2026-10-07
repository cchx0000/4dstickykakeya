import Theorems.Thm_StickyKakeya4_native_offset_angular_geometry
import Theorems.Thm_StickyKakeya4_native_offset_menu_count
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeActualOffsetMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeIncidentAffineAnchorGeometry NativeNormalizedCellAngularMenu
open NativeReferenceXYGridLinear NativeOffsetAngularGeometry NativeOffsetMenuCount
open NativeGrainQuotientInjection NativeGrainQuotientBins NativeHorizontalGrainSlice
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual normalized angular cells control the full Euclidean direction,
including the fixed zero-height embedding used by the graph quotient. -/
theorem angular_cell_local_difference {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ)
    (hM : 0 < M) (p : Parent) (i j : Fin n)
    (hcell : angularCell D N M p i=angularCell D N M p j) :
    ‖localHorizontalSlope D N p i-localHorizontalSlope D N p j‖ ≤ 24/(M:ℝ) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hcoord (s : Fin 3) : |localSlope D N p i s-localSlope D N p j s| ≤ 8/(M:ℝ) := by
    have he := congrFun hcell s
    change ⌊((M:ℝ)*localSlope D N p i s)/8⌋=⌊((M:ℝ)*localSlope D N p j s)/8⌋ at he
    have hlo := Int.floor_le (((M:ℝ)*localSlope D N p i s)/8)
    have hhi := Int.lt_floor_add_one (((M:ℝ)*localSlope D N p i s)/8)
    have hklo := Int.floor_le (((M:ℝ)*localSlope D N p j s)/8)
    have hkhi := Int.lt_floor_add_one (((M:ℝ)*localSlope D N p j s)/8)
    rw [he] at hlo hhi
    have hh : |((M:ℝ)*localSlope D N p i s)/8-((M:ℝ)*localSlope D N p j s)/8| ≤ 1 :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    have heq : ((M:ℝ)*localSlope D N p i s)/8-((M:ℝ)*localSlope D N p j s)/8=
        ((M:ℝ)/8)*(localSlope D N p i s-localSlope D N p j s) := by ring
    rw [heq,abs_mul,abs_of_pos (by positivity : (0:ℝ)<(M:ℝ)/8)] at hh
    apply (le_div_iff₀ hMr).mpr
    nlinarith only [hh]
  have hn := euclidean_norm_le_sum (localHorizontalSlope D N p i-localHorizontalSlope D N p j)
  rw [Fin.sum_univ_castSucc] at hn
  simp only [localHorizontalSlope,PiLp.sub_apply,ActualSlopeSource.heightPoint_castSucc,
    ActualSlopeSource.heightPoint_last,sub_self,abs_zero,add_zero,Fin.sum_univ_three] at hn
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  change ‖localHorizontalSlope D N p i-localHorizontalSlope D N p j‖ ≤ _
  change ‖localHorizontalSlope D N p i-localHorizontalSlope D N p j‖ ≤ _ at hn
  calc
    _ ≤ 3*(8/(M:ℝ)) := by linarith only [hn,h0,h1,h2]
    _ = _ := by ring

/-- Coarse angular overlap bounds the number of actual offset labels. The
F variation and affine errors are explicit; all incidences and directions
are original. A later caller supplies the proved per-point angular lower. -/
theorem actual_offset_count {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N M : ℕ)
    (hM : 0 < M) (p : Parent) (I : Finset (Fin n × Index))
    (hp : ∀z∈I,parentLabel D a N z.1=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : Index → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error variation d : ℝ)
    (hF : ∀k∈I.image Prod.snd,‖F k‖ ≤ (1/4:ℝ))
    (hvar : ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,‖F k-F l‖ ≤ variation)
    (hres : ∀z∈I,‖quotientMap P hP ell hell hell4 hd (F z.2)
      (localHorizontalSlope D N p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀k∈I.image Prod.snd,d ≤
      (((I.filter (fun z => z.2=k)).image (fun z => angularCell D N M p z.1)).card:ℝ))
    (hH : 0 < 2*error+48/(M:ℝ)+8*variation) :
    d*((I.image (fun z => label (2*error+48/(M:ℝ)+8*variation) (xi z.2))).card:ℝ) ≤
      (4:ℝ)^(4-ell)*(I.image (fun z => angularCell D N M p z.1)).card := by
  apply geometric_offset_count I Prod.snd xi (fun z => angularCell D N M p z.1)
    (2*error+48/(M:ℝ)+8*variation) hH d hlower
  intro z hz w hw he
  have hb := incident_offsets_close P hP ell hell hell4 hd (F z.2) (F w.2)
    (hF z.2 (mem_image_of_mem _ hz)) (localHorizontalSlope D N p z.1) (localHorizontalSlope D N p w.1)
    (xi z.2) (xi w.2) error (24/(M:ℝ)) variation
    (localHorizontalSlope_norm D a N p w.1 (hp w hw)) (hres z hz) (hres w hw)
    (angular_cell_local_difference D N M hM p z.1 w.1 he)
    (hvar z.2 (mem_image_of_mem _ hz) w.2 (mem_image_of_mem _ hw))
  convert hb using 1; ring

end NativeActualOffsetMenu
