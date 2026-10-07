import Theorems.Thm_StickyKakeya4_native_actual_reference_W_directions
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeActualReferenceWPhysical
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeLocalParentGeometry NativeLocalParentPhysicalMap NativeLocalCellCoherence
open NativeAnisotropicShortRowGeometry NativeAnisotropicGlobalSourceBridge NativeActualReferenceWGeometry
open NativeActualReferenceWDirections NativeCoarseDirectionThinning NativeDyadicParentCells

/-- One fixed physical point for each geometric anisotropic column. It is
shared by all incident coarse tubes; no pointwise affine anchor is merged. -/
def position (N : ℕ) (sigma H : ℝ) (q : Index) : E4 :=
  WithLp.toLp 2 (fun v => chartWidth N sigma H v*((q v:ℝ)+1/2))

lemma position_coordinate_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (sigma H : ℝ) (k : Index) (v : Fin 4)
    (hw : 0<chartWidth N sigma H v) :
    |position N sigma H (columnLabel D a N p sigma H k) v-
      physicalMap D a N p (cellCenter (mesh D) k) v| ≤ chartWidth N sigma H v/2 := by
  have hlo := (le_div_iff₀ hw).mp (Int.floor_le
    (physicalMap D a N p (cellCenter (mesh D) k) v/chartWidth N sigma H v))
  have hhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one
    (physicalMap D a N p (cellCenter (mesh D) k) v/chartWidth N sigma H v))
  change |chartWidth N sigma H v*((⌊physicalMap D a N p (cellCenter (mesh D) k) v/
    chartWidth N sigma H v⌋:ℝ)+1/2)-physicalMap D a N p (cellCenter (mesh D) k) v| ≤ _
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma local_front_phase_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N K : ℕ) (hK : 0<K) (p : Parent) (i j : Fin n) (k : Index)
    (hphase : parentLabel D a K j=parentLabel D a K i)
    (ht : |NativeOriginalPaddedCells.oldTime D a k|≤1) (v : Fin 3) :
    |NativeLocalParentCells.frontPoint D a N p i k v.castSucc-
      NativeLocalParentCells.frontPoint D a N p j k v.castSucc|≤(N:ℝ)/(64*(K:ℝ)) := by
  have hh := NativeCoarsePointMultiplicity.same_parent_front_error D a K hK i j k hphase ht v.castSucc
  rw [abs_sub_comm] at hh
  have he : NativeLocalParentCells.frontPoint D a N p i k v.castSucc-
      NativeLocalParentCells.frontPoint D a N p j k v.castSucc=
      (N:ℝ)*(NativeOriginalPaddedCells.frontPoint D a (0,0) i k v.castSucc-
        NativeOriginalPaddedCells.frontPoint D a (0,0) j k v.castSucc) := by
    simp only [NativeLocalParentCells.frontPoint,NativeOriginalPaddedCells.frontPoint,
      NativeContractedUnitParent.contractPoint,ActualSlopeSource.heightPoint_castSucc,
      PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,localSlope,localIntercept,
      NativeUnitParentNormalization.newSlope,NativeUnitParentNormalization.newIntercept]
    simp only [Pi.zero_apply,Int.cast_zero,sub_zero]
    ring
  rw [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N)).trans_eq (by ring)

lemma local_front_graph {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) (k : Index) (v : Fin 3) :
    NativeLocalParentCells.frontPoint D a N p i k v.castSucc=
      localIntercept D a N p i v/32+
        physicalMap D a N p (cellCenter (mesh D) k) (3:Fin 4)*localSlope D N p i v := by
  rw [physicalCell_height]
  simp only [NativeLocalParentCells.frontPoint,NativeContractedUnitParent.contractPoint,
    ActualSlopeSource.heightPoint_castSucc,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
  ring

/-- An original incidence yields the actual common-column-point residual
against any original representative of its fine phase, with all scales paid. -/
theorem original_column_residual {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N K : ℕ) (hN : 0<N) (hK : 0<K) (p : Parent) (i j : Fin n) (k : Index)
    (hk : k∈original i) (hpj : parentLabel D a N j=p)
    (hphase : parentLabel D a K j=parentLabel D a K i)
    (hdelta : D.thickness≤64/(K:ℝ)) (hwindow : 64/(N:ℝ)≤(N:ℝ)*(64/(K:ℝ))) (v : Fin 3) :
    let sigma : ℝ := 64/(K:ℝ)
    let H : ℝ := 64/(N:ℝ)
    let x := position N sigma H (columnLabel D a N p sigma H k)
    |x v.castSucc-localIntercept D a N p j v/32-x (3:Fin 4)*localSlope D N p j v|≤(N:ℝ)*sigma/64 := by
  intro sigma H x
  let P := physicalMap D a N p (cellCenter (mesh D) k)
  let yi := NativeLocalParentCells.frontPoint D a N p i k
  let yj := NativeLocalParentCells.frontPoint D a N p j k
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hsigma : 0<sigma := by dsimp [sigma]; positivity
  have hH : 0<H := by dsimp [H]; positivity
  have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
  have h1 := position_coordinate_error D a N p sigma H k v.castSucc
    (by simp only [chartWidth,if_neg hv]; positivity)
  simp only [chartWidth,if_neg hv] at h1
  have hHeight := position_coordinate_error D a N p sigma H k (3:Fin 4)
    (by simp only [chartWidth,if_true]; positivity)
  simp only [chartWidth,if_true] at hHeight
  have h2 := frontPoint_near_physicalCell h original horiginal ha N p i k hk v.castSucc
  rw [abs_sub_comm] at h2
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k|≤1 at ht
  have h3 := local_front_phase_error D a N K hK p i j k hphase ht v
  have hs := localSlope_bound D a N p j hpj v
  have h4 : |(P (3:Fin 4)-x (3:Fin 4))*localSlope D N p j v|≤H/512/2 := by
    rw [abs_mul]
    rw [abs_sub_comm] at hHeight
    exact (mul_le_mul hHeight hs (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have he : x v.castSucc-localIntercept D a N p j v/32-x (3:Fin 4)*localSlope D N p j v=
      (x v.castSucc-P v.castSucc)+(P v.castSucc-yi v.castSucc)+(yi v.castSucc-yj v.castSucc)+
        (P (3:Fin 4)-x (3:Fin 4))*localSlope D N p j v := by
    have hj : yj v.castSucc=localIntercept D a N p j v/32+P (3:Fin 4)*localSlope D N p j v :=
      local_front_graph D a N p j k v
    rw [hj]
    ring
  rw [he]
  have hh := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
  have hid : (N:ℝ)/(64*(K:ℝ))=(N:ℝ)*sigma/4096 := by dsimp [sigma]; ring
  rw [hid] at hh
  have hdeltaN := mul_le_mul_of_nonneg_left hdelta hNr.le
  change (N:ℝ)*D.thickness≤(N:ℝ)*sigma at hdeltaN
  change H≤(N:ℝ)*sigma at hwindow
  change |(x v.castSucc-P v.castSucc)+(P v.castSucc-yi v.castSucc)+(yi v.castSucc-yj v.castSucc)+
      (P (3:Fin 4)-x (3:Fin 4))*localSlope D N p j v|≤
      (N:ℝ)*sigma/512/2+(3/2:ℝ)*((N:ℝ)*D.thickness/128)+(N:ℝ)*sigma/4096+H/512/2 at hh
  nlinarith only [hh,hdeltaN,hwindow,mul_pos hNr hsigma]

/-- The incidence graph's common physical position and actual full-R tube
representative satisfy a genuine chord-ready coordinate residual. The
point is determined by its column alone, independently of the incident tube. -/
theorem geometric_incidence_residual {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (m f : ℕ) (hmf : m≤f)
    (hdelta : D.thickness≤64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2≤64/((2^f:ℕ):ℝ))
    (p : Parent) (H : Finset (Fin n × Index))
    (hH : H⊆NativeCubicalIncidenceCounts.incidences original)
    (hR : ∀z∈H,z.1∈R) (hp : ∀z∈H,parentLabel D a (2^m) z.1=p)
    (q : Index) (t : Parent) (hqt : (q,t)∈NativeActualReferenceWGeometry.incidences D a m f p H)
    (v : Fin 3) :
    let x := position (2^m) (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) q
    let j := representative h R a (2^f) t
    |x v.castSucc-localIntercept D a (2^m) p j v/32-x (3:Fin 4)*localSlope D (2^m) p j v|≤
      ((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ))/64 := by
  intro x j
  obtain ⟨z,hz,hze⟩ := mem_image.mp hqt
  have hcol : (columnPair D a m f p z).2=q := congrArg Prod.fst hze
  have hphase : parentLabel D a (2^f) z.1=t := congrArg Prod.snd hze
  have ht : t∈TwoTubePathCollisionCount.tubes (NativeActualReferenceWGeometry.incidences D a m f p H) :=
    mem_image_of_mem Prod.snd hqt
  have hrep := representative_parent h R m f hmf p H hR hp t ht
  have hscale : 64/((2^m:ℕ):ℝ)≤((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hwindow (show (0:ℝ)≤((2^m:ℕ):ℝ) by positivity)
    have hid : ((2^m:ℕ):ℝ)*(64/((2^m:ℕ):ℝ))^2=64*(64/((2^m:ℕ):ℝ)) := by field_simp
    rw [hid] at hh
    linarith only [hh,show (0:ℝ)<64/((2^m:ℕ):ℝ) by positivity]
  have hbound := original_column_residual h original horiginal ha (2^m) (2^f) (by positivity) (by positivity)
    p z.1 j z.2 ((mem_incidences original z.1 z.2).mp (hH hz)) hrep.2.2
    (hrep.2.1.trans hphase.symm) hdelta hscale v
  change columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2=q at hcol
  simpa only [hcol] using hbound

end NativeActualReferenceWPhysical
