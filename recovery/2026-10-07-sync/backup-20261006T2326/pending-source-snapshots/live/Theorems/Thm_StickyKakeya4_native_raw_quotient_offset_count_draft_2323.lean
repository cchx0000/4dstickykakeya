import Theorems.Thm_StickyKakeya4_native_raw_same_point_old_cell_menu_draft_2300
import Theorems.Thm_StickyKakeya4_native_prepared_offset_query_draft_2306
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

/- Actual remembered-source offset counting. The geometric input is the
same-witness affine residual and the already selected one-T coherence;
the old-cell menu is derived from the actual source halo, not assumed.
No uniformity or lower profile is inherited through the eventual cut. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeRawQuotientOffsetCountDraft2323
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeRawHeightSourceAdapter NativeRememberedSourceMaps NativeRememberedCellHalo
open NativeLocalCellCoherence NativeTranslatedGrainHeightOverlap NativeReferenceXYGridPoints
open NativeActualConfiguredPoint CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice
open NativeRawSamePointOldCellMenuDraft2300 NativeTangentGridCoarsening

/-- Literal two-dimensional integer bins of an actual quotient vector. -/
def bin (sigma : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ℤ × ℤ :=
  (⌊v 0/sigma⌋,⌊v 1/sigma⌋)

theorem bin_card_of_diameter {A : Type*} (V : Finset A)
    (v : A → EuclideanSpace ℝ (Fin 2)) {sigma M : ℝ}
    (hsigma : 0 < sigma) (hM : 0 ≤ M)
    (hdiam : ∀z∈V,∀w∈V,‖v z-v w‖ ≤ M) :
    ((V.image (fun z => bin sigma (v z))).card:ℝ) ≤ (2*M/sigma+2)^2 := by
  by_cases hV : V.Nonempty
  · obtain ⟨w,hw⟩ := hV
    have hrect (z : A) (hz : z∈V) :
        (v w 0-M ≤ v z 0 ∧ v z 0 ≤ (v w 0-M)+2*M) ∧
        (v w 1-M ≤ v z 1 ∧ v z 1 ≤ (v w 1-M)+2*M) := by
      have h0 : |v z 0-v w 0| ≤ M :=
        (by simpa only [PiLp.sub_apply,Real.norm_eq_abs] using
          PiLp.norm_apply_le (v z-v w) (0:Fin 2)).trans (hdiam z hz w hw)
      have h1 : |v z 1-v w 1| ≤ M :=
        (by simpa only [PiLp.sub_apply,Real.norm_eq_abs] using
          PiLp.norm_apply_le (v z-v w) (1:Fin 2)).trans (hdiam z hz w hw)
      obtain ⟨h0l,h0u⟩ := abs_le.mp h0
      obtain ⟨h1l,h1u⟩ := abs_le.mp h1
      exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
    simpa only [bin,planarCells,pow_two] using
      planar_rectangle_grid_card V (fun z => (v z 0,v z 1)) hsigma
        (mul_nonneg (by norm_num) hM) (mul_nonneg (by norm_num) hM) hrect
  · rw [not_nonempty_iff_eq_empty] at hV
    simp only [hV,image_empty,card_empty,Nat.cast_zero]
    positivity

/-- Count a bounded union of genuine quotient clouds, without asserting
that different old coherence cells have nearby offsets. -/
theorem bin_card_of_partition {A Label : Type*} [DecidableEq Label]
    (V : Finset A) (label : A → Label) (v : A → EuclideanSpace ℝ (Fin 2))
    {sigma ratio : ℝ} (hsigma : 0 < sigma) (hratio : 512 ≤ ratio)
    (hdiam : ∀z∈V,∀w∈V,label z=label w →
      ‖v z-v w‖ ≤ 4096*ratio*sigma) :
    ((V.image (fun z => bin sigma (v z))).card:ℝ) ≤
      (2:ℝ)^28*ratio^2*(V.image label).card := by
  apply image_card_le_real_mul_of_fiber_images V _ label
  intro q _hq
  have hcap := bin_card_of_diameter (V.filter (fun z => label z=q)) v hsigma
    (by positivity : 0 ≤ 4096*ratio*sigma) (by
      intro z hz w hw
      exact hdiam z (mem_filter.mp hz).1 w (mem_filter.mp hw).1
        ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm))
  have hcancel : 2*(4096*ratio*sigma)/sigma+2=8192*ratio+2 := by
    field_simp [hsigma.ne']
    ring
  rw [hcancel] at hcap
  have hlinear : 8192*ratio+2 ≤ 16384*ratio := by linarith only [hratio]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 8192*ratio+2) hlinear 2
  exact hcap.trans (hpow.trans_eq (by norm_num; ring))

/-- At a single actual native point, raw B fixes the TRUE original height.
Thus the affine parent subtraction is literally the same vector. The
remaining xi variation is exactly the one-T physical-cell coherence. -/
theorem raw_offset_diameter {n nA : ℕ} (C : FiniteScaleSource nA)
    (c : ℕ) (pA : Parent) (Occ : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (k : Index) (label : ((Fin nA × Index) × (Fin n × Index)) → Index)
    (offset : ((Fin nA × Index) × (Fin n × Index)) → EuclideanSpace ℝ (Fin 2))
    (xi : Index → EuclideanSpace ℝ (Fin 2))
    (beta : ℤ → EuclideanSpace ℝ (Fin 2)) {sigma d R : ℝ}
    (hsigma : 0 < sigma) (hd : 0 < d) (hquery : 512*d ≤ R)
    (hscale : ((2^c:ℕ):ℝ)*d=64*sigma)
    (hres : ∀z∈rawCellWitnesses C c pA Occ B k,
      ‖offset z-(((2^c:ℕ):ℝ) • xi z.2.2-beta (z.2.2 3))‖ ≤ 4102*sigma)
    (hcoh : ∀z∈rawCellWitnesses C c pA Occ B k,
      ∀w∈rawCellWitnesses C c pA Occ B k,label z=label w →
      ‖xi z.2.2-xi w.2.2‖ ≤ (129/4:ℝ)*R) :
    ∀z∈rawCellWitnesses C c pA Occ B k,
      ∀w∈rawCellWitnesses C c pA Occ B k,label z=label w →
      ‖offset z-offset w‖ ≤ 4096*(R/d)*sigma := by
  intro z hz w hw hlabel
  have hheight := same_raw_original_height C c pA Occ B hB k z w hz hw
  let az := ((2^c:ℕ):ℝ) • xi z.2.2-beta (z.2.2 3)
  let aw := ((2^c:ℕ):ℝ) • xi w.2.2-beta (w.2.2 3)
  have ha : ‖az-aw‖ ≤ ((2^c:ℕ):ℝ)*((129/4:ℝ)*R) := by
    dsimp only [az,aw]
    rw [hheight,sub_sub_sub_cancel_right,←smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ)<((2^c:ℕ):ℝ))]
    exact mul_le_mul_of_nonneg_left (hcoh z hz w hw hlabel) (by positivity)
  have hzres : ‖offset z-az‖ ≤ 4102*sigma := hres z hz
  have hwres : ‖aw-offset w‖ ≤ 4102*sigma := by
    rw [norm_sub_rev]
    exact hres w hw
  have hsum : ‖offset z-offset w‖ ≤ 8204*sigma+((2^c:ℕ):ℝ)*((129/4:ℝ)*R) := by
    calc
      _ = ‖(offset z-az)+(az-aw)+(aw-offset w)‖ := by congr 1; abel
      _ ≤ (‖offset z-az‖+‖az-aw‖)+‖aw-offset w‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ _ := by linarith only [hzres,ha,hwres]
  have hratio : 512 ≤ R/d := (le_div_iff₀ hd).mpr hquery
  have hidentity : ((2^c:ℕ):ℝ)*((129/4:ℝ)*R)=2064*(R/d)*sigma := by
    apply (mul_right_cancel₀ hd.ne')
    field_simp [hd.ne']
    nlinarith only [hscale]
  rw [hidentity] at hsum
  have hpaid := mul_le_mul_of_nonneg_right
    (show 8204+2064*(R/d) ≤ 4096*(R/d) by linarith only [hratio]) hsigma.le
  exact hsum.trans (by nlinarith only [hpaid])

/-- Full source-facing count. The257^4 menu is proved here from the actual
raw remembered halo; only the original one-T coherence and the genuine
representative residual are read from their source constructors. -/
theorem actual_raw_offset_bin_card {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ)≤64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b:ℕ):ℝ))
    (c : ℕ) (pA : Parent) (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (k : Index) (depth : ℕ) (hQuery : 512*C.thickness≤64/((2^depth:ℕ):ℝ))
    (offset : ((Fin Q.card × Index) × (Fin n × Index)) → EuclideanSpace ℝ (Fin 2))
    (xi : Index → EuclideanSpace ℝ (Fin 2))
    (beta : ℤ → EuclideanSpace ℝ (Fin 2))
    (hres : ∀z∈rawCellWitnesses C c pA (occurrences h backbone a m b p hp Q cells A) B k,
      ‖offset z-(((2^c:ℕ):ℝ) • xi z.2.2-beta (z.2.2 3))‖ ≤
        4102*(((2^c:ℕ):ℝ)*C.thickness/64))
    (hcoh : ∀z∈A,∀w∈A,
      physicalCell D a (2^m) (2^depth) p z.2=physicalCell D a (2^m) (2^depth) p w.2 →
      ‖xi z.2-xi w.2‖ ≤ (129/4:ℝ)*(64/((2^depth:ℕ):ℝ))) :
    let V := rawCellWitnesses C c pA (occurrences h backbone a m b p hp Q cells A) B k
    ((V.image (fun z => bin (((2^c:ℕ):ℝ)*C.thickness/64) (offset z))).card:ℝ) ≤
      (2:ℝ)^64*((64/((2^depth:ℕ):ℝ))/C.thickness)^2 := by
  intro V
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  let R : ℝ := 64/((2^depth:ℕ):ℝ)
  let label := fun z : (Fin Q.card × Index) × (Fin n × Index) =>
    physicalCell D a (2^m) (2^depth) p z.2.2
  have hdC : 0 < C.thickness := hC.1.2.1
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hratio : 512 ≤ R/C.thickness := (le_div_iff₀ hdC).mpr hQuery
  have hOld (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈V) : z.2∈A :=
    ((mem_occurrences h backbone a m b p hp Q cells A z).mp
      (mem_filter.mp (mem_filter.mp hz).1).1).2.1
  have hdiam := raw_offset_diameter C c pA (occurrences h backbone a m b p hp Q cells A)
    B hB k label offset xi beta hsigma hdC hQuery (by dsimp only [sigma]; ring) hres
    (fun z hz w hw hlabel => hcoh z.2 (hOld z hz) w.2 (hOld w hw) hlabel)
  have hbins := bin_card_of_partition V label offset hsigma hratio hdiam
  have hMenu := (actual_raw_cell_old_menu h original horiginal ha backbone m b hm p hp
    hNscale hRelScale Q C hC cells hcells haC hthickness A hA hParent P hP hd
    F Fcfg hF hCfg R0 hR0 hbase hmatch c pA B hB k depth hQuery).2
  have hMenuReal : ((V.image label).card:ℝ) ≤ (257:ℝ)^4 := by exact_mod_cast hMenu
  have hmul := mul_le_mul_of_nonneg_left hMenuReal
    (by positivity : 0 ≤ (2:ℝ)^28*(R/C.thickness)^2)
  have hfixed : (2:ℝ)^28*(257:ℝ)^4 ≤ (2:ℝ)^64 := by norm_num
  calc
    _ ≤ (2:ℝ)^28*(R/C.thickness)^2*(V.image label).card := hbins
    _ ≤ (2:ℝ)^28*(R/C.thickness)^2*(257:ℝ)^4 := hmul
    _ = ((2:ℝ)^28*(257:ℝ)^4)*(R/C.thickness)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfixed (sq_nonneg _)

/-- The actual prepared predecessor pays the two-dimensional offset menu
at the unchanged final native mesh. G is a fixed pre-source arity. -/
theorem paid_bin_count {card sigma ratio chi : ℝ} {G : ℕ}
    (hG : 0 < G) (hsigma : 0 < sigma) (hchi : 0 < chi) (hratio : 0 ≤ ratio)
    (hcard : card ≤ (2:ℝ)^64*ratio^2)
    (hgap : ratio ≤ 1024*sigma^(-(2/((G:ℝ)*chi)))) :
    card ≤ (2:ℝ)^84*sigma^(-(4/((G:ℝ)*chi))) := by
  have hGr : (0:ℝ) < G := by exact_mod_cast hG
  have hpow := pow_le_pow_left₀ hratio hgap 2
  have hidentity : (sigma^(-(2/((G:ℝ)*chi))))^2=sigma^(-(4/((G:ℝ)*chi))) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hsigma.le]
    congr 1
    field_simp [hGr.ne',hchi.ne']
    <;> ring
  calc
    card ≤ (2:ℝ)^64*ratio^2 := hcard
    _ ≤ (2:ℝ)^64*(1024*sigma^(-(2/((G:ℝ)*chi))))^2 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow,hidentity]; norm_num

end NativeRawQuotientOffsetCountDraft2323
