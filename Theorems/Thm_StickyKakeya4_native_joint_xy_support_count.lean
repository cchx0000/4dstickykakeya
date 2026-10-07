import Theorems.Thm_StickyKakeya4_native_slice_class_balls
import Theorems.Thm_StickyKakeya4_native_joint_spatial_geometry
import Theorems.Thm_StickyKakeya4_native_grid_support_population
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_actual_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeJointXYSupportCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridSupport
open NativeTwoMapRetainedSliceLabels NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls
open NativeJointSpatialGeometry NativeGridSupportPopulation NativeNormalizedCellRelativeMenu
open NativeTranslatedGrainHeightOverlap NativeSquaredGrainQueries NativeHorizontalGrainSlice
open FiniteVoronoiRealADCoarsening NativeCubicalIncidenceCounts
open scoped Matrix.Norms.Elementwise

lemma encoded_realized_bound {k l : ℕ} (hd : k+l=3) (z : NativeTwoMapRetainedSliceLabels.XY k l)
    {mu : ℝ} (hmu : 0 < mu) (hmu1 : mu  ≤  1) (N : ℕ) (hN : mu*(N:ℝ)  ≤  1)
    (hX : ∀j,|z.2.1 j|  ≤  (N:ℤ)) (hY : ∀j,|z.2.2 j|  ≤  (N:ℤ)) :
    dist (realized mu (encode hd z)) 0  ≤  2 := by
  have hb (i : Fin (k+l)) : |Fin.append z.2.1 z.2.2 i|  ≤  (N:ℤ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hX j
    · simpa only [Fin.append_right] using hY j
  apply (dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 2)).mpr
  intro j
  have hi : |((Fin.append z.2.1 z.2.2 (Fin.cast hd.symm j):ℤ):ℝ)|  ≤  (N:ℝ) := by
    exact_mod_cast hb (Fin.cast hd.symm j)
  have hs := abs_add_le (((Fin.append z.2.1 z.2.2 (Fin.cast hd.symm j):ℤ):ℝ)) (1/2:ℝ)
  rw [Real.dist_eq]
  simp only [realized,encode,Fin.lastCases_castSucc,Pi.zero_apply,sub_zero,abs_mul,abs_of_pos hmu]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at hs
  have hsum : |((Fin.append z.2.1 z.2.2 (Fin.cast hd.symm j):ℤ):ℝ)+1/2| ≤ (N:ℝ)+1/2 :=
    by linarith only [hs,hi]
  have hh := mul_le_mul_of_nonneg_left hsum hmu.le
  nlinarith only [hh,hN,hmu1]

/-- The actual original incidence and same-parent geometry supply the
bounded support required by the finite AD-to-cover theorem. -/
theorem source_realized_box {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12  ≤  m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m  ≤  level) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆incidences original) (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (height : ℤ) :
    ∀x∈realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
      (mu m) height,dist x 0  ≤  2 := by
  intro x hx
  simp only [realizedSlice,NativeSliceCountComparison.heightSlice,mem_image,mem_filter] at hx
  obtain ⟨v,⟨⟨z,hz,rfl⟩,_hheight⟩,rfl⟩ := hx
  have hb := dyadic_pxy_support h original horiginal ha m level hm hdy hf p z.1 z.2 (hT hz)
    (hp z hz) P hP ell hell hell4 hd F hF
  have hmu1 : mu m  ≤  1 := (terminal_bounds m hm).1.trans (by norm_num)
  apply encoded_realized_bound (dimension_sum ell hell hell4) _ (mu_pos m) hmu1 (2*halfWidth m)
  · have hh := mu_fullWidth m (by omega)
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh.le
  · intro j
    exact (hb.1 j).trans (by omega)
  · exact hb.2

lemma realized_coarse_label (mu : ℝ) (hmu : 0 < mu) (R : ℕ) (v : Index) :
    NativeLiteralGridCoverAD.label ((R:ℝ)*mu) (realized mu v)=
      fun j : Fin 3 => v j.castSucc/(R:ℤ) := by
  funext j
  change ⌊mu*((v j.castSucc:ℝ)+1/2)/((R:ℝ)*mu)⌋=v j.castSucc/(R:ℤ)
  rw [mul_comm (R:ℝ) mu,mul_div_mul_left _ _ hmu.ne',Int.floor_div_natCast,Int.floor_intCast_add]
  norm_num

/-- Exact same-height XY coarsening is counted by occupied cubes of the
actual fine realized slice, not by its uncoarsened label cardinality. -/
theorem coarse_xy_image_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (S T : Finset (Fin n × Index)) (hST : S⊆T) (height : ℤ)
    (ht : ∀z∈S,translatedHeight D a m z.2=height) (R : ℕ) :
    (S.image (fun z => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F z.2))).card  ≤ 
      ((realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
        (mu m) height).image (NativeLiteralGridCoverAD.label ((R:ℝ)*mu m))).card := by
  let dim := dimension_sum ell hell hell4
  let Q := S.image (fun z => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F z.2))
  let pack := fun z : NativeReferenceXYGridMaps.XY ell => fun j : Fin 3 => encode dim z j.castSucc
  have hheight : ∀z∈Q,z.1=height := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact ht x hx
  have hcard : (Q.image pack).card=Q.card := by
    apply card_image_iff.mpr
    intro z hz w hw he
    apply (encode_injective dim)
    funext j
    refine Fin.lastCases ?_ (fun j => congrFun he j) j
    simpa only [show (Fin.last 3:Fin 4)=3 by rfl,encode_height] using
      (hheight z hz).trans (hheight w hw).symm
  rw [←hcard]
  apply card_le_card
  intro q hq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  apply mem_image.mpr
  refine ⟨realized (mu m) (encodedPoint D a m ell p P hP hell hell4 hd F x.2),?_,?_⟩
  · apply mem_image.mpr
    refine ⟨encodedPoint D a m ell p P hP hell hell4 hd F x.2,?_,rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_image_of_mem _ (hST hx),?_⟩
    rw [encodedPoint_height,pref_height]
    exact ht x hx
  · rw [realized_coarse_label _ (mu_pos m)]
    funext j
    change encode dim (pxy D a m ell p P hP hell hell4 hd F x.2) j.castSucc/(R:ℤ)=
      encode dim (coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F x.2)) j.castSucc
    simp only [encode,Fin.lastCases_castSucc,coarseXY]
    exact (append_div _ _ R _).symm

/-- Source AD, actual original support and the proved physical-cell halo
produce a count for any literal restriction to one old translated height.
No geometric or spatial-count certificate occurs among the hypotheses. -/
theorem source_height_physical_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12  ≤  m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m  ≤  level) (p : Parent) (S T : Finset (Fin n × Index))
    (hST : S⊆T) (hT : T⊆incidences original) (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (height : ℤ) (ht : ∀z∈S,translatedHeight D a m z.2=height)
    (R depth : ℕ) (hR : 512  ≤  R) (hdepth : 6  ≤  depth)
    (hscale : (R:ℝ)*mu m=64/((2^depth:ℕ):ℝ)) {K t : ℝ} (hK : 0 < K)
    (H : ADBounds (realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
      (mu m) height) (mu m) K t) :
    ((S.image (fun z => physicalCell D a (2^m) (2^depth) p z.2)).card:ℝ)  ≤ 
      (((17^4*9^3*13^3:ℕ):ℝ))*K^2*(64/((2^depth:ℕ):ℝ))^(-t) := by
  let A := realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2)) (mu m) height
  have hR1 : (1:ℝ)  ≤  R := by exact_mod_cast (show 1 ≤ R by omega)
  have hmuScale : mu m  ≤  (R:ℝ)*mu m := le_mul_of_one_le_left (mu_pos m).le hR1
  have hScale1 : (R:ℝ)*mu m  ≤  1 := by
    rw [hscale]
    have hpow : (64:ℝ)  ≤  ((2^depth:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hdepth
    exact (div_le_one (by positivity)).mpr hpow
  have hbox := source_realized_box h original horiginal ha m level ell hm hdy hf p T hT hp P hP hell hell4 hd F hF height
  have hcover := bounded_AD_occupied_keys A (mu_pos m) hmuScale hScale1 hK H hbox
  have hxy : ((S.image (fun z => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ)  ≤ 
      ((A.image (NativeLiteralGridCoverAD.label ((R:ℝ)*mu m))).card:ℝ) :=
    Nat.cast_le.mpr (coarse_xy_image_card D a m ell p P hP hell hell4 hd F S T hST height ht R)
  have hphysical := physical_image_card h m ell (by omega) p i hi P hP hell hell4 hd F hF R depth hR hscale S
  have hh := hphysical.trans (mul_le_mul_of_nonneg_left (hxy.trans hcover) (by positivity))
  rw [hscale] at hh
  simpa only [Nat.cast_mul,mul_assoc] using hh

/-- Global occupied base keys on one genuine source height, with the
fine mesh cancelled by the AD lower populations. -/
theorem source_height_base_keys_global {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (p : Parent) (S T : Finset (Fin n × Index))
    (hST : S⊆T) (hT : T⊆incidences original) (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (height : ℤ) (ht : ∀z∈S,translatedHeight D a m z.2=height)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase1 : (R0:ℝ)*mu m ≤ 1) {K t : ℝ} (hK : 0 < K)
    (H : ADBounds (realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2))
      (mu m) height) (mu m) K t) :
    ((S.image (fun z => coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ) ≤
      ((9^3:ℕ):ℝ)*((13^3:ℕ):ℝ)*K^2*((R0:ℝ)*mu m)^(-t) := by
  let A := realizedSlice (T.image (fun z => encodedPoint D a m ell p P hP hell hell4 hd F z.2)) (mu m) height
  have hR1 : (1:ℝ) ≤ R0 := by exact_mod_cast hR0
  have hscale : mu m ≤ (R0:ℝ)*mu m := le_mul_of_one_le_left (mu_pos m).le hR1
  have hbox := source_realized_box h original horiginal ha m level ell hm hdy hf p T hT hp P hP hell hell4 hd F hF height
  have hg := bounded_AD_occupied_keys A (mu_pos m) hscale hbase1 hK H hbox
  exact (Nat.cast_le.mpr (coarse_xy_image_card D a m ell p P hP hell hell4 hd F S T hST height ht R0)).trans hg

end NativeJointXYSupportCount
