import Theorems.Thm_StickyKakeya4_native_coarse_point_multiplicity
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeCoarseScaleInterpolation
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeOriginalPaddedCells NativeCoarseShadingCapacity NativeCoarseDirectionThinning
open NativeDyadicParentCells NativeCoarseDyadicShading NativeCoarsePointMultiplicity
open scoped BigOperators

/-- Three spatial neighbor choices and the exact dyadic height ancestor. -/
def coarseMenu (r : ℕ) (q : Index) : Finset Index :=
  Fintype.piFinset (fun j => if j=(3:Fin 4) then {q j/(r:ℤ)}
    else Icc (q j/(r:ℤ)-1) (q j/(r:ℤ)+1))

lemma coarseMenu_card (r : ℕ) (q : Index) : (coarseMenu r q).card=27 := by
  have hi (j : Fin 4) : (Icc (q j/(r:ℤ)-1) (q j/(r:ℤ)+1)).card=3 := by
    have hh : ((Icc (q j/(r:ℤ)-1) (q j/(r:ℤ)+1)).card:ℤ)=3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [coarseMenu,Fintype.card_piFinset,Fin.prod_univ_four]
  simp [hi]

/-- Inverse menu: exactly 3r spatial indices and r height indices. -/
def fineMenu (r : ℕ) (q : Index) : Finset Index :=
  Fintype.piFinset (fun j => if j=(3:Fin 4) then
    Icc ((r:ℤ)*q j) ((r:ℤ)*(q j+1)-1)
    else Icc ((r:ℤ)*(q j-1)) ((r:ℤ)*(q j+2)-1))

lemma fineMenu_card (r : ℕ) (hr : 0 < r) (q : Index) : (fineMenu r q).card=27*r^4 := by
  have hrz : (0:ℤ)<r := by exact_mod_cast hr
  have hi (j : Fin 4) : (Icc ((r:ℤ)*(q j-1)) ((r:ℤ)*(q j+2)-1)).card=3*r := by
    have hh : ((Icc ((r:ℤ)*(q j-1)) ((r:ℤ)*(q j+2)-1)).card:ℤ)=3*r := by
      rw [Int.card_Icc_of_le _ _ (by nlinarith)]
      ring
    exact_mod_cast hh
  have ht (j : Fin 4) : (Icc ((r:ℤ)*q j) ((r:ℤ)*(q j+1)-1)).card=r := by
    have hh : ((Icc ((r:ℤ)*q j) ((r:ℤ)*(q j+1)-1)).card:ℤ)=r := by
      rw [Int.card_Icc_of_le _ _ (by nlinarith)]
      ring
    exact_mod_cast hh
  simp only [fineMenu,Fintype.card_piFinset,Fin.prod_univ_four]
  norm_num only [show (0:Fin 4)≠3 by decide,show (1:Fin 4)≠3 by decide,
    show (2:Fin 4)≠3 by decide,if_false,if_true,hi,ht]
  ring

lemma coarse_mem_implies_fine_mem (r : ℕ) (hr : 0 < r) (qc qm : Index)
    (h : qc∈coarseMenu r qm) : qm∈fineMenu r qc := by
  have hrz : (0:ℤ)<r := by exact_mod_cast hr
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := Fintype.mem_piFinset.mp h j
  by_cases ht : j=(3:Fin 4)
  · subst j
    simp only [if_true,mem_singleton] at hj
    simp only [if_true]
    apply mem_Icc.mpr
    have hlo := (Int.le_ediv_iff_mul_le hrz).mp hj.le
    have hhi := (Int.ediv_lt_iff_lt_mul hrz).mp (show qm 3/(r:ℤ)<qc 3+1 by omega)
    constructor <;> nlinarith
  · simp only [if_neg ht,mem_Icc] at hj
    simp only [if_neg ht]
    apply mem_Icc.mpr
    have hlo := (Int.le_ediv_iff_mul_le hrz).mp (show qc j-1≤qm j/(r:ℤ) by omega)
    have hhi := (Int.ediv_lt_iff_lt_mul hrz).mp (show qm j/(r:ℤ)<qc j+2 by omega)
    constructor <;> nlinarith

lemma floor_close {e : ℝ} (he : 0 < e) (x y : ℝ) (hxy : |x-y|≤e) :
    ⌊x/e⌋ ∈ Icc (⌊y/e⌋-1) (⌊y/e⌋+1) := by
  have ha := abs_le.mp hxy
  have hl : y/e-1≤x/e := by apply (le_div_iff₀ he).mpr; field_simp [he.ne']; linarith
  have hu : x/e≤y/e+1 := by apply (div_le_iff₀ he).mpr; field_simp [he.ne']; linarith
  have hl' := Int.floor_mono hl
  have hu' := Int.floor_mono hu
  rw [Int.floor_sub_one] at hl'
  rw [Int.floor_add_one] at hu'
  exact mem_Icc.mpr ⟨hl',hu'⟩

/-- Moving the representative by at most one coarse mesh only changes the
spatial dyadic ancestor by one; the common height ancestor is exact. -/
lemma cellIndex_mem_coarseMenu {ef ec : ℝ} (hf : 0 < ef) (r : ℕ) (hr : 0 < r)
    (hscale : ec=(r:ℝ)*ef) (x y : E4) (hxy : ∀j,|x j-y j|≤ec)
    (ht : x (3:Fin 4)=y (3:Fin 4)) :
    wzDyadicCellIndex ec x∈coarseMenu r (wzDyadicCellIndex ef y) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hc : 0<ec := by rw [hscale]; positivity
  have he (j : Fin 4) : ⌊y j/ec⌋=⌊y j/ef⌋/(r:ℤ) := by
    have hx : y j/ec=(y j/ef)/(r:ℝ) := by rw [hscale]; field_simp
    rw [hx,Int.floor_div_natCast]
  apply Fintype.mem_piFinset.mpr
  intro j
  by_cases hj : j=(3:Fin 4)
  · subst j
    simp only [if_true,mem_singleton,wzDyadicCellIndex,ht]
    exact he 3
  · simp only [if_neg hj]
    change ⌊x j/ec⌋∈Icc (⌊y j/ef⌋/(r:ℤ)-1) (⌊y j/ef⌋/(r:ℤ)+1)
    rw [←he j]
    exact floor_close hc _ _ (hxy j)

/-- The actual parent/cell label at a dyadic coarse depth. -/
def actualPair {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level t : ℕ) (z : Fin n × Index) : Parent × Index :=
  label D a (2^t) (block level t) (representative h R a (2^t)) z

lemma coarse_mesh_ratio (c m : ℕ) (hcm : c ≤ m) :
    32/((2^c:ℕ):ℝ)=((2^(m-c):ℕ):ℝ)*(32/((2^m:ℕ):ℝ)) := by
  have hp : (2:ℝ)^m=(2:ℝ)^c*(2:ℝ)^(m-c) := by rw [←pow_add,Nat.add_sub_of_le hcm]
  push_cast
  rw [hp]
  field_simp

/-- The same original incidence determines both actual labels. Its two
representatives have the same original c-parent, with no output hypothesis. -/
theorem actual_pair_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) (z : Fin n × Index) (hz : z.1∈R) (hk : z.2∈original z.1) :
    (actualPair h R a level c z).1=ancestor m c (actualPair h R a level m z).1 ∧
      (actualPair h R a level c z).2∈coarseMenu (2^(m-c)) (actualPair h R a level m z).2 := by
  let jc := representative h R a (2^c) (parentLabel D a (2^c) z.1)
  let jm := representative h R a (2^m) (parentLabel D a (2^m) z.1)
  have hc := (representative_spec h R a (2^c) (mem_image_of_mem _ hz)).2
  have hm := (representative_spec h R a (2^m) (mem_image_of_mem _ hz)).2
  have hp : parentLabel D a (2^c) jc=parentLabel D a (2^c) jm := by
    rw [←parent_ancestor_eq D a hcm jm,show parentLabel D a (2^m) jm=parentLabel D a (2^m) z.1 from hm,
      parent_ancestor_eq D a hcm z.1]
    exact hc
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original z.1 z.2).mpr hk)).1
  change |oldTime D a z.2|≤1 at ht
  refine ⟨(parent_ancestor_eq D a hcm z.1).symm,?_⟩
  change projectedLabel D a (block level c) jc z.2∈
    coarseMenu (2^(m-c)) (projectedLabel D a (block level m) jm z.2)
  unfold projectedLabel
  rw [block_mesh hdy (hcm.trans hml),block_mesh hdy hml]
  apply cellIndex_mem_coarseMenu (by positivity) _ (by positivity) (coarse_mesh_ratio c m hcm)
  · intro j
    have hh := same_parent_front_error D a (2^c) (by positivity) jm jc z.2 hp ht j
    have he : (1/((2^c:ℕ):ℝ))/64≤32/((2^c:ℕ):ℝ) := by
      have hp : (0:ℝ)<((2^c:ℕ):ℝ) := by positivity
      field_simp
      norm_num
    exact hh.trans he
  · rw [frontPoint_height,frontPoint_height]

/-- A fixed genuine fine parent/cell pair has at most 27 coarse images.
The parent ancestor is fixed, so only the physical cell menu is counted. -/
theorem pair_fiber_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) (v : Parent × Index) :
    ((E.filter (fun z => actualPair h R a level m z=v)).image
      (actualPair h R a level c)).card ≤ 27 := by
  have hsub : (E.filter (fun z => actualPair h R a level m z=v)).image
      (actualPair h R a level c) ⊆
        (coarseMenu (2^(m-c)) v.2).image (fun q => (ancestor m c v.1,q)) := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    obtain ⟨hz,hv⟩ := mem_filter.mp hz
    have hh := actual_pair_menu h original horiginal ha R level c m hdy hcm hml z
      (hR z hz) ((mem_incidences original z.1 z.2).mp (hE hz))
    rw [hv] at hh
    exact mem_image.mpr ⟨(actualPair h R a level c z).2,hh.2,Prod.ext hh.1.symm rfl⟩
  calc
    _ ≤ ((coarseMenu (2^(m-c)) v.2).image (fun q => (ancestor m c v.1,q))).card := card_le_card hsub
    _ ≤ (coarseMenu (2^(m-c)) v.2).card := card_image_le
    _ = 27 := coarseMenu_card _ _

/-- A fixed genuine coarse point has at most 27r^4 fine images. No spatial
occupancy or per-parent density enters this bound on the SAME original E. -/
theorem point_fiber_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) (q : Index) :
    ((E.filter (fun z => (actualPair h R a level c z).2=q)).image
      (fun z => (actualPair h R a level m z).2)).card ≤ 27*(2^(m-c))^4 := by
  rw [←fineMenu_card (2^(m-c)) (by positivity) q]
  apply card_le_card
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hz,hq⟩ := mem_filter.mp hz
  have hh := (actual_pair_menu h original horiginal ha R level c m hdy hcm hml z
    (hR z hz) ((mem_incidences original z.1 z.2).mp (hE hz))).2
  rw [hq] at hh
  exact coarse_mem_implies_fine_mem _ (by positivity) _ _ hh

/-- Actual coarse multiplicity interpolates to every finer dyadic depth.
Both numerator and support comparisons use the same original E witnesses. -/
theorem actual_multiplicity_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) :
    NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level c)) ≤
      (729:ℝ)*((2^(m-c):ℕ):ℝ)^4*
        NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level m)) := by
  have hcard : ((E.image (actualPair h R a level c)).card:ℝ) ≤
      27*((E.image (actualPair h R a level m)).card:ℝ) := by
    apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    intro v _hv
    exact_mod_cast pair_fiber_image_card_le h original horiginal ha R E hE hR level c m hdy hcm hml v
  have hsupp : ((E.image (fun z => (actualPair h R a level m z).2)).card:ℝ) ≤
      (27:ℝ)*((2^(m-c):ℕ):ℝ)^4*((E.image (fun z => (actualPair h R a level c z).2)).card:ℝ) := by
    apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    intro q _hq
    exact_mod_cast point_fiber_image_card_le h original horiginal ha R E hE hR level c m hdy hcm hml q
  by_cases hEn : E.Nonempty
  · have hsc : (0:ℝ)<(E.image (fun z => (actualPair h R a level c z).2)).card := by
      exact_mod_cast card_pos.mpr (hEn.image _)
    have hsm : (0:ℝ)<(E.image (fun z => (actualPair h R a level m z).2)).card := by
      exact_mod_cast card_pos.mpr (hEn.image _)
    simp only [NativeIncidenceMultiplicityTower.multiplicity,image_image,Function.comp_def]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hsc hsm).mpr
    calc
      _ ≤ (27*((E.image (actualPair h R a level m)).card:ℝ))*
          ((E.image (fun z => (actualPair h R a level m z).2)).card:ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ ≤ (27*((E.image (actualPair h R a level m)).card:ℝ))*
          ((27:ℝ)*((2^(m-c):ℕ):ℝ)^4*((E.image (fun z => (actualPair h R a level c z).2)).card:ℝ)) :=
        mul_le_mul_of_nonneg_left hsupp (by positivity)
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hEn]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- Physical same-source interpolation between arbitrary dyadic depths.
No ancestor population or output admissibility is assumed at either depth. -/
theorem full_source_multiplicity_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) :
    (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level c E)).toReal ≤
      (729:ℝ)*((2^(m-c):ℕ):ℝ)^4*
        (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal := by
  rw [full_source_multiplicity_real h R a level c E hR,
    full_source_multiplicity_real h R a level m E hR]
  exact actual_multiplicity_le h original horiginal ha R E hE hR level c m hdy hcm hml

end NativeCoarseScaleInterpolation
