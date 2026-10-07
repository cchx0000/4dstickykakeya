import Theorems.Thm_StickyKakeya4_native_coarse_scale_interpolation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeCoarseScaleReverse
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeDyadicParentCells NativeCoarsePointMultiplicity
open NativeCoarseScaleInterpolation
open scoped BigOperators

/-- The exact r-by-r-by-r inverse menu of one original phase coordinate. -/
def phaseMenu (r : ℕ) (p : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun j => Icc ((r:ℤ)*p j) ((r:ℤ)*(p j+1)-1))

lemma phaseMenu_card (r : ℕ) (hr : 0 < r) (p : Fin 3 → ℤ) : (phaseMenu r p).card=r^3 := by
  have hrz : (0:ℤ)<r := by exact_mod_cast hr
  have hi (j : Fin 3) : (Icc ((r:ℤ)*p j) ((r:ℤ)*(p j+1)-1)).card=r := by
    have hh : ((Icc ((r:ℤ)*p j) ((r:ℤ)*(p j+1)-1)).card:ℤ)=r := by
      rw [Int.card_Icc_of_le _ _ (by nlinarith)]
      ring
    exact_mod_cast hh
  simp only [phaseMenu,Fintype.card_piFinset,hi,prod_const,card_univ,Fintype.card_fin]

/-- Both original slope and intercept coordinates retain their dyadic parent. -/
def parentMenu (r : ℕ) (p : Parent) : Finset Parent := (phaseMenu r p.1).product (phaseMenu r p.2)

lemma parentMenu_card (r : ℕ) (hr : 0 < r) (p : Parent) : (parentMenu r p).card=r^6 := by
  rw [parentMenu,Finset.product_eq_sprod,Finset.card_product,phaseMenu_card r hr,phaseMenu_card r hr]
  ring

lemma phase_mem_menu (r : ℕ) (hr : 0 < r) (p q : Fin 3 → ℤ)
    (hp : ∀j,q j/(r:ℤ)=p j) : q∈phaseMenu r p := by
  have hrz : (0:ℤ)<r := by exact_mod_cast hr
  apply Fintype.mem_piFinset.mpr
  intro j
  apply mem_Icc.mpr
  have hl := (Int.le_ediv_iff_mul_le hrz).mp (hp j).ge
  have hu := (Int.ediv_lt_iff_lt_mul hrz).mp (show q j/(r:ℤ)<p j+1 by rw [hp j]; omega)
  constructor <;> nlinarith

lemma parent_mem_menu (c m : ℕ) (p q : Parent) (hp : ancestor m c q=p) :
    q∈parentMenu (2^(m-c)) p := by
  apply mem_product.mpr
  constructor
  · exact phase_mem_menu _ (by positivity) _ _ (congrFun (congrArg Prod.fst hp))
  · exact phase_mem_menu _ (by positivity) _ _ (congrFun (congrArg Prod.snd hp))

/-- Above one actual coarse parent/cell pair there are at most r^6 phase
parents and 27r^4 fine point labels, using only original incidence witnesses. -/
theorem pair_fiber_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) (v : Parent × Index) :
    ((E.filter (fun z => actualPair h R a level c z=v)).image
      (actualPair h R a level m)).card ≤ 27*(2^(m-c))^10 := by
  have hsub : (E.filter (fun z => actualPair h R a level c z=v)).image
      (actualPair h R a level m) ⊆
        (parentMenu (2^(m-c)) v.1).product (fineMenu (2^(m-c)) v.2) := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    obtain ⟨hz,hv⟩ := mem_filter.mp hz
    have hh := actual_pair_menu h original horiginal ha R level c m hdy hcm hml z
      (hR z hz) ((mem_incidences original z.1 z.2).mp (hE hz))
    rw [hv] at hh
    exact mem_product.mpr ⟨parent_mem_menu c m _ _ hh.1.symm,
      coarse_mem_implies_fine_mem _ (by positivity) _ _ hh.2⟩
  calc
    _ ≤ ((parentMenu (2^(m-c)) v.1).product (fineMenu (2^(m-c)) v.2)).card := card_le_card hsub
    _ = _ := by rw [Finset.product_eq_sprod,Finset.card_product,parentMenu_card _ (by positivity),fineMenu_card _ (by positivity)]; ring

/-- A fixed actual fine point has at most 27 coarse point images. -/
theorem point_fiber_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) (q : Index) :
    ((E.filter (fun z => (actualPair h R a level m z).2=q)).image
      (fun z => (actualPair h R a level c z).2)).card ≤ 27 := by
  rw [←coarseMenu_card (2^(m-c)) q]
  apply card_le_card
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hz,hq⟩ := mem_filter.mp hz
  have hh := (actual_pair_menu h original horiginal ha R level c m hdy hcm hml z
    (hR z hz) ((mem_incidences original z.1 z.2).mp (hE hz))).2
  rwa [hq] at hh

/-- Crude reverse interpolation costs ten scale powers: six for actual
phase descendants and four for actual physical point descendants. -/
theorem actual_multiplicity_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) :
    NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level m)) ≤
      (729:ℝ)*((2^(m-c):ℕ):ℝ)^10*
        NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level c)) := by
  have hcard : ((E.image (actualPair h R a level m)).card:ℝ) ≤
      (27:ℝ)*((2^(m-c):ℕ):ℝ)^10*((E.image (actualPair h R a level c)).card:ℝ) := by
    apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    intro v _hv
    exact_mod_cast pair_fiber_image_card_le h original horiginal ha R E hE hR level c m hdy hcm hml v
  have hsupp : ((E.image (fun z => (actualPair h R a level c z).2)).card:ℝ) ≤
      (27:ℝ)*((E.image (fun z => (actualPair h R a level m z).2)).card:ℝ) := by
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
    apply (div_le_div_iff₀ hsm hsc).mpr
    calc
      _ ≤ ((27:ℝ)*((2^(m-c):ℕ):ℝ)^10*((E.image (actualPair h R a level c)).card:ℝ))*
          ((E.image (fun z => (actualPair h R a level c z).2)).card:ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ ≤ ((27:ℝ)*((2^(m-c):ℕ):ℝ)^10*((E.image (actualPair h R a level c)).card:ℝ))*
          ((27:ℝ)*((E.image (fun z => (actualPair h R a level m z).2)).card:ℝ)) :=
        mul_le_mul_of_nonneg_left hsupp (by positivity)
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hEn]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- Reverse physical interpolation on the same R and E, without output
native assumptions, ancestor occupancy, or off-menu uniformity. -/
theorem full_source_multiplicity_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level c m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hml : m ≤ level) :
    (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ≤
      (729:ℝ)*((2^(m-c):ℕ):ℝ)^10*
        (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level c E)).toReal := by
  rw [full_source_multiplicity_real h R a level c E hR,
    full_source_multiplicity_real h R a level m E hR]
  exact actual_multiplicity_le h original horiginal ha R E hE hR level c m hdy hcm hml

end NativeCoarseScaleReverse
