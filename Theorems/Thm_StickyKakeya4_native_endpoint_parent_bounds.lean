import Theorems.Thm_StickyKakeya4_native_scale_menu_successor
import Theorems.Thm_StickyKakeya4_native_coarse_scale_reverse

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeEndpointParentBounds
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeDyadicParentCells
open NativeIncidenceMultiplicityTower NativeLocalMenuInterpolation NativeScaleMenuSuccessor
open NativeCoarseScaleReverse
open scoped BigOperators

lemma one_le_multiplicity {T X : Type*} [DecidableEq X]
    (I : Finset (T × X)) (hne : I.Nonempty) : 1 ≤ multiplicity I := by
  have hs : (0:ℝ) < (I.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  apply (le_div_iff₀ hs).mpr
  simpa only [one_mul] using (show ((I.image Prod.snd).card:ℝ) ≤ I.card by
    exact_mod_cast (card_image_le (s:=I) (f:=Prod.snd)))

/-- The average incidence degree never exceeds the number of tube labels. -/
lemma multiplicity_le_tube_card {T X : Type*} [DecidableEq T] [DecidableEq X]
    (I : Finset (T × X)) : multiplicity I ≤ (I.image Prod.fst).card := by
  have hsub : I ⊆ (I.image Prod.fst).product (I.image Prod.snd) := by
    intro z hz
    exact mem_product.mpr ⟨mem_image_of_mem _ hz,mem_image_of_mem _ hz⟩
  have hc : I.card ≤ (I.image Prod.fst).card*(I.image Prod.snd).card := by
    simpa only [Finset.product_eq_sprod,Finset.card_product] using card_le_card hsub
  by_cases hne : I.Nonempty
  · have hs : (0:ℝ) < (I.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hne.image Prod.snd)
    exact (div_le_iff₀ hs).mpr (by exact_mod_cast hc)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- The literal finer labels of an original parent lie in the exact
six-dimensional dyadic descendant menu. -/
lemma active_descendants_card_le {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) {coarse fine : ℕ} (hcf : coarse ≤ fine) (p : Parent) :
    ((parentEdges D a (2^coarse) E p).image
      (fun z => parentLabel D a (2^fine) z.1)).card ≤ (2^(fine-coarse))^6 := by
  have hsub : (parentEdges D a (2^coarse) E p).image
      (fun z => parentLabel D a (2^fine) z.1) ⊆ parentMenu (2^(fine-coarse)) p := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    apply parent_mem_menu coarse fine
    exact (parent_ancestor_eq D a hcf z.1).trans (mem_filter.mp hz).2
  exact (card_le_card hsub).trans_eq (parentMenu_card _ (by positivity) p)

/-- Coarse original parents have at most r^6 active finer children.
Summing child upper bounds uses only literal incidence and support counts. -/
theorem old_parent_upper_from_children {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) {coarse fine : ℕ} (hcf : coarse ≤ fine)
    (M : ℝ) (hM : 0 ≤ M)
    (H : ∀ q,(parentEdges D a (2^fine) E q).Nonempty →
      edgeMultiplicity (parentEdges D a (2^fine) E q) ≤ M) (p : Parent) :
    edgeMultiplicity (parentEdges D a (2^coarse) E p) ≤
      (((2^(fine-coarse):ℕ):ℝ)^6)*M := by
  let I := parentEdges D a (2^coarse) E p
  let f := parentLabel D a (2^fine)
  have hchildren : ∀ q∈I.image (fun z => f z.1),multiplicity (parent I f q) ≤ M := by
    intro q hq
    have hqn := parent_nonempty I f hq
    change (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q).Nonempty at hqn
    have he := nested_parentEdges_eq D a E hcf p q hqn
    change edgeMultiplicity (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q) ≤ M
    rw [he]
    exact H q (he ▸ hqn)
  have hcount : ((I.image (fun z => f z.1)).card:ℝ) ≤ ((2^(fine-coarse):ℕ):ℝ)^6 := by
    exact_mod_cast active_descendants_card_le D a E hcf p
  have hcoarse := multiplicity_le_tube_card (NativeIncidenceMultiplicityTower.coarse I f)
  rw [coarse_parents] at hcoarse
  have hprod := multiplicity_le_parent_upper I f M hchildren
  exact hprod.trans ((mul_le_mul_of_nonneg_left (hcoarse.trans hcount) hM).trans_eq (by ring))

lemma localScale_mono {delta : ℝ} (hd : 0 ≤ delta) {coarse fine : ℕ} (hcf : coarse ≤ fine) :
    localScale delta coarse ≤ localScale delta fine := by
  have hp : (2:ℝ)^coarse ≤ (2:ℝ)^fine := pow_le_pow_right₀ (by norm_num) hcf
  simpa only [localScale,Nat.cast_pow,Nat.cast_ofNat] using
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hd) (by norm_num : (0:ℝ)≤64)

/-- Original-parent upper interpolation toward the coarse endpoint pays
six scale powers, with no point-uniformity premise at either depth. -/
theorem old_parent_power_upper_from_children {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (E : Finset (Fin n × Index))
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (gap b s : ℝ)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ gap*level) (hs : 0 ≤ s)
    (H : ∀ q,(parentEdges D a (2^fine) E q).Nonempty →
      edgeMultiplicity (parentEdges D a (2^fine) E q) ≤
        D.thickness^(-b)*(localScale D.thickness fine)^(-s)) (p : Parent) :
    edgeMultiplicity (parentEdges D a (2^coarse) E p) ≤
      D.thickness^(-(b+6*gap))*(localScale D.thickness coarse)^(-s) := by
  have hc := localScale_pos hd coarse
  have hf := localScale_pos hd fine
  have hr := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
  have hr6 : ((2^(fine-coarse):ℕ):ℝ)^6 ≤ D.thickness^(-(6*gap)) := by
    calc
      _ ≤ (D.thickness^(-gap))^6 := pow_le_pow_left₀ (by positivity) hr 6
      _ = _ := by rw [←Real.rpow_mul_natCast hd.le]; congr 1; ring
  have heps := Real.rpow_le_rpow_of_nonpos hc (localScale_mono hd.le hcf) (neg_nonpos.mpr hs)
  have hmu := old_parent_upper_from_children D a E hcf _
    (mul_nonneg (Real.rpow_pos_of_pos hd _).le (Real.rpow_pos_of_pos hf _).le) H p
  apply hmu.trans
  calc
    _ ≤ D.thickness^(-(6*gap))*(D.thickness^(-b)*(localScale D.thickness coarse)^(-s)) := by
      gcongr
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring

/-- Pure direction packing bounds every retained original parent, even
when the selected incidences give it a highly nonuniform shading. -/
theorem old_parent_geometric_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1) (p : Parent) :
    edgeMultiplicity (parentEdges D a N E p) ≤ 5832*(1/((N:ℝ)*D.thickness))^3 := by
  have hsub : (parentEdges D a N E p).image Prod.fst ⊆
      R.filter (fun i => parentLabel D a N i=p) := by
    intro i hi
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨hR z (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩
  have hc : (((parentEdges D a N E p).image Prod.fst).card:ℝ) ≤
      (R.filter (fun i => parentLabel D a N i=p)).card := by exact_mod_cast card_le_card hsub
  exact (multiplicity_le_tube_card _).trans (hc.trans
    (NativeOriginalSlopeCubePacking.native_retained_parent_card_le h R a N hN hscale p))

lemma inverse_relative_scale {delta : ℝ} (level m : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    1/(((2^m:ℕ):ℝ)*delta)=((2^(level-m):ℕ):ℝ) := by
  rw [NativeLocalParentScales.relative_scale hdy hm]
  simp only [one_div,inv_pow,inv_inv,Nat.cast_pow,Nat.cast_ofNat]

lemma localScale_inverse_remaining {delta : ℝ} (level m : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    (localScale delta m)⁻¹=64*((2^(level-m):ℕ):ℝ) := by
  have hh := inverse_relative_scale level m hdy hm
  change ((((2^m:ℕ):ℝ)*delta)/64)⁻¹=_
  rw [inv_div]
  calc
    _ = 64*(1/(((2^m:ℕ):ℝ)*delta)) := by ring
    _ = _ := by rw [hh]

lemma localScale_le_one {delta : ℝ} (level m : ℕ)
    (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) : localScale delta m ≤ 1 := by
  have hs : ((2^m:ℕ):ℝ)*delta ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  change (((2^m:ℕ):ℝ)*delta)/64 ≤ 1
  linarith

/-- At the fine endpoint the negative local power is bounded by the
remaining depth alone; kappa≤3 pays at most three such powers. -/
lemma local_negative_power_le_remaining {delta s : ℝ} (hd : 0 < delta)
    (level m : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (hm : m ≤ level) (hs : s ≤ 3) :
    (localScale delta m)^(-s) ≤ (64:ℝ)^3*((2^(level-m):ℕ):ℝ)^3 := by
  have he := localScale_pos hd m
  calc
    _ ≤ (localScale delta m)^(-(3:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge he (localScale_le_one level m hdy hm) (by linarith)
    _ = _ := by
      rw [Real.rpow_neg he.le,Real.rpow_ofNat,←inv_pow,localScale_inverse_remaining level m hdy hm]
      ring

theorem old_parent_dyadic_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) (a : ℝ)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (p : Parent) :
    edgeMultiplicity (parentEdges D a (2^m) E p) ≤ 5832*((2^(level-m):ℕ):ℝ)^3 := by
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  simpa only [inverse_relative_scale level m hdy hm] using
    old_parent_geometric_upper h R E hR a (2^m) (by positivity) hscale p

lemma one_le_full_multiplicity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) (hne : E.Nonempty)
    (a : ℝ) (level m : ℕ) :
    1 ≤ (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal := by
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level m E hR]
  exact one_le_multiplicity _ (hne.image _)

end NativeEndpointParentBounds
