import Theorems.Thm_StickyKakeya4_original_three_dimensional_unit_slabs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalUnitNormals
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitSlabs

def unitNormal (rho : ℝ) (d : DirectionLabel) : Point3 := fun i =>
  ![rho*d.2.1/normalLength rho d,rho*d.2.2/normalLength rho d,1/normalLength rho d] (d.1.symm i)

lemma original_unit_normal_square (rho : ℝ) (d : DirectionLabel) :
    ∑ i, (unitNormal rho d i)^2=1 := by
  rw [← Equiv.sum_comp d.1 (fun i => (unitNormal rho d i)^2)]
  simpa [unitNormal,Fin.sum_univ_three] using original_normal_coefficients_unit rho d

lemma original_unit_normal_dot (rho : ℝ) (d : DirectionLabel) (p : Point3) :
    (∑ i, unitNormal rho d i*p i)=unitValue rho d p := by
  rw [← Equiv.sum_comp d.1 (fun i => unitNormal rho d i*p i)]
  simp [unitNormal,Fin.sum_univ_three,unitValue,value,projection]
  ring

/-- Normalization does not identify two grid normals in a fixed chart. -/
theorem unit_normal_chart_injective (rho : ℝ) (hrho : 0<rho)
    (e : Equiv.Perm (Fin 3)) :
    Function.Injective (fun v : ℤ×ℤ => unitNormal rho (e,v)) := by
  intro a b he
  have h2 := congrFun he (e 2)
  have hL : normalLength rho (e,a)=normalLength rho (e,b) := by
    have hh : 1/normalLength rho (e,a)=1/normalLength rho (e,b) := by
      simpa [unitNormal] using h2
    simpa only [one_div,inv_inj] using hh
  have hLp : 0<normalLength rho (e,a) := lt_of_lt_of_le (by norm_num) (normal_length_one_le rho _)
  have h0 : rho*(a.1:ℝ)/normalLength rho (e,a)=rho*(b.1:ℝ)/normalLength rho (e,a) := by
    have hh := congrFun he (e 0)
    simpa [unitNormal,← hL] using hh
  have h1 : rho*(a.2:ℝ)/normalLength rho (e,a)=rho*(b.2:ℝ)/normalLength rho (e,a) := by
    have hh := congrFun he (e 1)
    simpa [unitNormal,← hL] using hh
  have h0' := (div_left_inj' hLp.ne').mp h0
  have h1' := (div_left_inj' hLp.ne').mp h1
  apply Prod.ext
  · have hh : (a.1:ℝ)=b.1 := (mul_left_cancel₀ hrho.ne') h0'
    exact_mod_cast hh
  · have hh : (a.2:ℝ)=b.2 := (mul_left_cancel₀ hrho.ne') h1'
    exact_mod_cast hh

/-- The only remaining chart duplication has multiplicity at most six. -/
theorem original_normal_label_count (rho : ℝ) (hrho : 0<rho) (S : Finset DirectionLabel) :
    S.card≤6*(S.image (unitNormal rho)).card := by
  let f : DirectionLabel→(Equiv.Perm (Fin 3))×Point3 := fun d => (d.1,unitNormal rho d)
  have hf : Function.Injective f := by
    rintro ⟨e,a⟩ ⟨g,b⟩ he
    have heg : e=g := congrArg Prod.fst he
    subst g
    have hn : unitNormal rho (e,a)=unitNormal rho (e,b) := congrArg Prod.snd he
    have hab := unit_normal_chart_injective rho hrho e hn
    simp only [hab]
  have hsub : S.image f⊆(Finset.univ : Finset (Equiv.Perm (Fin 3))).product (S.image (unitNormal rho)) := by
    intro v hv
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨d,hd,rfl⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hc
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin,show Nat.factorial 3=6 by decide] using hc

/-- The retained pair has many genuinely distinct oriented Euclidean
unit normals, after paying the actual finite chart multiplicity. -/
theorem retained_actual_unit_normals (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ)
    (hrho : 0<rho) (z : Pair3) (hz : z∈retainedPairs P G rho H) :
    1≤12*rho*((goodDirections P rho H z).image (unitNormal rho)).card := by
  have hh := (Finset.mem_filter.mp hz).2
  have hc := original_normal_label_count rho hrho (goodDirections P rho H z)
  have hcr : ((goodDirections P rho H z).card : ℝ)≤
      6*((goodDirections P rho H z).image (unitNormal rho)).card := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hcr (show 0≤2*rho by positivity)
  nlinarith only [hh,hm]

/-- Each actual retained unit normal has a literal original heavy source
slab through the original endpoints, with no representative approximation. -/
theorem original_unit_normal_heavy_witness (P : Finset Point3) (rho H : ℝ)
    (z : Pair3) (n : Point3) (hrho : 0≤rho)
    (hn : n∈(goodDirections P rho H z).image (unitNormal rho)) :
    (∑ i, (n i)^2)=1 ∧ ∃ c : ℝ, ∃ Q : Finset Point3, Q⊆P ∧
      H≤(Q.card : ℝ) ∧ z.1∈Q ∧ z.2∈Q ∧
      ∀ p∈Q, |(∑ i, n i*p i)-c|≤3*rho := by
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨k,hm,h1,h2,hslab⟩ := retained_direction_original_slab P rho H z d hrho hd
  refine ⟨original_unit_normal_square rho d,rho*k/normalLength rho d,
    slabPoints P rho d k,Finset.filter_subset _ _,hm,h1,h2,?_⟩
  intro p hp
  rw [original_unit_normal_dot]
  exact hslab p hp

end OriginalThreeDimensionalUnitNormals
