import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_uniform_multiplicity_restriction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeLocalMenuInterpolation
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeDyadicParentCells
open SelfUniform NativeWeightedPointPopulations
open scoped BigOperators

/-- The scheduled relation records an actual original parent and the
unchanged original fine spatial cell. It is a relation on the single E. -/
def parentPointLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (z : Fin n × Index) : Parent × Index := (parentLabel D a N z.1,z.2)

def parentPointRel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (z w : Fin n × Index) : Prop := parentPointLabel D a N z = parentPointLabel D a N w

lemma parentPointRel_refl {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (z : Fin n × Index) : parentPointRel D a N z z := rfl

lemma parentPointRel_symm {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (z w : Fin n × Index) : parentPointRel D a N z w → parentPointRel D a N w z := Eq.symm

/-- Average incidence multiplicity on literal original spatial cells. -/
def edgeMultiplicity {n : ℕ} (E : Finset (Fin n × Index)) : ℝ :=
  (E.card : ℝ)/(E.image Prod.snd).card

lemma degree_eq_parent_point_weight {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (E : Finset (Fin n × Index)) (p : Parent)
    (z : Fin n × Index) (hz : parentLabel D a N z.1 = p) :
    degree (fun _ : Fin n × Index => 1) (parentPointRel D a N) E z =
      projectedWeight (fun _ : Fin n × Index => 1) Prod.snd (parentEdges D a N E p) z.2 := by
  rw [degree,projectedWeight,parentEdges,sum_filter]
  apply sum_congr rfl
  intro w _hw
  simp only [parentPointRel,parentPointLabel,Prod.mk.injEq,hz]
  by_cases hp : parentLabel D a N w.1 = p
  · simp only [hp,true_and,if_true]
    by_cases hc : z.2 = w.2
    · simp [hc]
    · simp [hc,Ne.symm hc]
  · simp [hp,Ne.symm hp]

/-- The single scheduled E-relation derives uniform point degrees in every
actual menu parent, rather than assuming a population law after restriction. -/
theorem parent_point_uniform {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N Q : ℕ) (E : Finset (Fin n × Index))
    (H : ∀ z w, z ∈ E → w ∈ E →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a N) E z ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a N) E w)
    (p : Parent) :
    ∀ x ∈ (parentEdges D a N E p).image Prod.snd,
      ∀ y ∈ (parentEdges D a N E p).image Prod.snd,
        projectedWeight (fun _ : Fin n × Index => 1) Prod.snd (parentEdges D a N E p) x ≤
          Q^2*projectedWeight (fun _ : Fin n × Index => 1) Prod.snd (parentEdges D a N E p) y := by
  intro x hx y hy
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
  obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
  obtain ⟨hwE,hwp⟩ := mem_filter.mp hw
  rw [←degree_eq_parent_point_weight D a N E p z hzp,
    ←degree_eq_parent_point_weight D a N E p w hwp]
  exact H z w hzE hwE

/-- Exact dyadic nesting on the SAME original incidences, including the
spatial cell coordinate. No new shading or local source is constructed. -/
lemma parentEdges_subset_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) {coarse fine : ℕ} (hcf : coarse ≤ fine) (q : Parent) :
    parentEdges D a (2^fine) E q ⊆
      parentEdges D a (2^coarse) E (ancestor fine coarse q) := by
  intro z hz
  obtain ⟨hzE,hzq⟩ := mem_filter.mp hz
  refine mem_filter.mpr ⟨hzE,?_⟩
  rw [←parent_ancestor_eq D a hcf z.1,hzq]

/-- A genuine restriction has controlled average multiplicity because the
ancestor's original point degrees are uniform. This is not monotonicity of
arbitrary shading restriction. -/
theorem subset_edgeMultiplicity {n : ℕ} (I J : Finset (Fin n × Index))
    (hJI : J ⊆ I) (Q : ℕ)
    (H : ∀ x ∈ I.image Prod.snd, ∀ y ∈ I.image Prod.snd,
      projectedWeight (fun _ : Fin n × Index => 1) Prod.snd I x ≤
        Q^2*projectedWeight (fun _ : Fin n × Index => 1) Prod.snd I y) :
    edgeMultiplicity J ≤ (Q:ℝ)^2*edgeMultiplicity I := by
  by_cases hJ : J.Nonempty
  · have hI : I.Nonempty := hJ.mono hJI
    have hIp : (0:ℝ) < (I.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hI.image Prod.snd)
    have hJp : (0:ℝ) < (J.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hJ.image Prod.snd)
    have hc := NativeUniformMultiplicityRestriction.subset_weighted_mass_cross
      (fun _ : Fin n × Index => 1) Prod.snd I J hJI (Q^2) H
    simp only [mass,sum_const,smul_eq_mul,mul_one] at hc
    rw [edgeMultiplicity,edgeMultiplicity,←mul_div_assoc]
    apply (div_le_div_iff₀ hJp hIp).mpr
    exact_mod_cast hc
  · rw [not_nonempty_iff_eq_empty.mp hJ]
    simp only [edgeMultiplicity,card_empty,Nat.cast_zero,image_empty,div_zero]
    positivity

/-- Every finer off-menu parent is controlled by its genuine menu ancestor.
Only the menu relation is uniformized; there is no off-menu input or profile
hypothesis and no refinement of R or E. -/
theorem off_menu_parent_multiplicity {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) (Q : ℕ) {coarse fine : ℕ} (hcf : coarse ≤ fine)
    (H : ∀ z w, z ∈ E → w ∈ E →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E z ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E w)
    (q : Parent) :
    edgeMultiplicity (parentEdges D a (2^fine) E q) ≤
      (Q:ℝ)^2*edgeMultiplicity (parentEdges D a (2^coarse) E (ancestor fine coarse q)) := by
  exact subset_edgeMultiplicity _ _ (parentEdges_subset_ancestor D a E hcf q) Q
    (parent_point_uniform D a (2^coarse) Q E H _)

/-- Direct readback from the scheduled native core: its arbitrary old
relation menu can include the parent/point relation at each chosen depth. -/
theorem core_off_menu_parent_multiplicity {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (a eta zeta : ℝ)
    (d g L : ℕ) (menu : Fin d → ℕ) (scales : Fin g → ℕ)
    (E : Finset (Fin n × Index))
    (hcore : IsCore D original R a eta zeta d g L
      (fun j => parentPointRel D a (2^(menu j))) scales E)
    (j : Fin d) (fine : ℕ) (hfine : menu j ≤ fine) (q : Parent) :
    edgeMultiplicity (parentEdges D a (2^fine) E q) ≤
      (coreRadix original R L:ℝ)^2*
        edgeMultiplicity (parentEdges D a (2^(menu j)) E (ancestor fine (menu j) q)) := by
  exact off_menu_parent_multiplicity D a E _ hfine (hcore.2.2.2.1 j) q

/-- The normalized actual local tube thickness at an integer depth. -/
def localScale (delta : ℝ) (depth : ℕ) : ℝ := ((2^depth:ℕ):ℝ)*delta/64

lemma localScale_pos {delta : ℝ} (hd : 0 < delta) (depth : ℕ) : 0 < localScale delta depth := by
  unfold localScale
  positivity

lemma localScale_ratio {delta : ℝ} (hd : 0 < delta) {coarse fine : ℕ} (hcf : coarse ≤ fine) :
    localScale delta fine / localScale delta coarse = ((2^(fine-coarse):ℕ):ℝ) := by
  have hp : (2:ℝ)^fine = (2:ℝ)^coarse*(2:ℝ)^(fine-coarse) := by
    rw [←pow_add,Nat.add_sub_of_le hcf]
  simp only [localScale,Nat.cast_pow,Nat.cast_ofNat]
  rw [hp]
  field_simp [hd.ne']

/-- A depth gap occupying at most tau of the original dyadic level costs
at most delta^(-tau), exactly, with no asymptotic or logarithmic premise. -/
lemma dyadic_gap_power {delta tau : ℝ} {level gap : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hgap : (gap:ℝ) ≤ tau*level) :
    ((2^gap:ℕ):ℝ) ≤ delta^(-tau) := by
  have he : delta^(-tau) = (2:ℝ)^((level:ℝ)*tau) := by
    rw [Real.rpow_neg_eq_inv_rpow,hdy,inv_pow,inv_inv,
      ←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [he,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith only [hgap]

lemma localScale_gap_power {delta tau : ℝ} {level coarse fine : ℕ}
    (hd : 0 < delta) (hdy : delta=(2:ℝ)⁻¹^level) (hcf : coarse ≤ fine)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ tau*level) :
    localScale delta fine / localScale delta coarse ≤ delta^(-tau) := by
  rw [localScale_ratio hd hcf]
  exact dyadic_gap_power hdy hgap

/-- Interpolation of the negative local-scale power pays precisely tau*s.
The menu depth precedes the requested off-menu depth. -/
lemma localScale_negative_power {delta tau s : ℝ} {level coarse fine : ℕ}
    (hd : 0 < delta) (hdy : delta=(2:ℝ)⁻¹^level) (hcf : coarse ≤ fine)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ tau*level) (hs : 0 ≤ s) :
    (localScale delta coarse)^(-s) ≤ delta^(-tau*s)*(localScale delta fine)^(-s) := by
  have hc := localScale_pos hd coarse
  have hf := localScale_pos hd fine
  have hpow := Real.rpow_le_rpow (div_pos hf hc).le (localScale_gap_power hd hdy hcf hgap) hs
  rw [←Real.rpow_mul hd.le] at hpow
  have hid : (localScale delta coarse)^(-s) =
      (localScale delta fine / localScale delta coarse)^s*(localScale delta fine)^(-s) := by
    rw [Real.div_rpow hf.le hc.le,Real.rpow_neg hc.le,Real.rpow_neg hf.le]
    field_simp [(Real.rpow_pos_of_pos hf s).ne',(Real.rpow_pos_of_pos hc s).ne']
  rw [hid]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_pos_of_pos hf _).le

/-- A menu-parent power upper bound transfers to any finer off-menu parent.
The only losses are Q^2 and the explicitly bounded scale gap. -/
theorem off_menu_parent_power_upper {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (E : Finset (Fin n × Index)) (Q : ℕ)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (tau theta s : ℝ)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ tau*level) (hs : 0 ≤ s)
    (H : ∀ z w, z ∈ E → w ∈ E →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E z ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E w)
    (hmenu : ∀ p, (parentEdges D a (2^coarse) E p).Nonempty →
      edgeMultiplicity (parentEdges D a (2^coarse) E p) ≤
        D.thickness^(-theta)*(localScale D.thickness coarse)^(-s)) (q : Parent) :
    edgeMultiplicity (parentEdges D a (2^fine) E q) ≤
      (Q:ℝ)^2*D.thickness^(-theta-tau*s)*(localScale D.thickness fine)^(-s) := by
  have hlocal := localScale_pos hd fine
  by_cases hq : (parentEdges D a (2^fine) E q).Nonempty
  · have hp := hq.mono (parentEdges_subset_ancestor D a E hcf q)
    calc
      _ ≤ (Q:ℝ)^2*edgeMultiplicity (parentEdges D a (2^coarse) E (ancestor fine coarse q)) :=
        off_menu_parent_multiplicity D a E Q hcf H q
      _ ≤ (Q:ℝ)^2*(D.thickness^(-theta)*(localScale D.thickness coarse)^(-s)) :=
        mul_le_mul_of_nonneg_left (hmenu _ hp) (sq_nonneg _)
      _ ≤ (Q:ℝ)^2*(D.thickness^(-theta)*
          (D.thickness^(-tau*s)*(localScale D.thickness fine)^(-s))) := by
        gcongr
        exact localScale_negative_power hd hdy hcf hgap hs
      _ = _ := by
        rw [←mul_assoc (D.thickness^(-theta)),←Real.rpow_add hd,
          show -theta + -tau*s = -theta-tau*s by ring]
        ring
  · rw [not_nonempty_iff_eq_empty.mp hq]
    simp only [edgeMultiplicity,card_empty,Nat.cast_zero,image_empty,div_zero]
    positivity

/-- Absorbing the scheduled core radix costs an additional gamma and no
new source assumptions at the off-menu scale. -/
theorem off_menu_parent_power_absorbed {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (E : Finset (Fin n × Index)) (Q : ℕ)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (tau theta gamma s : ℝ)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ tau*level) (hs : 0 ≤ s)
    (hQ : (Q:ℝ)^2 ≤ D.thickness^(-gamma))
    (H : ∀ z w, z ∈ E → w ∈ E →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E z ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^coarse)) E w)
    (hmenu : ∀ p, (parentEdges D a (2^coarse) E p).Nonempty →
      edgeMultiplicity (parentEdges D a (2^coarse) E p) ≤
        D.thickness^(-theta)*(localScale D.thickness coarse)^(-s)) (q : Parent) :
    edgeMultiplicity (parentEdges D a (2^fine) E q) ≤
      D.thickness^(-(theta+gamma+tau*s))*(localScale D.thickness fine)^(-s) := by
  have hlocal := localScale_pos hd fine
  have hh := off_menu_parent_power_upper D hd a E Q level hdy hcf tau theta s hgap hs H hmenu q
  apply hh.trans
  calc
    _ ≤ D.thickness^(-gamma)*D.thickness^(-theta-tau*s)*(localScale D.thickness fine)^(-s) := by
      gcongr
    _ = _ := by rw [←Real.rpow_add hd]; congr 2; ring

end NativeLocalMenuInterpolation
