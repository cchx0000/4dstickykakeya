import Theorems.Thm_StickyKakeya4_native_active_phase_population
import Theorems.Thm_StickyKakeya4_native_local_pair_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativePopulationParentSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeActivePhasePopulation
open NativeMiddleWindowBalance
open scoped BigOperators

/-- Average actual incidence density against the complete R tube backbone.
This selects the population-rich parent rather than inferring its density
from relative incidence retention alone. -/
theorem exists_population_parent {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (a : ℝ) (N : ℕ) (mu : ℝ) (hmu : 0 < mu)
    (hglobal : mu*(R.card:ℝ) ≤ D.thickness*E.card) :
    ∃p∈R.image (parentLabel D a N),
      (R.filter (fun i => parentLabel D a N i=p)).Nonempty ∧
      (parentEdges D a N E p).Nonempty ∧
      mu*(R.filter (fun i => parentLabel D a N i=p)).card ≤
        D.thickness*(parentEdges D a N E p).card := by
  have hRn : R.Nonempty := by
    obtain ⟨z,hz⟩ := hEn
    exact ⟨z.1,(mem_filter.mp (hE hz)).2⟩
  have hsR : (∑p∈R.image (parentLabel D a N),
      ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))=(R.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image (parentLabel D a N) R).symm
  have hsE : (∑p∈R.image (parentLabel D a N),
      ((parentEdges D a N E p).card:ℝ))=(E.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s:=E) (t:=R.image (parentLabel D a N))
      (f:=fun z : Fin n × Index => parentLabel D a N z.1)
      (fun z hz => mem_image_of_mem _ (mem_filter.mp (hE hz)).2)).symm
  have hs : (∑p∈R.image (parentLabel D a N),
      mu*((R.filter (fun i => parentLabel D a N i=p)).card:ℝ)) ≤
      ∑p∈R.image (parentLabel D a N),D.thickness*((parentEdges D a N E p).card:ℝ) := by
    rw [←mul_sum,←mul_sum,hsR,hsE]
    exact hglobal
  obtain ⟨p,hp,hloc⟩ := exists_le_of_sum_le (hRn.image _) hs
  have hRp : (R.filter (fun i => parentLabel D a N i=p)).Nonempty := by
    obtain ⟨i,hi,hip⟩ := mem_image.mp hp
    exact ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩
  have hEp : (parentEdges D a N E p).Nonempty := by
    have hpos : 0 < mu*((R.filter (fun i => parentLabel D a N i=p)).card:ℝ) :=
      mul_pos hmu (Nat.cast_pos.mpr (card_pos.mpr hRp))
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,card_empty,Nat.cast_zero,mul_zero] at hloc
    linarith
  exact ⟨p,hp,hRp,hEp,hloc⟩

/-- A source-derived population density also retains every reference subset
of the same original R-parent, using only the proved upper row capacity. -/
lemma population_implies_reference_retention {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ)
    (I E : Finset (Fin n × Index)) (hI : I⊆retained original R)
    (p : Parent) (mu : ℝ) (hmu : 0 ≤ mu)
    (hpop : mu*(R.filter (fun i => parentLabel D a N i=p)).card ≤
      D.thickness*(parentEdges D a N E p).card) :
    (mu/rowConstant)*(parentEdges D a N I p).card ≤ (parentEdges D a N E p).card := by
  have hd := h.1.2.1
  have hc := parent_incidence_capacity h original horiginal R a N I hI p
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ rowConstant_pos).mpr
  apply (mul_le_mul_iff_right₀ hd).mp
  calc
    _ = mu*(D.thickness*(parentEdges D a N I p).card) := by ring
    _ ≤ mu*(rowConstant*(R.filter (fun i => parentLabel D a N i=p)).card) :=
      mul_le_mul_of_nonneg_left hc hmu
    _ = rowConstant*(mu*(R.filter (fun i => parentLabel D a N i=p)).card) := by ring
    _ ≤ rowConstant*(D.thickness*(parentEdges D a N E p).card) :=
      mul_le_mul_of_nonneg_left hpop rowConstant_pos.le
    _ = _ := by ring

/-- All population density is produced from native total shading density,
the first and second actual selection costs, and the mixed cleanup's actual
retained incidence mass. No parent density is a public premise. -/
theorem source_population_parent {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (hsmall : D.thickness ≤ 1/8) (R : Finset (Fin n))
    (E1 E2 H : Finset (Fin n × Index)) (h1R : E1⊆retained original R)
    (h21 : E2⊆E1) (hH2 : H⊆E2) (hHn : H.Nonempty)
    (F1 G W : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hW : 0 < W)
    (hfirst : (incidences original).card ≤ F1*E1.card)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsecond : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (hhalf : W ≤ 2*H.card) (m : ℕ) :
    let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
    let mu := theta*D.thickness^eta
    0 < theta ∧ 0 < mu ∧ ∃p∈R.image (parentLabel D a (2^m)),
      (parentEdges D a (2^m) H p).Nonempty ∧
      mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
        D.thickness*(parentEdges D a (2^m) H p).card ∧
      ∀I⊆retained original R,
        (mu/rowConstant)*(parentEdges D a (2^m) I p).card ≤
          (parentEdges D a (2^m) H p).card := by
  intro theta mu
  have hd := h.1.2.1
  have hE2n : E2.Nonempty := hHn.mono hH2
  have hE2r : (0:ℝ)<E2.card := Nat.cast_pos.mpr (card_pos.mpr hE2n)
  have hF1r : (0:ℝ)<F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hWr : (0:ℝ)<W := by exact_mod_cast hW
  have hden : 0 < 2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ) := by positivity
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hmu : 0 < mu := mul_pos ht (Real.rpow_pos_of_pos hd _)
  have hRn : (R.card:ℝ) ≤ n := by exact_mod_cast (show R.card ≤ n by simpa only [Fintype.card_fin] using card_le_univ R)
  have hbase : D.thickness^eta*(R.card:ℝ) ≤ D.thickness*(incidences original).card :=
    (mul_le_mul_of_nonneg_left hRn (Real.rpow_pos_of_pos hd _).le).trans
      (NativeLocalPairFibers.original_incidence_lower_weak h original horiginal hsmall)
  have hfirstR : ((incidences original).card:ℝ) ≤ (F1:ℝ)*E1.card := by exact_mod_cast hfirst
  have hhalfR : (W:ℝ) ≤ 2*(H.card:ℝ) := by exact_mod_cast hhalf
  have hcross : (lambda*(W:ℝ))*(D.thickness^eta*(R.card:ℝ)) ≤
      (D.thickness*H.card)*(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ)) := by
    calc
      _ ≤ (lambda*(W:ℝ))*(D.thickness*(incidences original).card) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ (lambda*(W:ℝ))*(D.thickness*((F1:ℝ)*E1.card)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfirstR hd.le) (by positivity)
      _ = ((W:ℝ)*D.thickness*(F1:ℝ))*(lambda*E1.card) := by ring
      _ ≤ ((W:ℝ)*D.thickness*(F1:ℝ))*((G:ℝ)*E2.card) :=
        mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = (D.thickness*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))*(W:ℝ) := by ring
      _ ≤ (D.thickness*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))*(2*(H.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hhalfR (by positivity)
      _ = _ := by ring
  have hglobal : mu*(R.card:ℝ) ≤ D.thickness*H.card := by
    dsimp [mu,theta]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_assoc] using hcross
  have hHR : H⊆retained original R := hH2.trans (h21.trans h1R)
  obtain ⟨p,hp,_hRp,hHp,hpop⟩ := exists_population_parent D original R H hHR hHn a (2^m) mu hmu hglobal
  refine ⟨ht,hmu,p,hp,hHp,hpop,?_⟩
  intro I hIR
  exact population_implies_reference_retention h original horiginal R a (2^m) I H hIR p mu hmu.le hpop

end NativePopulationParentSelection
