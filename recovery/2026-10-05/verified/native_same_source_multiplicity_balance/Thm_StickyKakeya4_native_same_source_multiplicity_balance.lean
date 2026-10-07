import Theorems.Thm_StickyKakeya4_native_coarse_fine_multiplicity
import Theorems.Thm_StickyKakeya4_native_local_admission_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeSameSourceMultiplicityBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeIncidenceMultiplicityTower NativeCoarseFineMultiplicity
open scoped BigOperators ENNReal

lemma multiplicity_nonneg {T X : Type*} [DecidableEq X] (E : Finset (T × X)) :
    0 ≤ multiplicity E := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The exact cardinal retention of the selected original incidences is also
multiplicity retention, because their point support only shrinks. -/
lemma selected_multiplicity_retention {T X : Type*} [DecidableEq X]
    (I E : Finset (T × X)) (hE : E⊆I) (F : ℕ) (hF : 0 < F)
    (hret : I.card ≤ F*E.card) : multiplicity I ≤ (F:ℝ)*multiplicity E := by
  have hFr : (0:ℝ)<F := by exact_mod_cast hF
  have hretR : (I.card:ℝ) ≤ (F:ℝ)*(E.card:ℝ) := by exact_mod_cast hret
  have hh := retained_incidence_multiplicity I E hE
    (show (0:ℝ)≤(F:ℝ)⁻¹ by positivity)
    (show (F:ℝ)⁻¹*(I.card:ℝ) ≤ E.card by
      rw [←div_eq_inv_mul]
      exact (div_le_iff₀ hFr).mpr (by simpa only [mul_comm] using hretR))
  have hh' := mul_le_mul_of_nonneg_left hh hFr.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hFr.ne',one_mul] using hh'

/-- A near lower bound for the actual original source is retained on its
literal selected cubical incidence set E, including the exact finite cost. -/
theorem selected_source_near {n : ℕ} {D : FiniteScaleSource n} {eta kappa theta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (F : ℕ) (hF : 0<F)
    (hret : (incidences original).card ≤ F*E.card)
    (hnear : D.thickness^(-kappa+theta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal) :
    D.thickness^(-kappa+theta) ≤ (F:ℝ)*multiplicity E := by
  rw [source_multiplicity_real h original horiginal] at hnear
  exact hnear.trans (selected_multiplicity_retention (incidences original) E hE F hF hret)

/-- The formal incidence tower and a proved physical comparison are kept as
two distinct steps. The physical object is never identified with the tower. -/
lemma fine_le_coarse_from_parent_upper {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) {M B C : ℝ} (hM : 0 ≤ M)
    (hparent : ∀p∈E.image (fun z => f z.1),multiplicity (parent E f p) ≤ M)
    (hphysical : multiplicity (coarse E f) ≤ B*C) :
    multiplicity E ≤ (M*B)*C := by
  exact (multiplicity_le_parent_upper E f M hparent).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hphysical hM)

/-- One actual occupied original parent carries the reverse product bound.
Only the exact finite tower, selected fine lower bound and coarse upper are used. -/
lemma exists_parent_from_coarse_upper {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (hne : E.Nonempty)
    {L F B C U : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hnear : L ≤ F*multiplicity E)
    (hphysical : multiplicity (coarse E f) ≤ B*C) (hupper : C ≤ U) :
    ∃p∈E.image (fun z => f z.1),(parent E f p).Nonempty ∧
      L ≤ (F*B*U)*multiplicity (parent E f p) := by
  obtain ⟨p,hp,hpne,hprod⟩ := exists_parent_multiplicity_product E f hne
  refine ⟨p,hp,hpne,?_⟩
  calc
    _ ≤ F*multiplicity E := hnear
    _ ≤ F*(multiplicity (parent E f p)*multiplicity (coarse E f)) :=
      mul_le_mul_of_nonneg_left hprod hF
    _ ≤ F*(multiplicity (parent E f p)*(B*U)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hphysical.trans (mul_le_mul_of_nonneg_left hupper hB))
          (multiplicity_nonneg _)) hF
    _ = _ := by ring

/-- The actual padded coarse and local thicknesses multiply to the original
thickness exactly, with no unspecified normalization factor. -/
lemma actual_scale_product {delta : ℝ} {N : ℕ} (hN : 0<N) :
    (64/(N:ℝ))*((N:ℝ)*delta/64)=delta := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- Exact rpow cancellation for the complementary actual scales. -/
lemma complementary_power_identity {delta rho eps kappa theta loss : ℝ}
    (hd : 0 < delta) (hr : 0 < rho) (he : 0 < eps) (hscale : rho*eps=delta) :
    delta^(-kappa+theta) =
      (delta^theta*eps^loss*rho^(-kappa))*eps^(-kappa-loss) := by
  calc
    _ = delta^theta*delta^(-kappa) := by rw [←Real.rpow_add hd]; congr 1; ring
    _ = delta^theta*(rho^(-kappa)*eps^(-kappa)) := by
      congr 1
      rw [←hscale,Real.mul_rpow hr.le he.le]
    _ = _ := by
      have hc : eps^loss*eps^(-kappa-loss)=eps^(-kappa) := by
        rw [←Real.rpow_add he]
        congr 1
        ring
      rw [show (delta^theta*eps^loss*rho^(-kappa))*eps^(-kappa-loss)=
        (delta^theta*rho^(-kappa))*(eps^loss*eps^(-kappa-loss)) by ring,hc]
      ring

/-- Near extremality plus an upper bound at one complementary scale forces
a lower bound at the other, keeping the exact error-scale factor. -/
lemma complementary_lower {delta rho eps kappa theta loss C M : ℝ}
    (hd : 0 < delta) (hr : 0 < rho) (he : 0 < eps) (hscale : rho*eps=delta)
    (hbound : delta^(-kappa+theta) ≤ C*eps^(-kappa-loss)*M) :
    delta^theta*eps^loss*rho^(-kappa) ≤ C*M := by
  rw [complementary_power_identity hd hr he hscale] at hbound
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos he (-kappa-loss))).mp
    (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound)

/-- Moving the explicit original-density loss to the near lower exponent. -/
lemma move_density_loss {delta theta eta X C M : ℝ} (hd : 0 < delta)
    (hbound : delta^theta*X ≤ C*delta^(-eta)*M) :
    delta^(theta+eta)*X ≤ C*M := by
  have hh := mul_le_mul_of_nonneg_left hbound (Real.rpow_pos_of_pos hd eta).le
  have hcancel : delta^eta*delta^(-eta)=1 := by rw [←Real.rpow_add hd]; simp
  calc
    _ = delta^eta*(delta^theta*X) := by rw [←mul_assoc,←Real.rpow_add hd]; congr 1; ring
    _ ≤ delta^eta*(C*delta^(-eta)*M) := hh
    _ = C*M := by rw [show delta^eta*(C*delta^(-eta)*M)=(delta^eta*delta^(-eta))*(C*M) by ring,hcancel,one_mul]

def localCost : ℝ := 125*175616*16384
def balanceCost : ℝ := 125*localCost

/-- Explicit same-E physical coarse lower, once the actual geometric coarse
comparison and actual local-parent upper have been proved for this E. -/
theorem coarse_near_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) {delta rho eps kappa theta eta loss C : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (F rad : ℕ)
    (hnear : delta^(-kappa+theta) ≤ (F:ℝ)*multiplicity E)
    (hparent : ∀p∈E.image (fun z => f z.1),multiplicity (parent E f p) ≤
      localCost*(F:ℝ)*(rad:ℝ)^2*delta^(-eta)*eps^(-kappa-loss))
    (hphysical : multiplicity (coarse E f) ≤ 125*(rad:ℝ)^4*C) :
    delta^(theta+eta)*eps^loss*rho^(-kappa) ≤ balanceCost*(F:ℝ)^2*(rad:ℝ)^6*C := by
  have hlocal : 0 ≤ localCost*(F:ℝ)*(rad:ℝ)^2*delta^(-eta)*eps^(-kappa-loss) := by
    dsimp [localCost]
    positivity
  have hfine := fine_le_coarse_from_parent_upper E f hlocal hparent hphysical
  have hbound : delta^(-kappa+theta) ≤
      (balanceCost*(F:ℝ)^2*(rad:ℝ)^6*delta^(-eta))*eps^(-kappa-loss)*C := by
    exact (hnear.trans (mul_le_mul_of_nonneg_left hfine (Nat.cast_nonneg _))).trans_eq
      (by dsimp [balanceCost]; ring)
  have hc := complementary_lower hd hr he hscale hbound
  have hm := move_density_loss (theta:=theta) (eta:=eta)
    (C:=balanceCost*(F:ℝ)^2*(rad:ℝ)^6) (M:=C) (X:=eps^loss*rho^(-kappa)) hd
    (by simpa only [mul_assoc] using hc)
  simpa only [mul_assoc] using hm

/-- A full physical coarse upper forces a near-extremal original parent.
This parent is selected by the exact tower on the original E. -/
theorem exists_parent_near_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (hne : E.Nonempty)
    {delta rho eps kappa theta gamma loss C : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (F rad : ℕ)
    (hnear : delta^(-kappa+theta) ≤ (F:ℝ)*multiplicity E)
    (hphysical : multiplicity (coarse E f) ≤ 125*(rad:ℝ)^4*C)
    (hupper : C ≤ delta^(-gamma)*rho^(-kappa-loss)) :
    ∃p∈E.image (fun z => f z.1),(parent E f p).Nonempty ∧
      delta^(theta+gamma)*rho^loss*eps^(-kappa) ≤
        (125:ℝ)*(F:ℝ)*(rad:ℝ)^4*multiplicity (parent E f p) := by
  obtain ⟨p,hp,hpne,hprod⟩ := exists_parent_from_coarse_upper E f hne
    (Nat.cast_nonneg F) (by positivity) hnear hphysical hupper
  refine ⟨p,hp,hpne,?_⟩
  have hbound : delta^(-kappa+theta) ≤
      ((125:ℝ)*(F:ℝ)*(rad:ℝ)^4*delta^(-gamma))*rho^(-kappa-loss)*multiplicity (parent E f p) := by
    convert hprod using 1; ring
  have hc := complementary_lower hd he hr (by simpa only [mul_comm] using hscale) hbound
  have hm := move_density_loss (theta:=theta) (eta:=gamma)
    (C:=(125:ℝ)*(F:ℝ)*(rad:ℝ)^4) (M:=multiplicity (parent E f p)) (X:=rho^loss*eps^(-kappa)) hd
    (by simpa only [mul_assoc] using hc)
  simpa only [mul_assoc] using hm

end NativeSameSourceMultiplicityBalance
