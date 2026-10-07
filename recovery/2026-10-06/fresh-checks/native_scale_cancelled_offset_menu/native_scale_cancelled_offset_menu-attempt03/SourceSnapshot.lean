import Theorems.Thm_StickyKakeya4_native_local_offset_menu
import Theorems.Thm_StickyKakeya4_canonical_angular_offset_geometry
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section

namespace NativeScaleCancelledOffsetMenu
open Classical Finset StickyKakeya4 NativeMatrixHeightWholePoint NativeLocalOffsetSelection
open NativeLocalOffsetMenu CanonicalConfiguredE4Bridge CanonicalAngularOffsetGeometry
open scoped BigOperators Matrix.Norms.Elementwise

/-- The common angular scale power cancels from the ACTUAL ceiling charge. -/
lemma ceiling_scale_cancel (ell : ℕ) {lower upper M kappa : ℝ}
    (hLower : 0 < lower) (hM : 0 < M) :
    ⌈((3:ℝ)^ell*(upper*M^kappa))/(lower*M^kappa)⌉₊=
      ⌈((3:ℝ)^ell*upper)/lower⌉₊ := by
  have hp : M^kappa≠0 := (Real.rpow_pos_of_pos hM _).ne'
  have hh : ((3:ℝ)^ell*(upper*M^kappa))/(lower*M^kappa)=((3:ℝ)^ell*upper)/lower := by
    field_simp [hLower.ne',hp]
  exact congrArg (fun x : ℝ => ⌈x⌉₊) hh

/-- At every working rho above the residual/base scale, the genuine A=2,
B=4 coordinate estimate has this fixed absolute constant. -/
lemma offset_width_le {E delta rho v : ℝ} (hrho : 0 < rho)
    (hE : E ≤ delta) (hscale : delta ≤ rho) (hv : v ≤ rho) :
    2*E+4/(64/rho)+8*v ≤ (161/16:ℝ)*rho := by
  have hdiv : (4:ℝ)/(64/rho)=rho/16 := by field_simp; norm_num
  rw [hdiv]
  linarith

/-- A complete prepared-menu consumer on literal incidence families.
The angular labels are floor(M theta) in E4, and the tangent/normal A=2,
B=4 readbacks are derived from the unchanged orthonormal chart. The common
M^kappa angular profile cancels before every maximum-weight selection.
The result retains every surviving original point's entire incidence fiber. -/
theorem select_actual_scale_menu {P T Cell : Type*}
    (s : Split) (K : ℕ) (S : Finset (P × T)) (theta : T → E4) (O : E4 ≃ₗᵢ[ℝ] E4)
    (physical : Fin K → P → Cell)
    (field : P → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (xi : P → Fin (normalDim s) → ℝ)
    (E delta lower upper kappa : ℝ) (rho v : Fin K → ℝ)
    (hE0 : 0 ≤ E) (hE : E ≤ delta) (hdelta : 0 < delta) (hLowerPos : 0 < lower)
    (hscale : ∀i,delta ≤ rho i) (hv0 : ∀i,0 ≤ v i) (hv : ∀i,v i ≤ rho i)
    (hTheta : ∀z∈S,‖theta z.2‖ ≤ 4)
    (hField : ∀p∈S.image Prod.fst,‖field p‖ ≤ (1/4:ℝ))
    (hVar : ∀i,∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,physical i p=physical i q →
      ‖field p-field q‖ ≤ v i)
    (hRes : ∀z∈S,‖affineResidual s O (theta z.2) (field z.1) (xi z.1)‖ ≤ E)
    (hLower : ∀i,∀p∈S.image Prod.fst,
      lower*((64/(rho i))^kappa) ≤
        (((S.filter (fun z => z.1=p)).image (fun z => angularKey (64/(rho i)) (theta z.2))).card:ℝ))
    (hUpper : ∀i c,
      (((physicalFiber S (physical i) c).image (fun z => angularKey (64/(rho i)) (theta z.2))).card:ℝ) ≤
        upper*((64/(rho i))^kappa)) :
    let N := ⌈((3:ℝ)^(normalDim s)*upper)/lower⌉₊
    ∃U,WholePoints S U ∧ S.card ≤ N^K*U.card ∧ (S.Nonempty → U.Nonempty) ∧
      ∀i,∀z∈U,∀u∈U,physical i z.1=physical i u.1 →
        ∀j,|xi z.1 j-xi u.1 j| ≤ (161/16:ℝ)*rho i := by
  intro N
  let M := fun i : Fin K => 64/(rho i)
  let angle := fun i t => angularKey (M i) (theta t)
  let tang := fun t => tangent s (O (theta t))
  let norm := fun t => normal s (O (theta t))
  have hrho (i : Fin K) : 0 < rho i := hdelta.trans_le (hscale i)
  have hM (i : Fin K) : 0 < M i := div_pos (by norm_num) (hrho i)
  have hTang : ∀z∈S,∀j,|tang z.2 j| ≤ 4 := by
    intro z hz j
    exact (chart_coordinates_bound s O (theta z.2) (hTheta z hz)).1 j
  have hF : ∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ) := by
    intro p hp i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm (field p) (i:=i) (j:=j)).trans (hField p hp)
  have hResCoord : ∀z∈S,∀i,|norm z.2 i-(∑j,field z.1 i j*tang z.2 j)-xi z.1 i| ≤ E := by
    intro z hz i
    have hh := (PiLp.norm_apply_le (affineResidual s O (theta z.2) (field z.1) (xi z.1)) i).trans (hRes z hz)
    simpa only [affineResidual,Real.norm_eq_abs] using hh
  have H : ∀i,LocalData S (angle i) (physical i) tang norm field xi
      E (M i) (v i) 2 4 (lower*(M i)^kappa) (upper*(M i)^kappa) := by
    intro i
    have imageBridge (Q : Finset (P × T)) :
        @Finset.image (P × T) (Fin 4 → ℤ) (fun a b => Classical.propDecidable (a=b))
          (fun z => angle i z.2) Q=
        @Finset.image (P × T) (Fin 4 → ℤ) (fun a b => Fintype.decidablePiFintype a b)
          (fun z => angle i z.2) Q :=
      congrArg (fun d : DecidableEq (Fin 4 → ℤ) =>
        @Finset.image (P × T) (Fin 4 → ℤ) d (fun z => angle i z.2) Q) (Subsingleton.elim _ _)
    refine ⟨hTang,hF,?_,?_,hResCoord,?_,?_⟩
    · intro p hp q hq heq a b
      have hh := (Matrix.norm_entry_le_entrywise_sup_norm (field p-field q) (i:=a) (j:=b)).trans
        (hVar i p hp q hq heq)
      simpa only [Matrix.sub_apply,Real.norm_eq_abs] using hh
    · intro z _hz u _hu ha
      exact chart_coordinates_close s O (M i) (hM i) (theta z.2) (theta u.2) ha
    · intro p hp
      have hh := hLower i p hp
      rw [←imageBridge] at hh
      exact hh
    · intro c
      have hh := hUpper i c
      rw [←imageBridge] at hh
      exact hh
  have hk : tangentDim s ≤ 2 := by cases s <;> decide
  obtain ⟨U,hWhole,hret,hne,hcoh⟩ := select_prepared_incidences univ S angle physical tang norm field xi
    (fun _ => E) M v (fun _ => 2) (fun _ => 4)
    (fun i => lower*(M i)^kappa) (fun i => upper*(M i)^kappa)
    hk (fun _ => hE0) hM hv0 (fun _ => by norm_num) (fun _ => by norm_num)
    (fun i => mul_pos hLowerPos (Real.rpow_pos_of_pos (hM i) _)) H
  have hcharge : (∏i : Fin K,⌈((3:ℝ)^(normalDim s)*(upper*(M i)^kappa))/(lower*(M i)^kappa)⌉₊)=N^K := by
    calc
      _ = ∏_i : Fin K,N := prod_congr rfl (fun i _ => ceiling_scale_cancel (normalDim s) hLowerPos (hM i))
      _ = _ := by simp
  rw [hcharge] at hret
  refine ⟨U,hWhole,hret,hne,?_⟩
  intro i z hz u hu heq j
  have hh := hcoh i (mem_univ i) z hz u hu heq j
  have hw := offset_width_le (hrho i) hE (hscale i) (hv i)
  exact hh.le.trans (by simpa only [M,show (2:ℝ)*2=4 by norm_num,show (2:ℝ)*4=8 by norm_num] using hw)

end NativeScaleCancelledOffsetMenu
