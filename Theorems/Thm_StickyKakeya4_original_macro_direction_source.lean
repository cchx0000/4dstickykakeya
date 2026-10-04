import Theorems.Thm_StickyKakeya4_original_macro_direction_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalMacroDirectionSource
open Classical Finset TwoTubePathCollisionCount OriginalMacroDirectionCells
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- The literal pointwise angular realization, SINGLE original macro xi,
 original coarse Phi cover, and scheduled slope oscillation produce a joint
 scalar/transverse reference bound for every actual original incident tube. -/
theorem original_direction_reference_cover (I : Finset (P × T))
    (height : P → ℝ) (offset : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (u : T → ℝ) (v : T → ℝ × ℝ) (fine : P → Finset ℝ) (Phi : Finset ℝ)
    (F0 : ℝ →L[ℝ] ℝ × ℝ) (xi0 : ℝ × ℝ) {delta q DirErr Cxi L A : ℝ}
    (hq : 0 < q) (hdq : delta ≤ q) (hD : 0 ≤ DirErr) (hXi : 0 ≤ Cxi)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hF0 : ‖F0‖ ≤ A)
    (hreal : ∀ p t, (p,t) ∈ I → ∃ phi ∈ fine p,
      |u t-phi| ≤ DirErr*delta ∧ ‖v t-offset p-F (height p) phi‖ ≤ DirErr*delta)
    (hbox : ∀ p ∈ points I, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hPhi : ∀ p ∈ points I, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ q)
    (hxi : ∀ p ∈ points I, ‖offset p-xi0‖ ≤ Cxi*q)
    (hosc : ∀ p ∈ points I, ‖F (height p)-F0‖ ≤ L*q) :
    ∀ t ∈ tubes I, ∃ a ∈ Phi,
      |u t-a| ≤ (DirErr+Cxi+L+A+1)*q ∧
      ‖v t-xi0-F0 a‖ ≤ (DirErr+Cxi+L+A+1)*q := by
  intro t ht
  obtain ⟨e,he,het⟩ := mem_image.mp ht
  change e.2=t at het
  subst t
  have hp : e.1 ∈ points I := mem_image_of_mem _ he
  obtain ⟨phi,hphi,hu,hv⟩ := hreal e.1 e.2 he
  obtain ⟨a,ha,hpa⟩ := hPhi e.1 hp phi hphi
  have herror : DirErr*delta ≤ DirErr*q := mul_le_mul_of_nonneg_left hdq hD
  have hvar : ‖(F (height e.1)-F0) phi‖ ≤ L*q := by
    have hh := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hosc e.1 hp) (hbox e.1 hp phi hphi) (norm_nonneg _) (mul_nonneg hL hq.le))
    simpa only [mul_one] using hh
  have hbase : ‖F0 (phi-a)‖ ≤ A*q :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hF0 hpa (norm_nonneg _) hA)
  have hid : v e.2-xi0-F0 a=(v e.2-offset e.1-F (height e.1) phi)+
      (offset e.1-xi0)+(F (height e.1)-F0) phi+F0 (phi-a) := by
    rw [sub_apply,map_sub]
    abel
  refine ⟨a,ha,?_,?_⟩
  · have hh := (abs_sub_le (u e.2) phi a).trans (add_le_add hu hpa)
    nlinarith only [hh,herror,mul_nonneg hXi hq.le,mul_nonneg hL hq.le,mul_nonneg hA hq.le]
  · rw [hid]
    calc
      _ ≤ ‖(v e.2-offset e.1-F (height e.1) phi)+(offset e.1-xi0)+
          (F (height e.1)-F0) phi‖+‖F0 (phi-a)‖ := norm_add_le _ _
      _ ≤ (‖(v e.2-offset e.1-F (height e.1) phi)+(offset e.1-xi0)‖+
          ‖(F (height e.1)-F0) phi‖)+‖F0 (phi-a)‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ ((‖v e.2-offset e.1-F (height e.1) phi‖+‖offset e.1-xi0‖)+
          ‖(F (height e.1)-F0) phi‖)+‖F0 (phi-a)‖ :=
        add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
      _ ≤ _ := by nlinarith only [hv,hxi e.1 hp,hvar,hbase,herror,hq.le]
/-- Actual original incidence data supplies the full terminal alphabet used
 for genuine W collisions. There is no supplied direction-count certificate,
 and the original coarse Phi alphabet is allowed to be unseparated. -/
theorem original_full_terminal_population (I : Finset (P × T))
    (height : P → ℝ) (offset : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (u : T → ℝ) (v : T → ℝ × ℝ) (fine : P → Finset ℝ) (Phi : Finset ℝ)
    (F0 : ℝ →L[ℝ] ℝ × ℝ) (xi0 : ℝ × ℝ) {delta q DirErr Cxi L A K kappa : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hdq : delta ≤ q) (hD : 0 ≤ DirErr) (hXi : 0 ≤ Cxi)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hK : 0 ≤ K) (hF0 : ‖F0‖ ≤ A)
    (hreal : ∀ p t, (p,t) ∈ I → ∃ phi ∈ fine p,
      |u t-phi| ≤ DirErr*delta ∧ ‖v t-offset p-F (height p) phi‖ ≤ DirErr*delta)
    (hbox : ∀ p ∈ points I, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hPhi : ∀ p ∈ points I, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ q)
    (hxi : ∀ p ∈ points I, ‖offset p-xi0‖ ≤ Cxi*q)
    (hosc : ∀ p ∈ points I, ‖F (height p)-F0‖ ≤ L*q)
    (H : NativeScalarCoverAD.CoverADBounds Phi q K kappa)
    (hPhiBox : ∀ a ∈ Phi, |a| ≤ 1) :
    q^kappa*((directionCells (tubes I) (q/8) u v).card:ℝ) ≤
      2*K*(16*(DirErr+Cxi+L+2*A+2)+2)^3 := by
  have hc := original_direction_reference_cover I height offset F u v fine Phi F0 xi0
    hq hdq hD hXi hL hA hF0 hreal hbox hPhi hxi hosc
  have hh := literal_original_direction_mass (tubes I) u v Phi F0 xi0 hq hq1
    (show 0 ≤ DirErr+Cxi+L+A+1 by positivity) hA hK hF0 H hPhiBox hc
  simpa only [show (DirErr+Cxi+L+A+1)+A+1=DirErr+Cxi+L+2*A+2 by ring] using hh
end OriginalMacroDirectionSource
