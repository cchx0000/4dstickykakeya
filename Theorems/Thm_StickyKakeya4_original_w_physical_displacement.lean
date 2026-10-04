import Theorems.Thm_StickyKakeya4_original_w_witness_counts
import Theorems.Thm_StickyKakeya4_finite_transverse_menu_growth
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalWPhysicalDisplacement
open OriginalWWitnessCounts Classical
noncomputable section

variable {P T K E : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A graph-incidence residual, expressed using ORIGINAL point coordinates,
actual height, tube intercept, and tube slope. -/
def incidenceResidual (height : P → ℝ) (position : P → E) (base slope : T → E)
    (p : P) (t : T) : E := position p-base t-height p • slope t

def pathResidual (height : P → ℝ) (position : P → E) (slope : T → E)
    (a : Path P T) : E := position a.point₂-position a.point₀-
      (height a.point₁-height a.point₀) • slope a.tube₁-
      (height a.point₂-height a.point₁) • slope a.tube₂

omit [DecidableEq P] [DecidableEq T] in
theorem incidence_chord_error (I : Finset (P × T)) (height : P → ℝ)
    (position : P → E) (base slope : T → E) {epsilon : ℝ}
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    {p q : P} {t : T} (hp : (p,t) ∈ I) (hq : (q,t) ∈ I) :
    ‖position q-position p-(height q-height p) • slope t‖ ≤ 2*epsilon := by
  calc
    ‖position q-position p-(height q-height p) • slope t‖ =
        ‖incidenceResidual height position base slope q t-
          incidenceResidual height position base slope p t‖ := by
      congr 1
      dsimp [incidenceResidual]
      module
    _ ≤ ‖incidenceResidual height position base slope q t‖+
          ‖incidenceResidual height position base slope p t‖ := norm_sub_le _ _
    _ ≤ epsilon+epsilon := add_le_add (hinc q t hq) (hinc p t hp)
    _ = 2*epsilon := by ring

theorem path_residual_bound (I : Finset (P × T)) (height : P → ℝ)
    (position : P → E) (base slope : T → E) {epsilon : ℝ}
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (a : Path P T) (ha : a ∈ TwoTubePathCollisionCount.paths I) :
    ‖pathResidual height position slope a‖ ≤ 4*epsilon := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (TwoTubePathCollisionCount.mem_paths I a).mp ha
  have hfirst := incidence_chord_error I height position base slope hinc h₀ h₁
  have hsecond := incidence_chord_error I height position base slope hinc h₂ h₃
  calc
    ‖pathResidual height position slope a‖ =
        ‖(position a.point₁-position a.point₀-(height a.point₁-height a.point₀) • slope a.tube₁)+
          (position a.point₂-position a.point₁-(height a.point₂-height a.point₁) • slope a.tube₂)‖ := by
      congr 1
      dsimp [pathResidual]
      abel
    _ ≤ ‖position a.point₁-position a.point₀-(height a.point₁-height a.point₀) • slope a.tube₁‖+
          ‖position a.point₂-position a.point₁-(height a.point₂-height a.point₁) • slope a.tube₂‖ := norm_add_le _ _
    _ ≤ 4*epsilon := by linarith

/-- Exact path-pair algebra with the actual shared start and heights recovered
from the original collision label. Equal and reversed times remain allowed. -/
theorem witness_two_leg_residual (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (position : P → E) (base slope : T → E) {epsilon : ℝ}
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell) :
    ‖position w.2.point₂-position w.1.point₂-
      (height w.1.point₁-height w.1.point₀) • (slope w.2.tube₁-slope w.1.tube₁)-
      (height w.1.point₂-height w.1.point₁) • (slope w.2.tube₂-slope w.1.tube₂)‖ ≤ 8*epsilon := by
  obtain ⟨ha,hb,hp,hz₁,hz₂,_hc⟩ := witness_conditions I height cell hw
  have he₁ := path_residual_bound I height position base slope hinc w.1 ha
  have he₂ := path_residual_bound I height position base slope hinc w.2 hb
  calc
    ‖position w.2.point₂-position w.1.point₂-
      (height w.1.point₁-height w.1.point₀) • (slope w.2.tube₁-slope w.1.tube₁)-
      (height w.1.point₂-height w.1.point₁) • (slope w.2.tube₂-slope w.1.tube₂)‖ =
        ‖pathResidual height position slope w.2-pathResidual height position slope w.1‖ := by
      congr 1
      dsimp [pathResidual]
      rw [hp,hz₁,hz₂]
      module
    _ ≤ ‖pathResidual height position slope w.2‖+‖pathResidual height position slope w.1‖ := norm_sub_le _ _
    _ ≤ 8*epsilon := by linarith

omit [NormedSpace ℝ E] in
theorem difference_approximation_bound (u₁ u₂ c₁ c₂ : E) {rho : ℝ}
    (h₁ : ‖u₁-c₁‖ ≤ rho) (h₂ : ‖u₂-c₂‖ ≤ rho) :
    ‖(u₂-u₁)-(c₂-c₁)‖ ≤ 2*rho := by
  calc
    ‖(u₂-u₁)-(c₂-c₁)‖ = ‖(u₂-c₂)-(u₁-c₁)‖ := by congr 1; abel
    _ ≤ ‖u₂-c₂‖+‖u₁-c₁‖ := norm_sub_le _ _
    _ ≤ 2*rho := by linarith

/-- Derive the coarse tangential displacement for the ACTUAL witness endpoints.
The angular premises below are literal grid-width consequences in the native
wrappers, not assumed endpoint-displacement or neighborhood certificates. -/
theorem witness_coarse_displacement (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (position : P → E) (base slope coarse : T → E)
    {epsilon rho : ℝ} (hrho : 0 ≤ rho)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (htime₁ : |height w.1.point₁-height w.1.point₀| ≤ rho)
    (htime₂ : |height w.1.point₂-height w.1.point₁| ≤ rho)
    (hgrid₁ : ‖slope w.1.tube₁-coarse w.1.tube₁‖ ≤ rho)
    (hgrid₂ : ‖slope w.2.tube₁-coarse w.2.tube₁‖ ≤ rho)
    (hterminal : ‖slope w.2.tube₂-slope w.1.tube₂‖ ≤ rho) :
    ‖position w.2.point₂-position w.1.point₂-
      (height w.1.point₁-height w.1.point₀) • (coarse w.2.tube₁-coarse w.1.tube₁)‖ ≤
        3*rho^2+8*epsilon := by
  have hres := witness_two_leg_residual I height cell position base slope hinc w hw
  have hdiff := difference_approximation_bound _ _ _ _ hgrid₁ hgrid₂
  have hterminalTerm : ‖(height w.1.point₂-height w.1.point₁) •
      (slope w.2.tube₂-slope w.1.tube₂)‖ ≤ rho^2 := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ rho*rho := mul_le_mul htime₂ hterminal (norm_nonneg _) hrho
      _ = rho^2 := by ring
  have hgridTerm : ‖(height w.1.point₁-height w.1.point₀) •
      ((slope w.2.tube₁-slope w.1.tube₁)-(coarse w.2.tube₁-coarse w.1.tube₁))‖ ≤ 2*rho^2 := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ rho*(2*rho) := mul_le_mul htime₁ hdiff (norm_nonneg _) hrho
      _ = 2*rho^2 := by ring
  let R := position w.2.point₂-position w.1.point₂-
      (height w.1.point₁-height w.1.point₀) • (slope w.2.tube₁-slope w.1.tube₁)-
      (height w.1.point₂-height w.1.point₁) • (slope w.2.tube₂-slope w.1.tube₂)
  let S := (height w.1.point₂-height w.1.point₁) • (slope w.2.tube₂-slope w.1.tube₂)
  let G := (height w.1.point₁-height w.1.point₀) •
      ((slope w.2.tube₁-slope w.1.tube₁)-(coarse w.2.tube₁-coarse w.1.tube₁))
  calc
    ‖position w.2.point₂-position w.1.point₂-
      (height w.1.point₁-height w.1.point₀) • (coarse w.2.tube₁-coarse w.1.tube₁)‖ = ‖(R+S)+G‖ := by
      congr 1
      dsimp [R,S,G]
      module
    _ ≤ (‖R‖+‖S‖)+‖G‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 3*rho^2+8*epsilon := by dsimp [R,S,G]; linarith

omit [DecidableEq P] [DecidableEq T] in
theorem same_tube_same_height_error (I : Finset (P × T)) (height : P → ℝ)
    (position : P → E) (base slope : T → E) {epsilon : ℝ}
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    {p q : P} {t : T} (hp : (p,t) ∈ I) (hq : (q,t) ∈ I) (hz : height q=height p) :
    ‖position q-position p‖ ≤ 2*epsilon := by
  have he := incidence_chord_error I height position base slope hinc hp hq
  simpa only [hz,sub_self,zero_smul,sub_zero] using he

/-- Replace actual terminal endpoints by fixed ORIGINAL incident representatives.
Their displacement error is derived from the common tube and exact old height. -/
theorem fixed_representative_displacement (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (position : P → E) (base slope coarse : T → E)
    {epsilon rho : ℝ} (hrho : 0 ≤ rho)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height position base slope p t‖ ≤ epsilon)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂)
    (htime₁ : |height w.1.point₁-height w.1.point₀| ≤ rho)
    (htime₂ : |height w.1.point₂-height w.1.point₁| ≤ rho)
    (hgrid₁ : ‖slope w.1.tube₁-coarse w.1.tube₁‖ ≤ rho)
    (hgrid₂ : ‖slope w.2.tube₁-coarse w.2.tube₁‖ ≤ rho)
    (hterminal : ‖slope w.2.tube₂-slope w.1.tube₂‖ ≤ rho) :
    ‖position p₂-position p₁-
      (height w.1.point₁-height w.1.point₀) • (coarse w.2.tube₁-coarse w.1.tube₁)‖ ≤
        3*rho^2+12*epsilon := by
  have hm := witness_conditions I height cell hw
  have hfirst := (TwoTubePathCollisionCount.mem_paths I w.1).mp hm.1
  have hsecond := (TwoTubePathCollisionCount.mem_paths I w.2).mp hm.2.1
  have he₁ := same_tube_same_height_error I height position base slope hinc hfirst.2.2.2 hp₁ hz₁
  have he₂ := same_tube_same_height_error I height position base slope hinc hsecond.2.2.2 hp₂ hz₂
  have hmain := witness_coarse_displacement I height cell position base slope coarse hrho hinc w hw
    htime₁ htime₂ hgrid₁ hgrid₂ hterminal
  let R := position w.2.point₂-position w.1.point₂-
    (height w.1.point₁-height w.1.point₀) • (coarse w.2.tube₁-coarse w.1.tube₁)
  calc
    ‖position p₂-position p₁-
      (height w.1.point₁-height w.1.point₀) • (coarse w.2.tube₁-coarse w.1.tube₁)‖ =
        ‖((position p₂-position w.2.point₂)+R)-(position p₁-position w.1.point₂)‖ := by
      congr 1
      dsimp [R]
      abel
    _ ≤ (‖position p₂-position w.2.point₂‖+‖R‖)+‖position p₁-position w.1.point₂‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 3*rho^2+12*epsilon := by dsimp [R]; linarith

def terminalGrid (q : ℝ) (theta : T → Fin 3 → ℝ) (t : T) : Fin 3 → ℤ :=
  fun j => ⌊theta t j/q⌋

def scalarSlope (theta : T → Fin 3 → ℝ) (t : T) : ℝ := theta t 0
def planarSlope (theta : T → Fin 3 → ℝ) (t : T) : ℝ × ℝ := (theta t 0,theta t 1)
def scalarAngle (q : ℝ) (theta : T → Fin 3 → ℝ) (t : T) : ℤ := ⌊theta t 0/q⌋
def planarAngle (q : ℝ) (theta : T → Fin 3 → ℝ) (t : T) : ℤ × ℤ :=
  (⌊theta t 0/q⌋,⌊theta t 1/q⌋)
def scalarDecode (q : ℝ) (a : ℤ) : ℝ := q*(a : ℝ)
def planarDecode (q : ℝ) (a : ℤ × ℤ) : ℝ × ℝ := (q*(a.1 : ℝ),q*(a.2 : ℝ))

lemma floor_approximation {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x-q*(⌊x/q⌋ : ℝ)| ≤ q := by
  have hl := (le_div_iff₀ hq).mp (Int.floor_le (x/q))
  have hu := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (x/q))
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

omit [DecidableEq T] in
theorem scalar_grid_approximation (q : ℝ) (hq : 0 < q) (theta : T → Fin 3 → ℝ) (t : T) :
    ‖scalarSlope theta t-scalarDecode q (scalarAngle q theta t)‖ ≤ q := by
  exact floor_approximation hq (theta t 0)

omit [DecidableEq T] in
theorem planar_grid_approximation (q : ℝ) (hq : 0 < q) (theta : T → Fin 3 → ℝ) (t : T) :
    ‖planarSlope theta t-planarDecode q (planarAngle q theta t)‖ ≤ q := by
  change max |theta t 0-q*(⌊theta t 0/q⌋ : ℝ)| |theta t 1-q*(⌊theta t 1/q⌋ : ℝ)| ≤ q
  exact max_le (floor_approximation hq _) (floor_approximation hq _)

omit [DecidableEq T] in
theorem terminal_grid_component_gap (q : ℝ) (hq : 0 < q) (theta : T → Fin 3 → ℝ)
    (s t : T) (heq : terminalGrid q theta s=terminalGrid q theta t) (j : Fin 3) :
    |theta s j-theta t j| ≤ q :=
  FiniteTransverseMenuGrowth.same_floor_abs_sub_le hq (congrFun heq j)

omit [DecidableEq T] in
theorem scalar_terminal_grid_gap (q : ℝ) (hq : 0 < q) (theta : T → Fin 3 → ℝ)
    (s t : T) (heq : terminalGrid q theta s=terminalGrid q theta t) :
    ‖scalarSlope theta s-scalarSlope theta t‖ ≤ q :=
  terminal_grid_component_gap q hq theta s t heq 0

omit [DecidableEq T] in
theorem planar_terminal_grid_gap (q : ℝ) (hq : 0 < q) (theta : T → Fin 3 → ℝ)
    (s t : T) (heq : terminalGrid q theta s=terminalGrid q theta t) :
    ‖planarSlope theta s-planarSlope theta t‖ ≤ q := by
  change max |theta s 0-theta t 0| |theta s 1-theta t 1| ≤ q
  exact max_le (terminal_grid_component_gap q hq theta s t heq 0)
    (terminal_grid_component_gap q hq theta s t heq 1)

theorem witness_time_gaps (I : Finset (P × T)) (height : P → ℝ) (cell : T → K)
    (Z : Finset ℝ) {rho : ℝ}
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell) :
    |height w.1.point₁-height w.1.point₀| ≤ rho ∧
      |height w.1.point₂-height w.1.point₁| ≤ rho := by
  have hp := (TwoTubePathCollisionCount.mem_paths I w.1).mp (witness_conditions I height cell hw).1
  have hz₀ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.1)
  have hz₁ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.1)
  have hz₂ := hheight _ (Finset.mem_image_of_mem Prod.fst hp.2.2.2)
  exact ⟨hdiam _ hz₁ _ hz₀,hdiam _ hz₂ _ hz₁⟩

/-- Native a=1 displacement from literal original graph incidences and literal
floor labels of the FULL original 3-coordinate tube slopes. -/
theorem scalar_native_witness_displacement (I : Finset (P × T)) (height : P → ℝ)
    (position : P → ℝ) (base : T → ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    {delta rho q Err : ℝ} (hrho : 0 ≤ rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height (terminalGrid q theta))
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖position p₂-position p₁-(height w.1.point₁-height w.1.point₀) •
      (scalarDecode q (scalarAngle q theta w.2.tube₁)-scalarDecode q (scalarAngle q theta w.1.tube₁))‖
        ≤ (3+12*Err)*rho^2 := by
  have ht := witness_time_gaps I height (terminalGrid q theta) Z hheight hdiam w hw
  have hc := (witness_conditions I height (terminalGrid q theta) hw).2.2.2.2.2
  have hdisp := fixed_representative_displacement I height (terminalGrid q theta) position base
    (scalarSlope theta) (fun t => scalarDecode q (scalarAngle q theta t)) hrho hinc w hw
    p₁ p₂ hp₁ hp₂ hz₁ hz₂ ht.1 ht.2
    ((scalar_grid_approximation q hq theta w.1.tube₁).trans hqρ)
    ((scalar_grid_approximation q hq theta w.2.tube₁).trans hqρ)
    ((scalar_terminal_grid_gap q hq theta w.2.tube₂ w.1.tube₂ hc).trans hqρ)
  have he := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 12*Err by positivity)
  nlinarith

/-- Native a=2 max-norm displacement. Its successor and fixed point may be
chosen from OriginalWSuccessorSelection; no displacement premise is assumed. -/
theorem planar_native_witness_displacement (I : Finset (P × T)) (height : P → ℝ)
    (position : P → ℝ × ℝ) (base : T → ℝ × ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    {delta rho q Err : ℝ} (hrho : 0 ≤ rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height (terminalGrid q theta))
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖position p₂-position p₁-(height w.1.point₁-height w.1.point₀) •
      (planarDecode q (planarAngle q theta w.2.tube₁)-planarDecode q (planarAngle q theta w.1.tube₁))‖
        ≤ (3+12*Err)*rho^2 := by
  have ht := witness_time_gaps I height (terminalGrid q theta) Z hheight hdiam w hw
  have hc := (witness_conditions I height (terminalGrid q theta) hw).2.2.2.2.2
  have hdisp := fixed_representative_displacement I height (terminalGrid q theta) position base
    (planarSlope theta) (fun t => planarDecode q (planarAngle q theta t)) hrho hinc w hw
    p₁ p₂ hp₁ hp₂ hz₁ hz₂ ht.1 ht.2
    ((planar_grid_approximation q hq theta w.1.tube₁).trans hqρ)
    ((planar_grid_approximation q hq theta w.2.tube₁).trans hqρ)
    ((planar_terminal_grid_gap q hq theta w.2.tube₂ w.1.tube₂ hc).trans hqρ)
  have he := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 12*Err by positivity)
  nlinarith

end
end OriginalWPhysicalDisplacement
