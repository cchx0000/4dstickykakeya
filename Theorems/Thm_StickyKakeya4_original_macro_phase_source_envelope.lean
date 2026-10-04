import Theorems.Thm_StickyKakeya4_native_original_phase_source_kt
import Theorems.Thm_StickyKakeya4_native_original_macro_menu_budget
import Theorems.Thm_StickyKakeya4_original_literal_angular_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace OriginalMacroPhaseSourceEnvelope
open Classical Finset NativeOriginalPhaseSourceKT NativeScheduledScaleSelection
open OriginalPhaseWindowGraph OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open NativeOriginalPhaseWindowGraph OriginalWGrainDrift OriginalPhaseGridPopulation OriginalPhaseGridError FinitePlaneProjectionGrid
/-- The enlarged budget uses a literal subsequence of the original scale
 schedule. The original single xi witnesses and all point labels survive. -/
theorem fourfold_original_xi_law {P : Type*} (E : Finset P) (height x : P → ℝ)
    (y xi : P → ℝ × ℝ) {delta eta Cxi K : ℝ} (hd : 0 < delta) (hCK : Cxi ≤ K)
    (hSource : ScheduledOriginalXiLaw E height x y xi delta eta Cxi) :
    ScheduledOriginalXiLaw E height x y xi delta (4*eta) K := by
  intro n hdn hn1
  rw [OriginalLiteralAngularBudget.fourfold_schedule_readback] at hdn hn1 ⊢
  have hs := hSource (4*n) hdn hn1
  intro q hq
  obtain ⟨center,hbox,hfield⟩ := hs q hq
  refine ⟨center,hbox,?_⟩
  intro p hp hcell
  exact (hfield p hp hcell).trans
    (mul_le_mul_of_nonneg_right hCK (hd.trans_le hdn).le)
/-- The actual expanded W window receives its absolute KT1 envelope from
 the original microscopic xi schedule. Its width is the derived drift width;
 there is no output A-profile or arbitrary width budget among the inputs. -/
theorem actual_macro_phase_KT {P T : Type*} [DecidableEq P] [DecidableEq T]
    (E : Finset P) (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (hOriginal : TwoTubePathCollisionCount.points I ⊆ E)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x0 : ℝ) (xi0 : ℝ × ℝ) (k : GrainLabel)
    {delta eta Cxi L DirErr IncErr r tau sourceMesh mesh : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta)
    (hKbig : 79626240000 ≤ delta^(-eta)) (hXiK : Cxi ≤ delta^(-eta))
    (hL : 0 ≤ L) (hLK : L ≤ delta^(-eta))
    (hD : 0 ≤ DirErr) (hDK : DirErr ≤ delta^(-eta))
    (_hI : 0 ≤ IncErr) (hIK : IncErr ≤ delta^(-eta))
    (hdr : delta ≤ r) (hr1 : r ≤ 1) (htau : r ≤ tau)
    (hSource : ScheduledOriginalXiLaw E height x y offset delta eta Cxi)
    (hFentries : |(F z 1).1| ≤ 1 ∧ |(F z 1).2| ≤ 1)
    (hSourceMesh : 0 < sourceMesh) (hmesh : 0 < mesh) (hmeshScale : mesh ≤ sourceMesh) :
    let width := (9*L+16*max DirErr (2*IncErr)+1)*r
    let Q := expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height S hSV s)) k
    ∀ i ∈ Q, ∀ R : ℝ, mesh ≤ R →
      ((Q.filter (fun j => dist3 (gridPoint sourceMesh i) (gridPoint sourceMesh j) ≤ R)).card:ℝ) ≤
        delta^(-36*eta)*R/mesh := by
  let K := delta^(-eta)
  let M := delta^(-(4*eta))
  have hK0 : 0 < K := Real.rpow_pos_of_pos hd _
  have hK1 : 1 ≤ K := by dsimp [K]; linarith only [hKbig]
  have hKM : K ≤ M := Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith : -(4*eta) ≤ -eta)
  have hM2 : 2 ≤ M := by dsimp [K] at hKM; linarith only [hKbig,hKM]
  have hr : 0 < r := hd.trans_le hdr
  have hmax : max DirErr (2*IncErr) ≤ 2*K := max_le (by dsimp [K]; linarith only [hDK,hK0.le])
    (by dsimp [K]; linarith only [hIK])
  have hwidth0 : 0 < (9*L+16*max DirErr (2*IncErr)+1)*r := by positivity
  have hcoef : 9*L+16*max DirErr (2*IncErr)+1 ≤ 40*K*M := by
    have hh := mul_le_mul_of_nonneg_left hM2 (show 0 ≤ 40*K by positivity)
    dsimp [K] at hK1 hmax hh ⊢
    nlinarith only [hLK,hmax,hK1,hh]
  have hwidth : (9*L+16*max DirErr (2*IncErr)+1)*r ≤ 40*K*M*r :=
    mul_le_mul_of_nonneg_right hcoef hr.le
  have hLaw := fourfold_original_xi_law E height x y offset hd hXiK hSource
  have hh := actual_window_source_power_KT E I height x y offset F hOriginal S hSV z x0 xi0 k
    hd hd1 (show 0 < 4*eta by positivity) hdr hr1 hK1 hKM
    (show 5101248 ≤ M by dsimp [K] at hKM; linarith only [hKbig,hKM]) hLaw htau
    hwidth0 hwidth hFentries hSourceMesh hmesh hmeshScale
  simpa only [show -9*(4*eta)=(-36:ℝ)*eta by ring] using hh
/-- The same selected macro-cell's proved height population is a concrete
 fine-height mass at the honest phase radius. -/
theorem original_macro_height_mass_power {K L delta q rho count : ℝ}
    (hK : 79626240000 ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K)
    (hd : 0 ≤ delta) (hq : 0 ≤ q) (hcount : 0 ≤ count) (hrho : rho ≤ 2*q)
    (hMass : q ≤ 124416000*K^5*(2*L+4)^2*delta*count) :
    (1/K^9)*rho ≤ delta*count := by
  have hK0 : 0 < K := by linarith
  have hcost := (OriginalLiteralMacroHeightBudget.original_macro_cost_absorption hK hL hLK).2.2
  have hm : q ≤ K^8*delta*count := hMass.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost hd) hcount)
  have hh : rho ≤ K^9*(delta*count) := by
    calc
      _ ≤ 2*q := hrho
      _ ≤ K*q := mul_le_mul_of_nonneg_right (show (2:ℝ)≤K by linarith) hq
      _ ≤ K*(K^8*delta*count) := mul_le_mul_of_nonneg_left hm hK0.le
      _ = _ := by ring
  have hdiv : rho/K^9 ≤ delta*count :=
    (div_le_iff₀ (pow_pos hK0 9)).mpr (by simpa only [mul_comm] using hh)
  exact (show (1/K^9)*rho=rho/K^9 by ring).trans_le hdiv
end OriginalMacroPhaseSourceEnvelope
