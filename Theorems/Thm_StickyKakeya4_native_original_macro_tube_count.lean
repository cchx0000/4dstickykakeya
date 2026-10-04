import Theorems.Thm_StickyKakeya4_original_macro_direction_source
import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeOriginalMacroTubeCount
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry
open OriginalMacroDirectionCells OriginalMacroDirectionSource NativeTangentGridCoarsening
variable {n : ℕ}
def scalarSlope (D : FiniteScaleSource n) (i : Fin n) : ℝ := slope (D.line i) (0:Fin 3)
def normalSlope (D : FiniteScaleSource n) (i : Fin n) : ℝ × ℝ :=
  (slope (D.line i) (1:Fin 3),slope (D.line i) (2:Fin 3))
/-- The counted three-coordinate vector is exactly the actual source slope. -/
theorem direction_vector_readback (D : FiniteScaleSource n) (i : Fin n) :
    directionVector (scalarSlope D) (normalSlope D) i=slope (D.line i) := by
  funext j
  fin_cases j <;> rfl
private lemma floor_box {x tau q : ℝ} (ht : 0 < tau) (htq : tau ≤ q) (k : ℤ)
    (hk : ⌊x/tau⌋=k) : tau*(k:ℝ) ≤ x ∧ x ≤ tau*(k:ℝ)+q := by
  have he : ⌊(x-0)/tau⌋=k := by simpa only [sub_zero] using hk
  have hb := coarse_floor_interval ht he
  exact ⟨by linarith only [hb.1],by linarith only [hb.2,htq]⟩
/-- Native source direction separation supplies every terminal-cell fiber
 cap directly. No AD or density assumption on the retained labels is used. -/
theorem native_terminal_fiber_card {D : FiniteScaleSource n} {eta delta q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (S : Finset (Fin n))
    (hd : 0 < delta) (hdD : delta ≤ D.thickness) (hdq : delta ≤ q) (k : ℤ × (ℤ × ℤ)) :
    ((S.filter (fun i => directionCell (q/8) (scalarSlope D) (normalSlope D) i=k)).card:ℝ) ≤
      5832*(q/delta)^3 := by
  have hq : 0 < q := hd.trans_le hdq
  let A := S.filter (fun i => directionCell (q/8) (scalarSlope D) (normalSlope D) i=k)
  let c : Fin 3 → ℝ := ![(q/8)*(k.1:ℝ),(q/8)*(k.2.1:ℝ),(q/8)*(k.2.2:ℝ)]
  apply NativeOriginalSlopeCubePacking.original_cube_card_le_ratio A D.line hd hdq
    (fun i _hi => h.1.2.2.2.2.1 i) (fun i _hi => h.2.1.1 i)
    (fun i _hi j _hj hij => hdD.trans (h.1.2.2.2.2.2.2.2.2.2.1 i j hij)) c
  intro i hi j
  have he := (mem_filter.mp hi).2
  have h0 : ⌊slope (D.line i) (0:Fin 3)/(q/8)⌋=k.1 := congrArg Prod.fst he
  have h1 : ⌊slope (D.line i) (1:Fin 3)/(q/8)⌋=k.2.1 :=
    congrArg (fun c : ℤ × (ℤ × ℤ) => c.2.1) he
  have h2 : ⌊slope (D.line i) (2:Fin 3)/(q/8)⌋=k.2.2 :=
    congrArg (fun c : ℤ × (ℤ × ℤ) => c.2.2) he
  fin_cases j
  · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.1 h0
  · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.2.1 h1
  · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.2.2 h2
/-- Count actual original tube labels by their true direction cells. -/
theorem native_tubes_le_terminal_cells {D : FiniteScaleSource n} {eta delta q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (S : Finset (Fin n))
    (hd : 0 < delta) (hdD : delta ≤ D.thickness) (hdq : delta ≤ q) :
    (S.card:ℝ) ≤ 5832*(q/delta)^3*
      ((directionCells S (q/8) (scalarSlope D) (normalSlope D)).card:ℝ) := by
  have hh := image_card_le_real_mul_of_fiber_images S id
    (directionCell (q/8) (scalarSlope D) (normalSlope D)) (5832*(q/delta)^3)
    (fun k _hk => by simpa only [image_id] using native_terminal_fiber_card h S hd hdD hdq k)
  simpa only [image_id,directionCells] using hh
/-- The actual native tube population follows from its existing direction
 separation and the literal original Phi/xi/f source data. The working mesh
 may be smaller than its source thickness, with that comparison explicit.
 This is a native supplier; no direction-separation property is attributed to arbitrary
 paper AD tube families. -/
theorem native_original_macro_tube_population {P : Type*} [DecidableEq P]
    {D : FiniteScaleSource n} {eta delta q DirErr Cxi L A K kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (I : Finset (P × Fin n))
    (height : P → ℝ) (offset : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (fine : P → Finset ℝ) (Phi : Finset ℝ) (F0 : ℝ →L[ℝ] ℝ × ℝ) (xi0 : ℝ × ℝ)
    (hd : 0 < delta) (hdD : delta ≤ D.thickness) (hq1 : q ≤ 1) (hdq : delta ≤ q) (hDir : 0 ≤ DirErr) (hXi : 0 ≤ Cxi)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hK : 0 ≤ K) (hF0 : ‖F0‖ ≤ A)
    (hreal : ∀ p t, (p,t) ∈ I → ∃ phi ∈ fine p,
      |scalarSlope D t-phi| ≤ DirErr*delta ∧
      ‖normalSlope D t-offset p-F (height p) phi‖ ≤ DirErr*delta)
    (hbox : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hPhi : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ q)
    (hxi : ∀ p ∈ TwoTubePathCollisionCount.points I, ‖offset p-xi0‖ ≤ Cxi*q)
    (hosc : ∀ p ∈ TwoTubePathCollisionCount.points I, ‖F (height p)-F0‖ ≤ L*q)
    (H : NativeScalarCoverAD.CoverADBounds Phi q K kappa) (hPhiBox : ∀ a ∈ Phi, |a| ≤ 1) :
    q^kappa*((TwoTubePathCollisionCount.tubes I).card:ℝ) ≤
      11664*K*(16*(DirErr+Cxi+L+2*A+2)+2)^3*(q/delta)^3 := by
  have hq : 0 < q := hd.trans_le hdq
  have ht := native_tubes_le_terminal_cells h (TwoTubePathCollisionCount.tubes I) hd hdD hdq
  have ha := original_full_terminal_population I height offset F (scalarSlope D) (normalSlope D)
    fine Phi F0 xi0 hq hq1 hdq hDir hXi hL hA hK hF0 hreal hbox hPhi hxi hosc H hPhiBox
  have ht' := mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hq kappa).le
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 5832*(q/delta)^3 by positivity)
  nlinarith only [ht',ha']
end NativeOriginalMacroTubeCount
