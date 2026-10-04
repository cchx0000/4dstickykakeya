import Theorems.Thm_StickyKakeya4_native_original_macro_tube_count
import Theorems.Thm_StickyKakeya4_native_dyadic_coarse_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
noncomputable section
namespace NativeRescaledMacroTubeCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry OriginalMacroDirectionCells NativeTangentGridCoarsening
variable {n : ℕ}
def scalarSlope (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : ℝ := (data D cells a N p).slope i (0:Fin 3)
def normalSlope (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) : ℝ × ℝ :=
  ((data D cells a N p).slope i (1:Fin 3),(data D cells a N p).slope i (2:Fin 3))
/-- Exact slope formula of the actual parent shear, on the original labels. -/
theorem actual_slope_readback (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (j : Fin 3) :
    (data D cells a N p).slope i j=(N:ℝ)*slope (D.line i) j-(p.1 j:ℝ) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  change (slope (D.line i) j-(p.1 j:ℝ)/(N:ℝ))/(1/(N:ℝ))=_
  field_simp
/-- The true R=32 phase mesh lies below the original separation enlarged
 by the actual parent factor N. This is an equality-based scale readback. -/
theorem actual_mesh_le_source_scale {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) :
    (data D cells a N p).σ/32 ≤ (N:ℝ)*D.thickness := by
  rw [NativeDyadicCoarseNormalization.native_dyadic_scale]
  have hn : (0:ℝ) ≤ (N:ℝ)*D.thickness := mul_nonneg (Nat.cast_nonneg _) h.1.2.1.le
  linarith
private lemma floor_box {x tau q : ℝ} (ht : 0 < tau) (htq : tau ≤ q) (k : ℤ)
    (hk : ⌊x/tau⌋=k) : tau*(k:ℝ) ≤ x ∧ x ≤ tau*(k:ℝ)+q := by
  have he : ⌊(x-0)/tau⌋=k := by simpa only [sub_zero] using hk
  have hb := coarse_floor_interval ht he
  exact ⟨by linarith only [hb.1],by linarith only [hb.2,htq]⟩
/-- A true direction cell of the RESCALED original tubes pulls back to an
 original slope cube of width q/N. The original native direction packing
 supplies its population before any new-scale AD/CW admission is available. -/
theorem rescaled_terminal_fiber_card {D : FiniteScaleSource n} {eta delta q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (S : Finset (Fin n))
    (hd : 0 < delta) (hscale : delta ≤ (N:ℝ)*D.thickness) (hdq : delta ≤ q)
    (k : ℤ × (ℤ × ℤ)) :
    ((S.filter (fun i => directionCell (q/8) (scalarSlope D cells a N p)
      (normalSlope D cells a N p) i=k)).card:ℝ) ≤ 32768*(q/delta)^3 := by
  have hq : 0 < q := hd.trans_le hdq
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  let A := S.filter (fun i => directionCell (q/8) (scalarSlope D cells a N p) (normalSlope D cells a N p) i=k)
  let corner : Fin 3 → ℝ := ![(q/8)*(k.1:ℝ),(q/8)*(k.2.1:ℝ),(q/8)*(k.2.2:ℝ)]
  let oldCorner : Fin 3 → ℝ := fun j => (corner j+(p.1 j:ℝ))/(N:ℝ)
  have hbox : ∀ i ∈ A, ∀ j, oldCorner j ≤ slope (D.line i) j ∧
      slope (D.line i) j ≤ oldCorner j+q/(N:ℝ) := by
    intro i hi j
    have he := (mem_filter.mp hi).2
    have h0 : ⌊(data D cells a N p).slope i (0:Fin 3)/(q/8)⌋=k.1 := congrArg Prod.fst he
    have h1 : ⌊(data D cells a N p).slope i (1:Fin 3)/(q/8)⌋=k.2.1 :=
      congrArg (fun c : ℤ × (ℤ × ℤ) => c.2.1) he
    have h2 : ⌊(data D cells a N p).slope i (2:Fin 3)/(q/8)⌋=k.2.2 :=
      congrArg (fun c : ℤ × (ℤ × ℤ) => c.2.2) he
    have hb : corner j ≤ (data D cells a N p).slope i j ∧
        (data D cells a N p).slope i j ≤ corner j+q := by
      fin_cases j
      · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.1 h0
      · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.2.1 h1
      · exact floor_box (by positivity : 0 < q/8) (by linarith : q/8 ≤ q) k.2.2 h2
    rw [actual_slope_readback D cells a N hN p i j] at hb
    constructor
    · apply (div_le_iff₀ hNr).mpr
      nlinarith only [hb.1]
    · have heq : oldCorner j+q/(N:ℝ)=(corner j+(p.1 j:ℝ)+q)/(N:ℝ) := by dsimp [oldCorner]; ring
      rw [heq]
      apply (le_div_iff₀ hNr).mpr
      nlinarith only [hb.2]
  have hc := NativeOriginalSlopeCubePacking.original_cube_card_le_add_one A D.line h.1.2.1
    (show 0 ≤ q/(N:ℝ) by positivity) (fun i _hi => h.1.2.2.2.2.1 i)
    (fun i _hi => h.2.1.1 i)
    (fun i _hi j _hj hij => h.1.2.2.2.2.2.2.2.2.2.1 i j hij) oldCorner hbox
  have hr : (q/(N:ℝ))/D.thickness ≤ q/delta := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hq.le hd hscale
  have hratio : 1 ≤ q/delta := (le_div_iff₀ hd).mpr (by simpa using hdq)
  have hSource : 0 < D.thickness := h.1.2.1
  have hp : ((q/(N:ℝ))/D.thickness+1)^3 ≤ (2*(q/delta))^3 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hr,hratio]
  exact hc.trans ((mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤4096)).trans_eq (by ring))
/-- Count the actual original labels of the coarse family using its real
 rescaled directions. Full new-scale native admissibility is not assumed. -/
theorem rescaled_tubes_le_terminal_cells {D : FiniteScaleSource n} {eta delta q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (S : Finset (Fin n))
    (hd : 0 < delta) (hscale : delta ≤ (N:ℝ)*D.thickness) (hdq : delta ≤ q) :
    (S.card:ℝ) ≤ 32768*(q/delta)^3*
      ((directionCells S (q/8) (scalarSlope D cells a N p) (normalSlope D cells a N p)).card:ℝ) := by
  have hh := image_card_le_real_mul_of_fiber_images S id
    (directionCell (q/8) (scalarSlope D cells a N p) (normalSlope D cells a N p))
    (32768*(q/delta)^3)
    (fun k _hk => by simpa only [image_id] using rescaled_terminal_fiber_card h cells a N hN p S hd hscale hdq k)
  simpa only [image_id,directionCells] using hh
/-- The native original source and the literal macro Phi/xi/f laws give
 the ACTUAL rescaled family's tube population. Its new-scale AD/CW status
 is not an input, and original label retention is unchanged. -/
theorem rescaled_original_macro_tube_population {P : Type*} [DecidableEq P]
    {D : FiniteScaleSource n} {eta delta q DirErr Cxi L A K kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (parent : Parent) (I : Finset (P × Fin n))
    (height : P → ℝ) (offset : P → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (fine : P → Finset ℝ) (Phi : Finset ℝ) (F0 : ℝ →L[ℝ] ℝ × ℝ) (xi0 : ℝ × ℝ)
    (hd : 0 < delta) (hscale : delta ≤ (N:ℝ)*D.thickness) (hq1 : q ≤ 1) (hdq : delta ≤ q)
    (hDir : 0 ≤ DirErr) (hXi : 0 ≤ Cxi) (hL : 0 ≤ L) (hA : 0 ≤ A) (hK : 0 ≤ K) (hF0 : ‖F0‖ ≤ A)
    (hreal : ∀ p t, (p,t) ∈ I → ∃ phi ∈ fine p,
      |scalarSlope D cells a N parent t-phi| ≤ DirErr*delta ∧
      ‖normalSlope D cells a N parent t-offset p-F (height p) phi‖ ≤ DirErr*delta)
    (hbox : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hPhi : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ phi ∈ fine p, ∃ b ∈ Phi, |phi-b| ≤ q)
    (hxi : ∀ p ∈ TwoTubePathCollisionCount.points I, ‖offset p-xi0‖ ≤ Cxi*q)
    (hosc : ∀ p ∈ TwoTubePathCollisionCount.points I, ‖F (height p)-F0‖ ≤ L*q)
    (H : NativeScalarCoverAD.CoverADBounds Phi q K kappa) (hPhiBox : ∀ b ∈ Phi, |b| ≤ 1) :
    q^kappa*((TwoTubePathCollisionCount.tubes I).card:ℝ) ≤
      65536*K*(16*(DirErr+Cxi+L+2*A+2)+2)^3*(q/delta)^3 := by
  have hq : 0 < q := hd.trans_le hdq
  have ht := rescaled_tubes_le_terminal_cells h cells a N hN parent
    (TwoTubePathCollisionCount.tubes I) hd hscale hdq
  have ha := OriginalMacroDirectionSource.original_full_terminal_population I height offset F
    (scalarSlope D cells a N parent) (normalSlope D cells a N parent)
    fine Phi F0 xi0 hq hq1 hdq hDir hXi hL hA hK hF0 hreal hbox hPhi hxi hosc H hPhiBox
  have ht' := mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hq kappa).le
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 32768*(q/delta)^3 by positivity)
  nlinarith only [ht',ha']
end NativeRescaledMacroTubeCount
