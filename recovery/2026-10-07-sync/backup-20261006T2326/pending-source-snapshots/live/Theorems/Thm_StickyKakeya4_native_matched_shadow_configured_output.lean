import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_source
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowConfiguredOutput
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseReadback NativeLocalParentSource CanonicalConfiguredE4Bridge
open NativeMatchedShadowConfiguredSource NativeConfiguredIncidenceFibers

/-- The inverse shadow menu at a possibly coarser scale, with no
coarse-scale separation assumption on the finer configured point set. -/
theorem actual_inverse_output_image_bounds {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref A : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * ((2 ^ b : ℕ) : ℝ) ≤ 64)
    (p : Parent) (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hA : A ⊆ incidences original)
    (hparent : ∀ z ∈ A, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) ≤ 4096 / ((2 ^ b : ℕ) : ℝ)) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
    let shadow := A.image (doublePair h R a m p hQ (2 ^ b))
    let output := A.image (fun z => (cfg z.2, outputTube h R Eref a m b p hS z.1))
    (shadow.image Prod.snd).card ≤ 5 ^ 4 * (output.image Prod.fst).card ∧
    shadow.card ≤ 5 ^ 4 * output.card := by
  intro cfg shadow output
  have hh := actual_inverse_image_bounds h original horiginal ha A R m (2 ^ b) hm
    (by positivity) hNscale hRelScale p hQ hA hparent s P hP hd F Fcfg
    hF hCfg R0 hR0 hbase hmatch
  dsimp only at hh
  have hp := outputPair_image_card h R Eref a m b p hS cfg A hparent
  change (A.image (fun z => (NativeRelativeParentLabels.relativeLabel D a (2 ^ m) p (2 ^ b) z.1,
    cfg z.2))).card = output.card at hp
  rw [hp] at hh
  simpa only [shadow, output, image_image, Function.comp_def] using hh

/-- The fixed-cost matched shadow comparison on the SAME actual output
index set used by the tube-containment and W readers. -/
theorem actual_output_image_bounds {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref A : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * ((2 ^ b : ℕ) : ℝ) ≤ 64)
    (p : Parent) (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hA : A ⊆ incidences original)
    (hparent : ∀ z ∈ A, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) = 4096 / ((2 ^ b : ℕ) : ℝ))
    (hsep : ∀ x ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      ∀ y ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      x ≠ y → (mu m * (R0 : ℝ)) / 64 ≤ dist x y) :
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0
    let shadow := A.image (doublePair h R a m p hQ (2 ^ b))
    let output := A.image (fun z => (cfg z.2, outputTube h R Eref a m b p hS z.1))
    (shadow.image Prod.snd).card ≤ 5 ^ 4 * (output.image Prod.fst).card ∧
    (output.image Prod.fst).card ≤ 33 ^ 4 * (shadow.image Prod.snd).card ∧
    shadow.card ≤ 5 ^ 4 * output.card ∧
    output.card ≤ 33 ^ 4 * shadow.card := by
  intro cfg shadow output
  have hh := actual_image_bounds h original horiginal ha A R m (2 ^ b) hm
    (by positivity) hNscale hRelScale p hQ hA hparent s P hP hd F Fcfg
    hF hCfg R0 hR0 hbase hmatch hsep
  dsimp only at hh
  have hp := outputPair_image_card h R Eref a m b p hS cfg A hparent
  change (A.image (fun z => (NativeRelativeParentLabels.relativeLabel D a (2 ^ m) p (2 ^ b) z.1,
    cfg z.2))).card = output.card at hp
  rw [hp] at hh
  simpa only [shadow, output, image_image, Function.comp_def] using hh

end NativeMatchedShadowConfiguredOutput
