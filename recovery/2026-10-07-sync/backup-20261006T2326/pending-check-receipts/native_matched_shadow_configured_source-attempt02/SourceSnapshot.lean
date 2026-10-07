import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_counts
import Theorems.Thm_StickyKakeya4_native_matched_shadow_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowConfiguredSource
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeRelativeCoarseReadback NativeRelativeCoarsePointMenu NativeRelativeParentLabels
open NativeLocalParentSource
open CanonicalConfiguredE4Bridge NativeMatchedShadowConfiguredGeometry
open NativeMatchedShadowConfiguredCounts

/-- One-sided source transfer at any coarser matched shadow mesh. The
actual configured points need not be separated at this coarser scale. -/
theorem actual_inverse_image_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (A : Finset (Fin n × Index))
    (backbone : Finset (Fin n)) (m M : ℕ) (hm : 6 ≤ m) (hM : 0 < M)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * (M : ℝ) ≤ 64)
    (p : Parent) (hQ : (parentLabels D backbone a (2 ^ m) p).Nonempty)
    (hA : A ⊆ incidences original)
    (hparent : ∀ z ∈ A, z.1 ∈ parentLabels D backbone a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) ≤ 4096 / (M : ℝ)) :
    let cfg := fun z : Fin n × Index => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2
    (A.image (fun z => (doublePair h backbone a m p hQ M z).2)).card ≤
      5 ^ 4 * (A.image cfg).card ∧
    (A.image (doublePair h backbone a m p hQ M)).card ≤
      5 ^ 4 * (A.image (fun z => (relativeLabel D a (2 ^ m) p M z.1, cfg z))).card := by
  intro cfg
  let front := fun z : Fin n × Index => doubleFront D a (2 ^ m) p
    (originalRepresentative h backbone a m p hQ M (relativeLabel D a (2 ^ m) p M z.1)) z.1 z.2
  let phase := fun z : Fin n × Index => relativeLabel D a (2 ^ m) p M z.1
  let O := NativePackedFrameIsometry.frame s P hP hd
  have hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ 64 / (M : ℝ) := by
    intro z hz
    exact point_front_distance h original horiginal ha m M hm hM hNscale hRelScale
      p z.1 _ z.2 ((mem_incidences original z.1 z.2).mp (hA hz))
      ((mem_parentLabels D backbone a (2 ^ m) p _).mp (hparent z hz)).2
      (originalRepresentative_label h backbone a m p hQ M z.1 (hparent z hz))
      s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
  have hp : (fun z => shadowLabel (64 / (M : ℝ)) front z) =
      (fun z => (doublePair h backbone a m p hQ M z).2) := by
    funext z
    dsimp only [shadowLabel, front, doublePair, doubleLabel]
    congr 1
    ring
  have hpair : (fun z => (phase z, shadowLabel (64 / (M : ℝ)) front z)) =
      doublePair h backbone a m p hQ M := by
    funext z
    exact Prod.ext rfl (congrFun hp z)
  have hh := inverse_image_bounds A (64 / (M : ℝ)) (by positivity) O phase front cfg hclose
  simpa only [hp, hpair, phase] using hh

/-- The unchanged original incidence set has fixed-cost comparisons between
its actual doublePair shadow and actual configured phase-point graph. The
separation field is exactly the one supplied by the global q=8 residue cut.
No pref or fine phase fiber is charged in this comparison. -/
theorem actual_image_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (A : Finset (Fin n × Index))
    (backbone : Finset (Fin n)) (m M : ℕ) (hm : 6 ≤ m) (hM : 0 < M)
    (hNscale : ((2 ^ m : ℕ) : ℝ) * D.thickness ≤ 1)
    (hRelScale : ((2 ^ m : ℕ) : ℝ) * D.thickness * (M : ℝ) ≤ 64)
    (p : Parent) (hQ : (parentLabels D backbone a (2 ^ m) p).Nonempty)
    (hA : A ⊆ incidences original)
    (hparent : ∀ z ∈ A, z.1 ∈ parentLabels D backbone a (2 ^ m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) = 4096 / (M : ℝ))
    (hsep : ∀ x ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      ∀ y ∈ A.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
      x ≠ y → (mu m * (R0 : ℝ)) / 64 ≤ dist x y) :
    let cfg := fun z : Fin n × Index => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2
    (A.image (fun z => (doublePair h backbone a m p hQ M z).2)).card ≤
      5 ^ 4 * (A.image cfg).card ∧
    (A.image cfg).card ≤
      33 ^ 4 * (A.image (fun z => (doublePair h backbone a m p hQ M z).2)).card ∧
    (A.image (doublePair h backbone a m p hQ M)).card ≤
      5 ^ 4 * (A.image (fun z => (relativeLabel D a (2 ^ m) p M z.1, cfg z))).card ∧
    (A.image (fun z => (relativeLabel D a (2 ^ m) p M z.1, cfg z))).card ≤
      33 ^ 4 * (A.image (doublePair h backbone a m p hQ M)).card := by
  intro cfg
  let front := fun z : Fin n × Index => doubleFront D a (2 ^ m) p
    (originalRepresentative h backbone a m p hQ M (relativeLabel D a (2 ^ m) p M z.1)) z.1 z.2
  let phase := fun z : Fin n × Index => relativeLabel D a (2 ^ m) p M z.1
  let O := NativePackedFrameIsometry.frame s P hP hd
  have hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ 64 / (M : ℝ) := by
    intro z hz
    exact point_front_distance h original horiginal ha m M hm hM hNscale hRelScale
      p z.1 _ z.2 ((mem_incidences original z.1 z.2).mp (hA hz))
      ((mem_parentLabels D backbone a (2 ^ m) p _).mp (hparent z hz)).2
      (originalRepresentative_label h backbone a m p hQ M z.1 (hparent z hz))
      s P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch.le
  have hsep' : ∀ x ∈ A.image cfg, ∀ y ∈ A.image cfg, x ≠ y → 64 / (M : ℝ) ≤ dist x y := by
    intro x hx y hy hxy
    have hh := hsep x hx y hy hxy
    rw [hmatch] at hh
    calc
      64 / (M : ℝ) = (4096 / (M : ℝ)) / 64 := by ring
      _ ≤ dist x y := hh
  have hp : (fun z => shadowLabel (64 / (M : ℝ)) front z) =
      (fun z => (doublePair h backbone a m p hQ M z).2) := by
    funext z
    dsimp only [shadowLabel, front, doublePair, doubleLabel]
    congr 1
    ring
  have hpair : (fun z => (phase z, shadowLabel (64 / (M : ℝ)) front z)) =
      doublePair h backbone a m p hQ M := by
    funext z
    exact Prod.ext rfl (congrFun hp z)
  have hh := image_bounds A (64 / (M : ℝ)) (by positivity) O phase front cfg hclose hsep'
  simpa only [hp, hpair, phase] using hh

end NativeMatchedShadowConfiguredSource
