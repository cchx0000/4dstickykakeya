import Theorems.Thm_StickyKakeya4_native_capped_old_ancestors
import Theorems.Thm_StickyKakeya4_native_original_ancestor_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeOldPhaseAncestorCount
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeUnitParentNormalization NativeOriginalPhaseChartGaps OriginalAncestorCounting
open OriginalAncestorFiberGeometry OriginalTubeAncestorSaturation OriginalWPhysicalDisplacement
open NativeCappedOldAncestors NativeCommonCubicalMesh

abbrev Tube {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ) (b : ℕ) :=
  Fin (R.image (parentLabel D a (2^b))).card

def line {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level b : ℕ)
    (Esource : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (i : Tube D R a b) : MarkedLine :=
  MarkedIsometricChart.line O c ((NativeFullCoarseShadow.fullSource h R a level b Esource).line i)

def scalarBase {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level b : ℕ)
    (Esource : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (i : Tube D R a b) : ℝ :=
  intercept (line h R a level b Esource O c i) 0

def scalarSlope {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level b : ℕ)
    (Esource : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (i : Tube D R a b) : ℝ :=
  slope (line h R a level b Esource O c i) 0

def planarBase {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level b : ℕ)
    (Esource : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (i : Tube D R a b) : ℝ × ℝ :=
  (intercept (line h R a level b Esource O c i) 0, intercept (line h R a level b Esource O c i) 1)

def planarSlope {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level b : ℕ)
    (Esource : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (i : Tube D R a b) : ℝ × ℝ :=
  (slope (line h R a level b Esource O c i) 0, slope (line h R a level b Esource O c i) 1)

/-- Shrink only the exact old ancestor scale. The geometric sigma and all
subsequent Section19 constants are unchanged. -/
theorem scalar_parameter_gaps {n : ℕ} {D : FiniteScaleSource n} {eta a sigma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i∈fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b k : ℕ) (hk : k ≤ b) (Esource : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (hsigma : 0 ≤ sigma)
    (hcap : 672/((2^k:ℕ):ℝ) ≤ sigma ∨ k=b)
    (i j : Tube D R a b) (he : oldAncestor D R a b k i=oldAncestor D R a b k j) :
    ‖scalarBase h R a level b Esource O c i-scalarBase h R a level b Esource O c j‖ ≤ sigma ∧
      ‖scalarSlope h R a level b Esource O c i-scalarSlope h R a level b Esource O c j‖ ≤ sigma := by
  have hh := capped_chart_gaps h hK ha R level b k hk Esource O hO c hc hsigma hcap i j he
  exact ⟨hh.2 0, hh.1 0⟩

theorem planar_parameter_gaps {n : ℕ} {D : FiniteScaleSource n} {eta a sigma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i∈fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b k : ℕ) (hk : k ≤ b) (Esource : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (hsigma : 0 ≤ sigma)
    (hcap : 672/((2^k:ℕ):ℝ) ≤ sigma ∨ k=b)
    (i j : Tube D R a b) (he : oldAncestor D R a b k i=oldAncestor D R a b k j) :
    ‖planarBase h R a level b Esource O c i-planarBase h R a level b Esource O c j‖ ≤ sigma ∧
      ‖planarSlope h R a level b Esource O c i-planarSlope h R a level b Esource O c j‖ ≤ sigma := by
  have hh := capped_chart_gaps h hK ha R level b k hk Esource O hO c hc hsigma hcap i j he
  exact ⟨max_le (hh.2 0) (hh.2 1),
    max_le (hh.1 0) (hh.1 1)⟩

/-- Scalar endpoint/fine-label counting uses the unchanged original
phase partition, so its later population lower is an ORIGINAL-source law. -/
theorem scalar_original_ancestor_count {Point Fine : Type*} [DecidableEq Point] [DecidableEq Fine]
    {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (level b k : ℕ) (_hk : k ≤ b) (Esource : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (I : Finset (Point × Tube D R a b)) (E : Finset Point) (height x : Point → ℝ)
    (Phi : Point → Finset Fine) (fine : Fine → ℝ) (center : Point → ℝ)
    (rho : ℝ) (realizer : Point → Fine → Tube D R a b)
    {delta sigma IncErr FineErr z Lrho Cdir : ℝ}
    (hsigma : 0 < sigma) (hd : delta ≤ sigma)
    (hgap : ∀ i j : Tube D R a b, oldAncestor D R a b k i=oldAncestor D R a b k j →
      (∀ v : Fin 3, |slope (line h R a level b Esource O c i) v-
        slope (line h R a level b Esource O c j) v| ≤ sigma) ∧
      ∀ v : Fin 3, |intercept (line h R a level b Esource O c i) v-
        intercept (line h R a level b Esource O c j) v| ≤ sigma)
    (hInc : 0 ≤ IncErr) (hFine : 0 ≤ FineErr) (hCdir : 0 ≤ Cdir)
    (hz : |z| ≤ 1) (hheight : ∀ p∈E, height p=z)
    (hinc : ∀ p t, (p,t)∈I →
      ‖incidenceResidual height x (scalarBase h R a level b Esource O c) (scalarSlope h R a level b Esource O c) p t‖ ≤ IncErr*delta)
    (hrealizer : ∀ p∈E, ∀ d∈Phi p, (p,realizer p d)∈I)
    (hfit : ∀ p∈E, ∀ d∈Phi p, ‖fine d-scalarSlope h R a level b Esource O c (realizer p d)‖ ≤ FineErr*delta)
    (hlower : ∀ p∈E, Lrho ≤ ((nearDirections Phi fine center rho p).card:ℝ))
    (hball : ∀ p∈E, ∀ b : ℝ,
      (((Phi p).filter (fun d => ‖fine d-b‖ ≤ (1+FineErr)*sigma)).card:ℝ) ≤ Cdir)
    (hgrid : Set.InjOn (fun p => ⌊x p/sigma⌋) (↑E)) :
    (E.card:ℝ)*Lrho ≤
      ((occupiedAncestors E Phi fine center rho (oldAncestor D R a b k) realizer).card:ℝ)*
        ((6+2*IncErr)*Cdir) := by
  let ancestor := oldAncestor D R a b k
  have hparam (i j : Tube D R a b) (he : ancestor i=ancestor j) :
      ‖scalarBase h R a level b Esource O c i-scalarBase h R a level b Esource O c j‖ ≤ sigma ∧
      ‖scalarSlope h R a level b Esource O c i-scalarSlope h R a level b Esource O c j‖ ≤ sigma := by
    have hh := hgap i j he
    exact ⟨hh.2 0, hh.1 0⟩
  apply original_pair_ancestor_count E Phi fine center rho ancestor realizer hCdir hlower
  · intro k hk
    obtain ⟨p0, _hp0, d0, _hd0, href⟩ :=
      occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
    let ref := realizer p0 d0
    let A := activePoints E Phi fine center rho ancestor realizer k
    have hgridA : Set.InjOn (fun p => ⌊x p/sigma⌋) (↑A) := by
      intro p hp q hq heq
      exact hgrid (mem_filter.mp hp).1 (mem_filter.mp hq).1 heq
    have hnear : ∀ p∈A, ‖x p-(scalarBase h R a level b Esource O c ref+z • scalarSlope h R a level b Esource O c ref)‖ ≤
        (2+IncErr)*sigma := by
      intro p hp
      exact active_points_in_ancestor_ball I E height x (scalarBase h R a level b Esource O c) (scalarSlope h R a level b Esource O c)
        Phi fine center rho ancestor realizer hd hInc hz hheight hinc hrealizer hparam k ref href p hp
    have hh := NativeTangentGridCoarsening.scalar_injective_grid_centered_card A x hsigma
      (show 0 ≤ 2+IncErr by positivity) hgridA hnear
    simpa only [show 2*(2+IncErr)+2=6+2*IncErr by ring] using hh
  · intro p hp k hk
    exact original_direction_fiber_bound E Phi fine center rho ancestor realizer
      (scalarSlope h R a level b Esource O c) hd hFine hfit (fun s t heq => (hparam s t heq).2) hball p hp k hk

/-- The two-dimensional tangent case uses the same unchanged phase
partition and the same original fine-direction realizers. -/
theorem planar_original_ancestor_count {Point Fine : Type*} [DecidableEq Point] [DecidableEq Fine]
    {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (level b k : ℕ) (_hk : k ≤ b) (Esource : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (I : Finset (Point × Tube D R a b)) (E : Finset Point) (height : Point → ℝ) (x : Point → ℝ × ℝ)
    (Phi : Point → Finset Fine) (fine : Fine → ℝ × ℝ) (center : Point → ℝ × ℝ)
    (rho : ℝ) (realizer : Point → Fine → Tube D R a b)
    {delta sigma IncErr FineErr z Lrho Cdir : ℝ}
    (hsigma : 0 < sigma) (hd : delta ≤ sigma)
    (hgap : ∀ i j : Tube D R a b, oldAncestor D R a b k i=oldAncestor D R a b k j →
      (∀ v : Fin 3, |slope (line h R a level b Esource O c i) v-
        slope (line h R a level b Esource O c j) v| ≤ sigma) ∧
      ∀ v : Fin 3, |intercept (line h R a level b Esource O c i) v-
        intercept (line h R a level b Esource O c j) v| ≤ sigma)
    (hInc : 0 ≤ IncErr) (hFine : 0 ≤ FineErr) (hCdir : 0 ≤ Cdir)
    (hz : |z| ≤ 1) (hheight : ∀ p∈E, height p=z)
    (hinc : ∀ p t, (p,t)∈I →
      ‖incidenceResidual height x (planarBase h R a level b Esource O c) (planarSlope h R a level b Esource O c) p t‖ ≤ IncErr*delta)
    (hrealizer : ∀ p∈E, ∀ d∈Phi p, (p,realizer p d)∈I)
    (hfit : ∀ p∈E, ∀ d∈Phi p, ‖fine d-planarSlope h R a level b Esource O c (realizer p d)‖ ≤ FineErr*delta)
    (hlower : ∀ p∈E, Lrho ≤ ((nearDirections Phi fine center rho p).card:ℝ))
    (hball : ∀ p∈E, ∀ b : ℝ × ℝ,
      (((Phi p).filter (fun d => ‖fine d-b‖ ≤ (1+FineErr)*sigma)).card:ℝ) ≤ Cdir)
    (hgrid : Set.InjOn (fun p => (⌊(x p).1/sigma⌋, ⌊(x p).2/sigma⌋)) (↑E)) :
    (E.card:ℝ)*Lrho ≤
      ((occupiedAncestors E Phi fine center rho (oldAncestor D R a b k) realizer).card:ℝ)*
        ((6+2*IncErr)^2*Cdir) := by
  let ancestor := oldAncestor D R a b k
  have hparam (i j : Tube D R a b) (he : ancestor i=ancestor j) :
      ‖planarBase h R a level b Esource O c i-planarBase h R a level b Esource O c j‖ ≤ sigma ∧
      ‖planarSlope h R a level b Esource O c i-planarSlope h R a level b Esource O c j‖ ≤ sigma := by
    have hh := hgap i j he
    exact ⟨max_le (hh.2 0) (hh.2 1), max_le (hh.1 0) (hh.1 1)⟩
  apply original_pair_ancestor_count E Phi fine center rho ancestor realizer hCdir hlower
  · intro k hk
    obtain ⟨p0, _hp0, d0, _hd0, href⟩ :=
      occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
    let ref := realizer p0 d0
    let A := activePoints E Phi fine center rho ancestor realizer k
    have hgridA : Set.InjOn (fun p => (⌊(x p).1/sigma⌋, ⌊(x p).2/sigma⌋)) (↑A) := by
      intro p hp q hq heq
      exact hgrid (mem_filter.mp hp).1 (mem_filter.mp hq).1 heq
    have hnear : ∀ p∈A, ‖x p-(planarBase h R a level b Esource O c ref+z • planarSlope h R a level b Esource O c ref)‖ ≤
        (2+IncErr)*sigma := by
      intro p hp
      exact active_points_in_ancestor_ball I E height x (planarBase h R a level b Esource O c) (planarSlope h R a level b Esource O c)
        Phi fine center rho ancestor realizer hd hInc hz hheight hinc hrealizer hparam k ref href p hp
    have hcoords : ∀ p∈A,
        |(x p).1-(planarBase h R a level b Esource O c ref+z • planarSlope h R a level b Esource O c ref).1| ≤ (2+IncErr)*sigma ∧
        |(x p).2-(planarBase h R a level b Esource O c ref+z • planarSlope h R a level b Esource O c ref).2| ≤ (2+IncErr)*sigma := by
      intro p hp
      exact max_le_iff.mp (hnear p hp)
    have hh := NativeTangentGridCoarsening.planar_injective_grid_centered_card A x
      (planarBase h R a level b Esource O c ref+z • planarSlope h R a level b Esource O c ref) hsigma
      (show 0 ≤ 2+IncErr by positivity) hgridA hcoords
    simpa only [show 2*(2+IncErr)+2=6+2*IncErr by ring] using hh
  · intro p hp k hk
    exact original_direction_fiber_bound E Phi fine center rho ancestor realizer
      (planarSlope h R a level b Esource O c) hd hFine hfit (fun s t heq => (hparam s t heq).2) hball p hp k hk

end NativeOldPhaseAncestorCount
