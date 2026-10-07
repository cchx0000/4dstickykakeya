import Theorems.Thm_StickyKakeya4_native_phase_height_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeSourceParentPopulationProfile
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeActivePhasePopulation
open NativePopulationParentSelection NativePhaseHeightPopulation NativeMiddleWindowBalance

/-- Choose one actual phase parent from the original source density and the
actual two selection costs. On that same parent, the unchanged E2 has all
fine-phase and translated-height population bounds. The chosen mixed-core
parent also retains every same-R reference at the explicitly paid ratio. -/
theorem source_parent_population_profile {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hsmall : D.thickness ≤ 1/8)
    (E1 E2 H : Finset (Fin n × Index)) (h1R : E1⊆retained original R)
    (h21 : E2⊆E1) (hH2 : H⊆E2) (hHn : H.Nonempty)
    (F1 G W : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hW : 0 < W)
    (hfirst : (incidences original).card ≤ F1*E1.card)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsecond : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (hhalf : W ≤ 2*H.card) (m : ℕ) (hm6 : 6 ≤ m) (hm : m ≤ level) :
    let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
    let mu := theta*D.thickness^eta
    let rho := 64/((2^m:ℕ):ℝ)
    0 < theta ∧ 0 < mu ∧ ∃p∈R.image (parentLabel D a (2^m)),
      (parentEdges D a (2^m) H p).Nonempty ∧
      mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
        D.thickness*(parentEdges D a (2^m) H p).card ∧
      (∀I⊆retained original R,
        (mu/rowConstant)*(parentEdges D a (2^m) I p).card ≤
          (parentEdges D a (2^m) H p).card) ∧
      mu ≤ (43904*rho)*(heightLabels D a rho (parentEdges D a (2^m) E2 p)).card ∧
      rho*(heightLabels D a rho (parentEdges D a (2^m) E2 p)).card ≤ 10 ∧
      ∀f : ℕ,m ≤ f → f ≤ level →
        (mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
          rowConstant*(activePhases D a f (parentEdges D a (2^m) E2 p)).card ∧
        ((activePhases D a f (parentEdges D a (2^m) E2 p)).card:ℝ) ≤
          D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) ∧
        mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
          (43904*rho)*(phaseHeightLabels D a rho f (parentEdges D a (2^m) E2 p)).card := by
  intro theta mu rho
  obtain ⟨ht,hmu,p,hp,hHpn,hpop,href⟩ := source_population_parent h original Hbackbone.1 hsmall R
    E1 E2 H h1R h21 hH2 hHn F1 G W hF1 hG hW hfirst lambda hlambda hsecond hhalf m
  have hHp2 : parentEdges D a (2^m) H p⊆parentEdges D a (2^m) E2 p := filter_subset_filter _ hH2
  have hFp : (parentEdges D a (2^m) E2 p).Nonempty := hHpn.mono hHp2
  have hFR : parentEdges D a (2^m) E2 p⊆retained original R :=
    (filter_subset _ _).trans (h21.trans h1R)
  have hparent : ∀z∈parentEdges D a (2^m) E2 p,parentLabel D a (2^m) z.1=p :=
    fun _z hz => (mem_filter.mp hz).2
  have hpopF : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E2 p).card :=
    hpop.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hHp2)) h.1.2.1.le)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm6
    norm_num only [show (2:ℕ)^6=64 by norm_num] at hh
    exact_mod_cast hh
  refine ⟨ht,hmu,p,hp,hHpn,hpop,href,?_,?_,?_⟩
  · exact parent_height_population h original R level Hbackbone m hm
      (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hpopF
  · apply height_population_upper h original Hbackbone.1 Hbackbone.2.2.1 rho hrho hrho1
    exact hFR.trans (filter_subset _ _)
  · intro f hmf hfl
    exact ⟨active_phase_population h original R level Hbackbone m f hmf hfl
        (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hmu.le hpopF,
      phase_height_population h original R level Hbackbone m f hmf hfl
        (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hmu.le hpopF⟩

end NativeSourceParentPopulationProfile
