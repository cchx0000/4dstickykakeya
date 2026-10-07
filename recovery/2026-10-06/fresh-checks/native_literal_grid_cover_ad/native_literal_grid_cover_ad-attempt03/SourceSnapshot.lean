import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeLiteralGridCoverAD
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening NativeLiteralGridOverlap
attribute [local instance] Classical.propDecidable

def label {l : ℕ} (rho : ℝ) (x : Fin l → ℝ) : Fin l → ℤ := fun j => ⌊x j/rho⌋

def representatives {l : ℕ} (A : Finset (Fin l → ℝ)) (rho : ℝ) : Finset (Fin l → ℝ) :=
  (A.image (label rho)).image (center rho)

/-- Literal occupied half-open rho-cubes of the original points inside
an original closed ball. The carrier is never replaced by grid centers. -/
def coverCount {l : ℕ} (A : Finset (Fin l → ℝ)) (rho : ℝ) (a : Fin l → ℝ) (r : ℝ) : ℝ :=
  ((carrierBall A a r).image (label rho)).card

def CoverADBounds {l : ℕ} (A : Finset (Fin l → ℝ)) (rho K s : ℝ) : Prop :=
  ∀a∈A,∀r : ℝ,rho ≤ r → r ≤ 1 →
    (r/rho)^s/K ≤ coverCount A rho a r ∧ coverCount A rho a r ≤ K*(r/rho)^s

lemma center_label_close {l : ℕ} {rho : ℝ} (hrho : 0 < rho) (x : Fin l → ℝ) :
    dist (center rho (label rho x)) x ≤ rho/2 := by
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ rho/2)).mpr
  intro j
  rw [Real.dist_eq]
  have hlo := (le_div_iff₀ hrho).mp (Int.floor_le (x j/rho))
  have hhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (x j/rho))
  dsimp [center,label]
  exact abs_le.mpr ⟨by nlinarith only [hhi],by nlinarith only [hlo]⟩

lemma anchor_mem {l : ℕ} (A : Finset (Fin l → ℝ)) (rho : ℝ) (a : Fin l → ℝ) (ha : a∈A) :
    center rho (label rho a)∈representatives A rho :=
  mem_image.mpr ⟨label rho a,mem_image_of_mem _ ha,rfl⟩

lemma upper_card {l : ℕ} (A : Finset (Fin l → ℝ)) {rho r : ℝ}
    (hrho : 0 < rho) (a : Fin l → ℝ) (hrrho : rho ≤ r) :
    coverCount A rho a r ≤
      ((carrierBall (representatives A rho) (center rho (label rho a)) (2*r)).card:ℝ) := by
  have hsub : ((carrierBall A a r).image (label rho)).image (center rho) ⊆
      carrierBall (representatives A rho) (center rho (label rho a)) (2*r) := by
    intro y hy
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
    obtain ⟨hxA,hxa⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨anchor_mem A rho x hxA,?_⟩
    have hx := center_label_close hrho x
    have ha := center_label_close hrho a
    have h1 := dist_triangle (center rho (label rho x)) x a
    have h2 := dist_triangle (center rho (label rho x)) a (center rho (label rho a))
    rw [dist_comm a (center rho (label rho a))] at h2
    linarith only [h1,h2,hx,ha,hxa,hrrho]
  have hc := card_le_card hsub
  rw [card_image_of_injective _ (center_injective hrho)] at hc
  exact Nat.cast_le.mpr hc

lemma lower_card {l : ℕ} (A : Finset (Fin l → ℝ)) {rho r : ℝ}
    (hrho : 0 < rho) (a : Fin l → ℝ) (hlarge : 2*rho ≤ r) :
    ((carrierBall (representatives A rho) (center rho (label rho a)) (r/2)).card:ℝ) ≤
      coverCount A rho a r := by
  have hsub : carrierBall (representatives A rho) (center rho (label rho a)) (r/2) ⊆
      ((carrierBall A a r).image (label rho)).image (center rho) := by
    intro y hy
    obtain ⟨hyP,hyd⟩ := mem_filter.mp hy
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hyP
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
    apply mem_image.mpr
    refine ⟨label rho x,mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,?_⟩,rfl⟩,rfl⟩
    have hxc := center_label_close hrho x
    have hac := center_label_close hrho a
    have h1 := dist_triangle x (center rho (label rho x)) (center rho (label rho a))
    have h2 := dist_triangle x (center rho (label rho a)) a
    rw [dist_comm x (center rho (label rho x))] at h1
    linarith only [h1,h2,hxc,hac,hyd,hlarge]
  have hc := card_le_card hsub
  rw [card_image_of_injective _ (center_injective hrho)] at hc
  exact Nat.cast_le.mpr hc

/-- Center AD gives the paper's occupied-cube AD for the literal original
union. The large-radius upper uses an independent global count. The small
radius lower uses an original point, not an AD test below rho. -/
theorem cover_AD_of_representatives {l : ℕ} (A : Finset (Fin l → ℝ))
    {rho K G s : ℝ} (hrho : 0 < rho) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds (representatives A rho) rho K s)
    (Hglobal : ((representatives A rho).card:ℝ) ≤ G*rho^(-s)) :
    CoverADBounds A rho ((2:ℝ)^s*max K G) s := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hmax : 0 < max K G := hKp.trans_le (le_max_left _ _)
  have htwo : 0 < (2:ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
  intro a ha r hrrho hr1
  have hr : 0 < r := hrho.trans_le hrrho
  have hac := anchor_mem A rho a ha
  have hratio : 0 ≤ (r/rho)^s := Real.rpow_nonneg (by positivity) _
  have hdouble : ((2*r)/rho)^s = (2:ℝ)^s*(r/rho)^s := by
    rw [show (2*r)/rho=2*(r/rho) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  constructor
  · by_cases hlarge : 2*rho ≤ r
    · have hlow := (H _ hac (r/2) (by linarith only [hlarge]) (by linarith only [hr1,hr])).1
      have hhalf : ((r/2)/rho)^s = (r/rho)^s/(2:ℝ)^s := by
        rw [show (r/2)/rho=(r/rho)/2 by ring,Real.div_rpow (by positivity) (by norm_num)]
      rw [hhalf,div_div] at hlow
      have hden : (2:ℝ)^s*K ≤ (2:ℝ)^s*max K G :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) htwo.le
      exact (div_le_div_of_nonneg_left hratio (mul_pos htwo hKp) hden).trans
        (hlow.trans (lower_card A hrho a hlarge))
    · have hpow : (r/rho)^s ≤ (2:ℝ)^s := Real.rpow_le_rpow (by positivity)
        ((div_le_iff₀ hrho).mpr (by linarith only [hlarge])) hs
      have hone : (1:ℝ) ≤ coverCount A rho a r := by
        apply Nat.one_le_cast.mpr
        apply card_pos.mpr
        exact ⟨label rho a,mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,by simp [hr.le]⟩,rfl⟩⟩
      have hden : (2:ℝ)^s ≤ (2:ℝ)^s*max K G :=
        le_mul_of_one_le_right htwo.le (hK.trans (le_max_left _ _))
      exact ((div_le_one (mul_pos htwo hmax)).mpr (hpow.trans hden)).trans hone
  · by_cases hsmall : 2*r ≤ 1
    · have hu := (H _ hac (2*r) (by linarith only [hrrho,hr]) hsmall).2
      rw [hdouble] at hu
      calc
        _ ≤ _ := upper_card A hrho a hrrho
        _ ≤ K*((2:ℝ)^s*(r/rho)^s) := hu
        _ ≤ max K G*((2:ℝ)^s*(r/rho)^s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg htwo.le hratio)
        _ = _ := by ring
    · have hcard : coverCount A rho a r ≤ ((representatives A rho).card:ℝ) := by
        have hsub : carrierBall A a r ⊆ A := filter_subset _ _
        have hc := card_le_card (image_subset_image (f:=label rho) hsub)
        dsimp [representatives]
        rw [card_image_of_injective _ (center_injective hrho)]
        exact Nat.cast_le.mpr hc
      have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/rho)
        (div_le_div_of_nonneg_right (by linarith only [hsmall] : (1:ℝ) ≤ 2*r) hrho.le) hs
      have hunit : (1/rho)^s = rho^(-s) := by
        rw [Real.div_rpow (by norm_num) hrho.le,Real.one_rpow,Real.rpow_neg hrho.le,one_div]
      rw [hunit,hdouble] at hpow
      calc
        _ ≤ _ := hcard
        _ ≤ G*rho^(-s) := Hglobal
        _ ≤ max K G*rho^(-s) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ max K G*((2:ℝ)^s*(r/rho)^s) := mul_le_mul_of_nonneg_left hpow hmax.le
        _ = _ := by ring

end NativeLiteralGridCoverAD
