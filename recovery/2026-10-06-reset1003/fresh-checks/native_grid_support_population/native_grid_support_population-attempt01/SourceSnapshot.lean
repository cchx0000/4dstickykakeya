import Theorems.Thm_StickyKakeya4_native_literal_grid_cover_ad
import Theorems.Thm_StickyKakeya4_native_recoded_grid_upper
import Theorems.Thm_StickyKakeya4_native_displaced_ad_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeGridSupportPopulation
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeLiteralGridCoverAD NativeRecodedGridUpper
open scoped BigOperators

/-- A bounded genuine fine AD set has an actual global count. Unit-grid
fibers are centered at original points before applying the unit-radius
upper bound; the support box is not asserted to be one unit ball. -/
theorem global_card_of_bounded_AD {d : ℕ} (A : Finset (Fin d → ℝ))
    {mu K t : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hK : 0 < K)
    (H : ADBounds A mu K t) (hbox : ∀x∈A,dist x 0 ≤ 2) :
    (A.card:ℝ) ≤ ((13^d:ℕ):ℝ)*K*mu^(-t) := by
  let B := A.image (label 1)
  have hB : B.card ≤ 13^d := by
    have hsub : B ⊆ B.filter (fun q => dist (center 1 q) 0 ≤ (3:ℝ)*1) := by
      intro q hq
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
      refine mem_filter.mpr ⟨mem_image_of_mem _ hx,?_⟩
      have hc := center_label_close (by norm_num : (0:ℝ)<1) x
      have ht := dist_triangle (center 1 (label 1 x)) x 0
      linarith only [hc,ht,hbox x hx]
    exact (card_le_card hsub).trans (by simpa using grid_ball_card_le B (by norm_num : (0:ℝ)<1) 0 3)
  have hfiber : ∀q∈B,((A.filter (fun x => label 1 x=q)).card:ℝ) ≤ K*mu^(-t) := by
    intro q hq
    obtain ⟨x,hx,hxq⟩ := mem_image.mp hq
    have hsub : A.filter (fun y => label 1 y=q) ⊆ carrierBall A x 1 := by
      intro y hy
      obtain ⟨hyA,hyq⟩ := mem_filter.mp hy
      have hxclose := center_label_close (by norm_num : (0:ℝ)<1) x
      have hyclose := center_label_close (by norm_num : (0:ℝ)<1) y
      rw [hxq] at hxclose
      rw [hyq,dist_comm] at hyclose
      have ht := dist_triangle y (center 1 q) x
      apply (mem_carrierBall A y x 1).mpr
      exact ⟨hyA,by linarith only [ht,hxclose,hyclose]⟩
    have hbound := (H x hx 1 hmu1 le_rfl).2
    have hunit : (1/mu)^t=mu^(-t) := by
      rw [Real.div_rpow (by norm_num) hmu.le,Real.one_rpow,Real.rpow_neg hmu.le,one_div]
    rw [hunit] at hbound
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans hbound
  have hc := FinePointSlabGeometry.card_le_real_mul_of_fibers A B (label 1) (K*mu^(-t))
    (fun x hx => mem_image_of_mem _ hx) hfiber
  exact hc.trans (by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hB) (by positivity : 0≤K*mu^(-t))
    simpa only [mul_assoc] using hh)

/-- AD lower populations around actual witnesses and literal grid overlap
control the number of occupied coarse cubes. The separate global count is
retained explicitly; no coarse AD or spatial-support count is a premise. -/
theorem occupied_keys_of_AD {d : ℕ} (A : Finset (Fin d → ℝ))
    {mu rho K G t : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 0 < K) (H : ADBounds A mu K t) (hglobal : (A.card:ℝ) ≤ G*mu^(-t)) :
    ((A.image (label rho)).card:ℝ) ≤ ((9^d:ℕ):ℝ)*K*G*rho^(-t) := by
  have hrho : 0 < rho := hmu.trans_le hmurho
  let B := A.image (label rho)
  let witness : (Fin d → ℤ) → (Fin d → ℝ) := fun q =>
    if hq : q∈B then Classical.choose (mem_image.mp hq) else 0
  have hw : ∀q∈B,witness q∈A ∧ label rho (witness q)=q := by
    intro q hq
    dsimp only [witness]
    rw [dif_pos hq]
    exact Classical.choose_spec (mem_image.mp hq)
  have hclose : ∀q∈B,dist (center rho q) (witness q) ≤ rho/2 := by
    intro q hq
    have hh := center_label_close hrho (witness q)
    rw [(hw q hq).2] at hh
    exact hh
  let M : ℝ := ((9^d:ℕ):ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hrows : (B.card:ℝ)*((rho/mu)^t/K) ≤
      ∑q∈B,((A.filter (fun x => dist x (witness q) ≤ rho)).card:ℝ) := by
    calc
      _ = ∑_q∈B,(rho/mu)^t/K := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro q hq
        exact (H (witness q) (hw q hq).1 rho hmurho hrho1).1
  have hcols : ∀x∈A,((B.filter (fun q => dist x (witness q) ≤ rho)).card:ℝ) ≤ M := by
    intro x _hx
    have hsub : B.filter (fun q => dist x (witness q) ≤ rho) ⊆
        B.filter (fun q => dist (center rho q) x ≤ (2:ℝ)*rho) := by
      intro q hq
      obtain ⟨hqB,hqx⟩ := mem_filter.mp hq
      have ht := dist_triangle (center rho q) (witness q) x
      have hc := hclose q hqB
      have hqx' : dist (witness q) x ≤ rho := by simpa only [dist_comm] using hqx
      exact mem_filter.mpr ⟨hqB,by linarith only [ht,hc,hqx',hrho]⟩
    have hc := (card_le_card hsub).trans (grid_ball_card_le B hrho x 2)
    exact_mod_cast hc
  have hcounts : (B.card:ℝ)*((rho/mu)^t/K) ≤ (A.card:ℝ)*M := by
    calc
      _ ≤ ∑q∈B,((A.filter (fun x => dist x (witness q) ≤ rho)).card:ℝ) := hrows
      _ = ∑x∈A,((B.filter (fun q => dist x (witness q) ≤ rho)).card:ℝ) :=
        incidence_sum_swap B A (fun q x => dist x (witness q) ≤ rho)
      _ ≤ ∑_x∈A,M := sum_le_sum hcols
      _ = _ := by simp
  have hcounts' : ((B.card:ℝ)*(rho/mu)^t)/K ≤ (A.card:ℝ)*M := by
    simpa only [mul_div_assoc] using hcounts
  have hmass := (div_le_iff₀ hK).mp hcounts'
  have hratio : rho^(-t)*(rho/mu)^t=mu^(-t) := by
    rw [Real.rpow_neg hrho.le,Real.div_rpow hrho.le hmu.le,Real.rpow_neg hmu.le]
    field_simp
  have hfinal : (B.card:ℝ)*(rho/mu)^t ≤ (M*K*G*rho^(-t))*(rho/mu)^t := by
    calc
      _ ≤ (A.card:ℝ)*M*K := hmass
      _ ≤ (G*mu^(-t))*M*K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hglobal hM) hK.le
      _ = _ := by rw [←hratio]; ring
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos (div_pos hrho hmu) t)).mp hfinal

/-- Bounded fine AD produces the desired coarse support exponent, rather
than an ambient-dimensional fine-grid cardinality estimate. -/
theorem bounded_AD_occupied_keys {d : ℕ} (A : Finset (Fin d → ℝ))
    {mu rho K t : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 0 < K) (H : ADBounds A mu K t) (hbox : ∀x∈A,dist x 0 ≤ 2) :
    ((A.image (label rho)).card:ℝ) ≤ ((9^d:ℕ):ℝ)*((13^d:ℕ):ℝ)*K^2*rho^(-t) := by
  have hg := global_card_of_bounded_AD A hmu (hmurho.trans hrho1) hK H hbox
  have hh := occupied_keys_of_AD A hmu hmurho hrho1 hK H hg
  convert hh using 1 <;> ring

end NativeGridSupportPopulation
