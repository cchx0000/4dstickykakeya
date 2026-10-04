import Theorems.Thm_StickyKakeya4_planar_shifted_near_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace ActualPlanarRoundedEnergy
open PlanarShiftedNearEnergy TwoTubePathCollisionCount
noncomputable section

lemma planar_rounding_injOn (X : Finset (ℝ×ℝ)) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖) :
    Set.InjOn (roundPoint (delta/2)) X := by
  intro x hx y hy heq
  by_contra hne
  have hb := hsep x hx y hy hne
  have heta : 0 < delta/2 := by positivity
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  dsimp [roundPoint] at h1 h2
  have hx1 := ActualRoundedAdditiveEnergy.round_error heta x.1
  have hy1 := ActualRoundedAdditiveEnergy.round_error heta y.1
  have hx2 := ActualRoundedAdditiveEnergy.round_error heta x.2
  have hy2 := ActualRoundedAdditiveEnergy.round_error heta y.2
  rw [← h1] at hy1
  rw [← h2] at hy2
  have hb1 : |x.1-y.1| < delta/2 := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  have hb2 : |x.2-y.2| < delta/2 := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  have hm := max_lt hb1 hb2
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] at hb
  linarith

lemma planar_rounded_card (X : Finset (ℝ×ℝ)) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖) :
    (X.image (roundPoint (delta/2))).card = X.card :=
  Finset.card_image_of_injOn (planar_rounding_injOn X hdelta hsep)

private lemma collisions_image_card {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (A : Finset P) (g : P → Q) (f : Q → ℤ×ℤ) (hg : Set.InjOn g A) :
    (collisions A (fun p => f (g p))).card = (collisions (A.image g) f).card := by
  apply Finset.card_bij (fun p _ => (g p.1,g p.2))
  · intro p hp
    obtain ⟨hp₁,hp₂,heq⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    exact (mem_collisions (A.image g) f _).mpr ⟨Finset.mem_image_of_mem g hp₁,
      Finset.mem_image_of_mem g hp₂,heq⟩
  · intro p hp q hq heq
    obtain ⟨hp₁,hp₂,_⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    obtain ⟨hq₁,hq₂,_⟩ := (mem_collisions A (fun p => f (g p)) q).mp hq
    exact Prod.ext (hg hp₁ hq₁ (congrArg Prod.fst heq)) (hg hp₂ hq₂ (congrArg Prod.snd heq))
  · intro q hq
    obtain ⟨hq₁,hq₂,heq⟩ := (mem_collisions (A.image g) f q).mp hq
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hq₁
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hq₂
    refine ⟨(a,b),(mem_collisions A (fun p => f (g p)) _).mpr ⟨ha,hb,?_⟩,?_⟩
    · simpa only [hea,heb] using heq
    · exact Prod.ext hea heb

lemma rounded_planar_product_image (X Y : Finset (ℝ×ℝ)) (δ : ℝ) :
    (X.product Y).image (fun p => (roundPoint δ p.1,roundPoint δ p.2)) =
      (X.image (roundPoint δ)).product (Y.image (roundPoint δ)) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp₁,Finset.mem_image_of_mem _ hp₂⟩
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    obtain ⟨x,hx,hex⟩ := Finset.mem_image.mp hq₁
    obtain ⟨y,hy,hey⟩ := Finset.mem_image.mp hq₂
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Prod.ext hex hey⟩


lemma rounded_planar_label_energy (X Y : Finset (ℝ×ℝ)) {delta : ℝ}
    (hdelta : 0 < delta)
    (hX : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖)
    (hY : ∀ x∈Y, ∀ y∈Y, x≠y → delta/2 ≤ ‖x-y‖) :
    (collisions (X.product Y)
      (fun p => roundPoint (delta/2) p.1+roundPoint (delta/2) p.2)).card =
      Finset.addEnergy (X.image (roundPoint (delta/2))) (Y.image (roundPoint (delta/2))) := by
  classical
  have hg : Set.InjOn
      (fun p : (ℝ×ℝ)×(ℝ×ℝ) => (roundPoint (delta/2) p.1,roundPoint (delta/2) p.2))
      (X.product Y) := by
    intro p hp q hq heq
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
    exact Prod.ext ((planar_rounding_injOn X hdelta hX) hp1 hq1 (congrArg Prod.fst heq))
      ((planar_rounding_injOn Y hdelta hY) hp2 hq2 (congrArg Prod.snd heq))
  have h := collisions_image_card (X.product Y)
    (fun p : (ℝ×ℝ)×(ℝ×ℝ) => (roundPoint (delta/2) p.1,roundPoint (delta/2) p.2))
    (fun q => q.1+q.2) hg
  rw [rounded_planar_product_image] at h
  calc
    _ = _ := h
    _ = _ := by
      simpa only [collisions,Finset.product_eq_sprod] using
        (Finset.addEnergy_eq_card_filter (X.image (roundPoint (delta/2)))
          (Y.image (roundPoint (delta/2)))).symm

/-- A literal original planar approximate-sum-energy input gives the exact
Z² energy used by the proved group-valued asymmetric BSG construction. -/
theorem original_planar_near_energy (X Y : Finset (ℝ×ℝ)) {delta : ℝ}
    (hdelta : 0 < delta)
    (hX : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖)
    (hY : ∀ x∈Y, ∀ y∈Y, x≠y → delta/2 ≤ ‖x-y‖) :
    (coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card ≤
      49*Finset.addEnergy (X.image (roundPoint (delta/2))) (Y.image (roundPoint (delta/2))) := by
  have h := original_labelled_planar_rounding (X.product Y) Prod.fst Prod.snd hdelta
  rw [rounded_planar_label_energy X Y hdelta hX hY] at h
  exact h

lemma max_norm_separation_of_euclidean_squared {x y : ℝ×ℝ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hsep : delta^2 ≤ (x.1-y.1)^2+(x.2-y.2)^2) : delta/2 ≤ ‖x-y‖ := by
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
  let M := max |x.1-y.1| |x.2-y.2|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have h1 : (x.1-y.1)^2 ≤ M^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x.1-y.1)) (le_max_left _ _) 2
  have h2 : (x.2-y.2)^2 ≤ M^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x.2-y.2)) (le_max_right _ _) 2
  change delta/2 ≤ M
  by_contra h
  have hlt : M < delta/2 := lt_of_not_ge h
  nlinarith

/-- Euclidean separation supplies the required max-norm separation. The
squared-distance input is the literal two-coordinate Euclidean condition. -/
theorem original_euclidean_planar_near_energy (X Y : Finset (ℝ×ℝ)) {delta : ℝ}
    (hdelta : 0 < delta)
    (hX : ∀ x∈X, ∀ y∈X, x≠y → delta^2 ≤ (x.1-y.1)^2+(x.2-y.2)^2)
    (hY : ∀ x∈Y, ∀ y∈Y, x≠y → delta^2 ≤ (x.1-y.1)^2+(x.2-y.2)^2) :
    (coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card ≤
      49*Finset.addEnergy (X.image (roundPoint (delta/2))) (Y.image (roundPoint (delta/2))) := by
  exact original_planar_near_energy X Y hdelta
    (fun x hx y hy hne => max_norm_separation_of_euclidean_squared hdelta (hX x hx y hy hne))
    (fun x hx y hy hne => max_norm_separation_of_euclidean_squared hdelta (hY x hx y hy hne))
end
end ActualPlanarRoundedEnergy
