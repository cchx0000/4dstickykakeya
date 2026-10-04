import Theorems.Thm_StickyKakeya4_native_euclidean_cover_input
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCoverADRepresentatives
open Classical Finset NativeDyadicTubeStopping NativeEuclideanCoverInput
open EuclideanAlignmentPatches ADGridCoverMenus FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

/-- One ORIGINAL point in each occupied cell, with no separation assumption. -/
theorem exists_original_representatives {X Z : Type*} [DecidableEq X] [DecidableEq Z] (Y : Finset X) (f : X → Z) :
    ∃ R : Finset X, R ⊆ Y ∧ R.image f = Y.image f ∧ Set.InjOn f (R : Set X) := by
  obtain ⟨S,hSY,hbij⟩ := Set.exists_subset_bijOn (Y : Set X) f
  have hfin : S.Finite := Y.finite_toSet.subset hSY
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    exact hSY (hfin.mem_toFinset.mp hx)
  · apply Finset.coe_injective
    simpa only [Finset.coe_image, hfin.coe_toFinset] using hbij.image_eq
  · simpa only [hfin.coe_toFinset] using hbij.injOn

lemma injective_subset_card_le_cover {Y R S : Finset Plane} {delta : ℝ}
    (hRY : R ⊆ Y) (hinj : Set.InjOn (gridLabel delta) (R : Set Plane))
    (hSR : S ⊆ R) {a : Plane} {r : ℝ} (hball : S ⊆ eball Y a r) :
    (S.card : ℝ) ≤ ecover Y delta a r := by
  have _hSY := hSR.trans hRY
  have hi : Set.InjOn (gridLabel delta) (S : Set Plane) := hinj.mono hSR
  unfold ecover
  rw [← Finset.card_image_of_injOn hi]
  exact_mod_cast card_le_card (image_subset_image hball)

lemma half_grid_card {Y : Finset Plane}
    (hbox : ∀ p ∈ Y, ∀ i : Fin 2, |p i| ≤ 1) :
    (Y.image (gridLabel (1/2))).card ≤ 25 := by
  let box : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ => Icc (-2 : ℤ) 2)
  have hs : Y.image (gridLabel (1/2)) ⊆ box := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    have hpi := abs_le.mp (hbox p hp i)
    have hlo : (-2 : ℝ) ≤ p i / (1/2) := by linarith
    have hhi : p i / (1/2) ≤ (2 : ℝ) := by linarith
    exact mem_Icc.mpr ⟨by simpa only [gridLabel,show ⌊(-2:ℝ)⌋ = (-2:ℤ) by norm_num] using Int.floor_mono hlo,
      by simpa [gridLabel] using Int.floor_mono hhi⟩
  have hc : box.card = 25 := by
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    decide
  exact (card_le_card hs).trans_eq hc

/-- The full square is covered using actual original half-unit cells; each
nonempty cell lies in a Euclidean unit ball about one of its original points. -/
lemma representative_total_upper {Y R : Finset Plane} {delta K t : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 ≤ K)
    (hbox : ∀ p ∈ Y, ∀ i : Fin 2, |p i| ≤ 1)
    (H : EuclideanCoverAD Y delta K t) (hRY : R ⊆ Y)
    (hinj : Set.InjOn (gridLabel delta) (R : Set Plane)) :
    (R.card : ℝ) ≤ 25*K*(1/delta)^t := by
  have hfib (z : Fin 2 → ℤ) (hz : z ∈ R.image (gridLabel (1/2))) :
      ((R.filter (fun p => gridLabel (1/2) p=z)).card : ℝ) ≤ K*(1/delta)^t := by
    obtain ⟨a,ha,haz⟩ := mem_image.mp hz
    have hb : R.filter (fun p => gridLabel (1/2) p=z) ⊆ eball Y a 1 := by
      intro p hp
      obtain ⟨hpR,hpz⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨hRY hpR, ?_⟩
      have hh := same_cell_euclidean_dist_le (1/2) (by norm_num) p a (hpz.trans haz.symm)
      norm_num at hh
      exact hh
    exact (injective_subset_card_le_cover hRY hinj (filter_subset _ _) hb).trans
      (H a (hRY ha) 1 hd1 le_rfl).2
  have hsum : (R.card : ℝ) = ∑z ∈ R.image (gridLabel (1/2)),
      ((R.filter (fun p => gridLabel (1/2) p=z)).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image (gridLabel (1/2)) R
  rw [hsum]
  calc
    _ ≤ ∑_z ∈ R.image (gridLabel (1/2)), K*(1/delta)^t := sum_le_sum hfib
    _ = ((R.image (gridLabel (1/2))).card : ℝ)*(K*(1/delta)^t) := by simp
    _ ≤ 25*(K*(1/delta)^t) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast half_grid_card (fun p hp => hbox p (hRY hp))) (mul_nonneg hK (by positivity))
    _ = _ := by ring

/-- Literal Euclidean occupied-cell AD gives point-count AD on an original
representative subset. The grid label is injective; metric separation is not claimed. -/
theorem original_representatives_AD {Y : Finset Plane} {delta K t : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hbox : ∀ p ∈ Y, ∀ i : Fin 2, |p i| ≤ 1)
    (H : EuclideanCoverAD Y delta K t) :
    ∃ R : Finset Plane, R ⊆ Y ∧ R.image (gridLabel delta) = Y.image (gridLabel delta) ∧
      Set.InjOn (gridLabel delta) (R : Set Plane) ∧ ADBounds R delta (100*K) t := by
  obtain ⟨R,hRY,himage,hinj⟩ := exists_original_representatives Y (gridLabel delta)
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num) hK
  refine ⟨R,hRY,himage,hinj,?_⟩
  intro a ha r hdr hr1
  have hr : 0 < r := hd.trans_le hdr
  have hp : 0 ≤ (r/delta)^t := by positivity
  have htwo : (2:ℝ)^t ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht2
    norm_num at hh
    exact hh
  constructor
  · by_cases hsmall : r < 2*delta
    · have hbase : r/delta ≤ 2 := (div_le_iff₀ hd).mpr hsmall.le
      have hpow : (r/delta)^t ≤ 4 := (Real.rpow_le_rpow (by positivity) hbase ht).trans htwo
      have hcard : (1:ℝ) ≤ (carrierBall R a r).card := by
        exact_mod_cast card_pos.mpr (show (carrierBall R a r).Nonempty from
          ⟨a,mem_filter.mpr ⟨ha,by simpa using hr.le⟩⟩)
      apply le_trans _ hcard
      apply (div_le_iff₀ (show 0<100*K by positivity)).mpr
      nlinarith
    · have hhalf : delta ≤ r/2 := by linarith
      have hcover : ecover Y delta a (r/2) ≤ (carrierBall R a r).card := by
        unfold ecover
        have hs : (eball Y a (r/2)).image (gridLabel delta) ⊆
            (carrierBall R a r).image (gridLabel delta) := by
          intro z hz
          obtain ⟨p,hpY,hpz⟩ := mem_image.mp hz
          have hzY : z ∈ Y.image (gridLabel delta) := mem_image.mpr ⟨p,(mem_filter.mp hpY).1,hpz⟩
          rw [← himage] at hzY
          obtain ⟨q,hq,hqz⟩ := mem_image.mp hzY
          refine mem_image.mpr ⟨q,mem_filter.mpr ⟨hq,?_⟩,hqz⟩
          have hnear := SeparatedAlignmentPatches.same_cell_dist_lt delta hd q p (hqz.trans hpz.symm)
          have hpdist := (sup_dist_le p a).trans (mem_filter.mp hpY).2
          exact (dist_triangle q p a).trans (by linarith)
        exact_mod_cast (card_le_card hs).trans card_image_le
      have hl := (H a (hRY ha) (r/2) hhalf (by linarith)).1.trans hcover
      have hpow : (r/delta)^t ≤ 4*((r/2)/delta)^t := by
        have he : r/delta = 2*((r/2)/delta) := by ring
        rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]
        exact mul_le_mul_of_nonneg_right htwo (by positivity)
      apply (div_le_iff₀ (show 0<100*K by positivity)).mpr
      have hh := (div_le_iff₀ hKp).mp hl
      have hc : (0:ℝ) ≤ (carrierBall R a r).card := by positivity
      nlinarith
  · by_cases hsmall : r ≤ 1/2
    · have hb : carrierBall R a r ⊆ eball Y a (2*r) := by
        intro p hpR
        obtain ⟨hpR,hpr⟩ := mem_filter.mp hpR
        refine mem_filter.mpr ⟨hRY hpR,?_⟩
        have hh := euclidean_dist_le_card_mul p a r hr.le (fun i => by
          simpa only [Real.dist_eq] using (dist_le_pi_dist p a i).trans hpr)
        simpa only [Fintype.card_fin,Nat.cast_ofNat] using hh
      have hc := (injective_subset_card_le_cover hRY hinj (filter_subset _ _) hb).trans
        (H a (hRY ha) (2*r) (by linarith) (by linarith)).2
      have hpow : ((2*r)/delta)^t ≤ 4*(r/delta)^t := by
        rw [mul_div_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]
        exact mul_le_mul_of_nonneg_right htwo hp
      exact hc.trans ((mul_le_mul_of_nonneg_left hpow hKp.le).trans (by nlinarith [mul_nonneg hKp.le hp]))
    · have hc : ((carrierBall R a r).card:ℝ) ≤ R.card := by
        exact_mod_cast card_le_card (filter_subset _ _)
      have htot := representative_total_upper hd hd1 hKp.le hbox H hRY hinj
      have hbase : 1/delta ≤ 2*(r/delta) := by
        apply (div_le_iff₀ hd).mpr
        have he : (2*(r/delta))*delta = 2*r := by field_simp
        rw [he]
        linarith
      have hpow : (1/delta)^t ≤ 4*(r/delta)^t := by
        have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/delta) hbase ht
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at hh
        exact hh.trans (mul_le_mul_of_nonneg_right htwo hp)
      exact (hc.trans htot).trans ((mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 25*K)).trans_eq (by ring))
end NativeCoverADRepresentatives
