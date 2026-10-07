import Theorems.Thm_StickyKakeya4_native_fixed_reference_angular_profile
import Theorems.Thm_StickyKakeya4_native_grain_quotient_bins
import Theorems.Thm_StickyKakeya4_native_rank_radius_rounding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeFixedReferenceAllRadiusAngularProfile
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeGenericReferenceData NativeFixedReferenceAngularProfile
open NativeActualMesoscopicRankConfiguration NativeFixedSizeScaleMenu NativeMiddleWindowBalance
open NativeFixedCompactKakeyaExponent
open scoped BigOperators

def angularConstant : ℝ := 343*1537^3

lemma ball_count_mono {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (k : Index) (v : E4) {r s : ℝ} (hrs : r ≤ s) :
    (ballDirections D E k v r).card ≤ (ballDirections D E k v s).card := by
  apply card_le_card
  apply image_subset_image
  intro z hz
  exact mem_filter.mpr ⟨(mem_filter.mp hz).1,(mem_filter.mp hz).2.1,
    (mem_filter.mp hz).2.2.trans hrs⟩

lemma occupied_ball_one {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (i : Fin n) (k : Index) (hik : (i,k)∈E) {r : ℝ} (hr : 0 ≤ r) :
    (1:ℝ) ≤ (ballDirections D E k (direction (D.line i)) r).card := by
  apply Nat.one_le_cast.mpr
  apply card_pos.mpr
  exact ⟨direction (D.line i),mem_image.mpr ⟨(i,k),mem_filter.mpr
    ⟨hik,rfl,by simpa only [dist_self] using hr⟩,rfl⟩⟩

lemma same_grid_close {rho : ℝ} (hrho : 0<rho) (x y : E4)
    (he : NativeGrainQuotientBins.label (rho/4) x=NativeGrainQuotientBins.label (rho/4) y) :
    dist x y ≤ rho := by
  have hs := SeparatedAlignmentPatches.same_cell_dist_lt (rho/4) (by positivity)
    (fun j => x j) (fun j => y j) he
  have hc (j : Fin 4) : |x j-y j| ≤ rho/4 := by
    have hcoord : |x j-y j| ≤ dist (fun j => x j) (fun j => y j) := by
      simpa only [Real.dist_eq] using dist_le_pi_dist (fun j => x j) (fun j => y j) j
    exact hcoord.trans hs.le
  have hh := EuclideanAlignmentPatches.euclidean_dist_le_card_mul
    (fun j => x j) (fun j => y j) (rho/4) (by positivity) hc
  change dist x y ≤ (4:ℝ)*(rho/4) at hh
  linarith

/-- Literal ambient four-dimensional floor cells cover any direction ball.
This proof partitions existing incidences and never selects a new reference. -/
lemma ball_upper_transfer {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (E : Finset (Fin n × Index))
    (k : Index) (v : E4) (r rho K U : ℝ) (hr : 0 ≤ r) (hrho : 0<rho)
    (hK : 1 ≤ K) (hscale : r ≤ K*rho) (hU : 0 ≤ U)
    (H : ∀u : E4,((ballDirections D E k u rho).card:ℝ) ≤ U) :
    ((ballDirections D E k v r).card:ℝ) ≤ 10000*K^4*U := by
  let B := ballIncidences D E k v r
  let f := fun z : Fin n × Index => NativeGrainQuotientBins.label (rho/4) (direction (D.line z.1))
  have hcells : ((B.image f).card:ℝ) ≤ (2*r/(rho/4)+2)^4 :=
    NativeGrainQuotientBins.occupied_card B (fun z => direction (D.line z.1))
      (by positivity) hr v (fun z hz => by
        simpa only [dist_eq_norm] using (mem_filter.mp hz).2.2)
  have hlinear : 2*r/(rho/4)+2 ≤ 10*K := by
    have hdiv : r/rho ≤ K := (div_le_iff₀ hrho).mpr hscale
    rw [show 2*r/(rho/4)+2=8*(r/rho)+2 by ring]
    linarith
  have hcount : ((B.image f).card:ℝ) ≤ 10000*K^4 := by
    calc
      _ ≤ (2*r/(rho/4)+2)^4 := hcells
      _ ≤ (10*K)^4 := pow_le_pow_left₀ (by positivity) hlinear 4
      _ = _ := by ring
  have hf (q : Fin 4 → ℤ) (hq : q∈B.image f) : ((B.filter (fun z => f z=q)).card:ℝ) ≤ U := by
    obtain ⟨z0,hz0,hzq⟩ := mem_image.mp hq
    have hsub : B.filter (fun z => f z=q)⊆ballIncidences D E k (direction (D.line z0.1)) rho := by
      intro z hz
      obtain ⟨hzB,hzq'⟩ := mem_filter.mp hz
      obtain ⟨hzE,hzk,_⟩ := mem_filter.mp hzB
      exact mem_filter.mpr ⟨hzE,hzk,same_grid_close hrho _ _ (hzq'.trans hzq.symm)⟩
    have hh := H (direction (D.line z0.1))
    rw [ballDirections_card h] at hh
    exact (show ((B.filter (fun z => f z=q)).card:ℝ) ≤ 
      (ballIncidences D E k (direction (D.line z0.1)) rho).card by exact_mod_cast card_le_card hsub).trans hh
  have hsum : (B.card:ℝ)=∑q∈B.image f,((B.filter (fun z => f z=q)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image f B
  rw [ballDirections_card h]
  change (B.card:ℝ) ≤ _
  calc
    _ = _ := hsum
    _ ≤ ∑_q∈B.image f,U := sum_le_sum hf
    _ = ((B.image f).card:ℝ)*U := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hU

def scheduledRadius {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) : ℝ :=
  64/((2^(ref.schedule j).val:ℕ):ℝ)

lemma scheduledRadius_pos {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) : 0<scheduledRadius ref j := by
  unfold scheduledRadius
  positivity

lemma reference_schedule_eq {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) :
    ref.schedule=windowSchedule (rankWindow tau) (rankWindow_pos htau).le g ref.level :=
  ref.schedule_eq.trans (fullSchedule_eq_rankWindow tau htau g ref.level)

lemma scheduledRadius_rank {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) :
    scheduledRadius ref j=3072*NativeRankRadiusMenu.radius
      (rankWindow tau) (rankWindow_pos htau).le g ref.level j := by
  unfold scheduledRadius NativeRankRadiusMenu.radius
  rw [reference_schedule_eq ref]
  ring

lemma first_radius_lower {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0<g)
    (hgrid : 1/(g:ℝ)<rankWindow tau/4) :
    32*D.thickness^(rankWindow tau/2) ≤ scheduledRadius ref 0 := by
  have hw := rankWindow_pos htau
  have hwsmall : rankWindow tau<1/2 :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num : (1/8:ℝ)<1/2)
  have hlarge := large_level_of_grid _ hw g ref.level hg hgrid ref.grid_depth
  have hh := NativeRankRadiusRounding.first_radius_lower (rankWindow tau) hw hwsmall
    g ref.level hlarge ref.backbone.2.1
  rw [scheduledRadius_rank ref]
  linarith

lemma last_radius_upper {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0<g) :
    scheduledRadius ref (Fin.last g) ≤ 128*D.thickness^(1-rankWindow tau/2) := by
  let w := rankWindow tau
  have hw : 0<w := rankWindow_pos htau
  have hm : (1-w/2)*(ref.level:ℝ)-1 ≤ ((ref.schedule (Fin.last g)).val:ℝ) := by
    rw [reference_schedule_eq ref,windowSchedule_last w hw.le g ref.level hg]
    have hh := Nat.lt_floor_add_one ((1-w/2)*(ref.level:ℝ))
    change (1-w/2)*(ref.level:ℝ)-1 ≤ (⌊(1-w/2)*(ref.level:ℝ)⌋₊:ℝ)
    linarith
  have hd : D.thickness=(2:ℝ)^(-(ref.level:ℝ)) := by
    simp only [ref.backbone.2.1,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have hp : 1/((2^(ref.schedule (Fin.last g)).val:ℕ):ℝ) ≤ 
      2*D.thickness^(1-w/2) := by
    calc
      _ = (2:ℝ)^(-((ref.schedule (Fin.last g)).val:ℝ)) := by
        simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
          Nat.cast_pow,Nat.cast_ofNat,one_div]
      _ ≤ (2:ℝ)^(1-(ref.level:ℝ)*(1-w/2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hm])
      _ = 2*(2:ℝ)^(-(ref.level:ℝ)*(1-w/2)) := by
        rw [show 1-(ref.level:ℝ)*(1-w/2)=1+(-(ref.level:ℝ)*(1-w/2)) by ring,
          Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      _ = _ := by rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  change 64/((2^(ref.schedule (Fin.last g)).val:ℕ):ℝ) ≤ _
  calc
    _ = 64*(1/((2^(ref.schedule (Fin.last g)).val:ℕ):ℝ)) := by ring
    _ ≤ 64*(2*D.thickness^(1-w/2)) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by dsimp [w]; ring

lemma middle_radius_bracket {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0<g)
    (hgrid : 1/(g:ℝ)<rankWindow tau/4) (r : ℝ)
    (hlo : scheduledRadius ref (Fin.last g) ≤ r) (hhi : r ≤ scheduledRadius ref 0) :
    ∃j : Fin (g+1), scheduledRadius ref j ≤ r ∧
      r ≤ (2*D.thickness^(-(1/(g:ℝ))))*scheduledRadius ref j := by
  let w := rankWindow tau
  have hw : 0<w := rankWindow_pos htau
  have hwsmall : w<1/2 :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num : (1/8:ℝ)<1/2)
  have hlarge := large_level_of_grid w hw g ref.level hg hgrid ref.grid_depth
  have hlo' : NativeRankRadiusMenu.radius w hw.le g ref.level (Fin.last g) ≤ r/3072 := by
    rw [scheduledRadius_rank ref] at hlo
    linarith
  have hhi' : r/3072 ≤ NativeRankRadiusMenu.radius w hw.le g ref.level 0 := by
    rw [scheduledRadius_rank ref] at hhi
    linarith
  obtain ⟨j,_hj,hjr,hrj⟩ := NativeRankRadiusRounding.exists_near_radius w hw hwsmall
    g ref.level hg hlarge ref.backbone.2.1 ref.level (Fin.last g)
    (Nat.le_of_lt_succ (windowSchedule w hw.le g ref.level (Fin.last g)).isLt)
    (r/3072) hlo' hhi'
  refine ⟨j,?_,?_⟩ <;> rw [scheduledRadius_rank ref]
  · linarith
  · nlinarith

/-- One scalar enlargement pays both clipped endpoints and all schedule gaps. -/
def enlargement (delta tau : ℝ) : ℝ := 128*delta^(-rankWindow tau)

lemma enlargement_one {delta tau : ℝ} (hd : 0<delta) (hd1 : delta ≤ 1) (htau : 0<tau) :
    1 ≤ enlargement delta tau := by
  have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1
    (neg_nonpos.mpr (rankWindow_pos htau).le)
  unfold enlargement
  linarith

lemma all_radius_alternative {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0<g)
    (hgrid : 1/(g:ℝ)<rankWindow tau/4) (r : ℝ) (hr1 : r ≤ 1) :
    (∃j : Fin (g+1),scheduledRadius ref j ≤ r ∧ r ≤ enlargement D.thickness tau*scheduledRadius ref j) ∨
    (r ≤ scheduledRadius ref (Fin.last g) ∧
      scheduledRadius ref (Fin.last g) ≤ enlargement D.thickness tau*D.thickness) := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hw := rankWindow_pos htau
  by_cases hr : scheduledRadius ref (Fin.last g) ≤ r
  · left
    by_cases hfirst : r ≤ scheduledRadius ref 0
    · obtain ⟨j,hjr,hrj⟩ := middle_radius_bracket ref hg hgrid r hr hfirst
      refine ⟨j,hjr,hrj.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (scheduledRadius_pos ref j).le
      have hgsmall : 1/(g:ℝ) ≤ rankWindow tau := by linarith
      have hh := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hgsmall)
      unfold enlargement
      have hp := Real.rpow_pos_of_pos hd (-rankWindow tau)
      nlinarith
    · refine ⟨0,(le_of_not_ge hfirst),?_⟩
      have hfirstLow := first_radius_lower ref hg hgrid
      have hp : D.thickness^(rankWindow tau) ≤ D.thickness^(rankWindow tau/2) :=
        Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      have hpos := Real.rpow_pos_of_pos hd (rankWindow tau/2)
      have hlow : D.thickness^(rankWindow tau) ≤ scheduledRadius ref 0 := by linarith
      have hh := mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg hd.le (-rankWindow tau))
      rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero] at hh
      unfold enlargement
      have hmul : 0 ≤ D.thickness^(-rankWindow tau)*scheduledRadius ref 0 :=
        mul_nonneg (Real.rpow_nonneg hd.le _) (scheduledRadius_pos ref 0).le
      nlinarith
  · right
    refine ⟨(lt_of_not_ge hr).le,?_⟩
    have hh := last_radius_upper ref hg
    have hp : D.thickness^(1-rankWindow tau/2) ≤ D.thickness^(1-rankWindow tau) :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    have he : D.thickness^(1-rankWindow tau)=D.thickness^(-rankWindow tau)*D.thickness := by
      calc
        _ = D.thickness^(-rankWindow tau+1) := by congr 1; ring
        _ = D.thickness^(-rankWindow tau)*D.thickness^1 := Real.rpow_add hd _ _
        _ = _ := by rw [Real.rpow_one]
    calc
      _ ≤ 128*D.thickness^(1-rankWindow tau/2) := hh
      _ ≤ 128*D.thickness^(1-rankWindow tau) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = _ := by rw [he]; unfold enlargement; ring

/-- The actual stored retention cost pays the sole square-radix loss.
The tolerance in Reference's type is unchanged. -/
lemma paid_scheduled_bounds {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (heta : 0 ≤ eta)
    (hseed : seed ≤ tau/16384) (j : Fin (g+1)) :
    (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 →
      D.thickness^(tau/16)*(scheduledRadius ref j/D.thickness)^extremalExponent ≤ 
        (ballDirections D ref.E1 k (direction (D.line i)) (scheduledRadius ref j)).card) ∧
    (∀ (k : Index) (v : E4),
      ((ballDirections D ref.E1 k v (scheduledRadius ref j)).card:ℝ) ≤ 
        angularConstant*D.thickness^(-(tau/16))*(scheduledRadius ref j/D.thickness)^extremalExponent) := by
  let Q := coreRadix ref.original ref.R L
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hQ : (Q:ℝ)^2 ≤ D.thickness^(-(seed/8)) :=
    radix_sq_le_of_transfer_cost hd hd1 heta (factor ref.dimension (g+1) L) Q
      (NativeGenericReferenceData.factor_pos ref) ref.cost
  have hQn : 0<Q := lt_of_lt_of_le (by norm_num : 0<4) (NativeSourceSizeBounds.radix_four_le _ _)
  have hQp : (0:ℝ)<(Q:ℝ)^2 := by positivity
  have hmargin : seed+seed/8 ≤ tau/16 := by linarith
  have hloCost : (Q:ℝ)^2*D.thickness^(tau/16) ≤ D.thickness^seed := by
    calc
      _ ≤ D.thickness^(-(seed/8))*D.thickness^(tau/16) :=
        mul_le_mul_of_nonneg_right hQ (Real.rpow_nonneg hd.le _)
      _ = D.thickness^(tau/16-seed/8) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hhiCost : (Q:ℝ)^2*D.thickness^(-seed) ≤ D.thickness^(-(tau/16)) := by
    calc
      _ ≤ D.thickness^(-(seed/8))*D.thickness^(-seed) :=
        mul_le_mul_of_nonneg_right hQ (Real.rpow_nonneg hd.le _)
      _ = D.thickness^(-(seed+seed/8)) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  obtain ⟨hlo,hhi⟩ := scheduled_angular_power_profile ref j
  have hP : 0 ≤ (scheduledRadius ref j/D.thickness)^extremalExponent := by
    exact Real.rpow_nonneg (div_nonneg (scheduledRadius_pos ref j).le hd.le) _
  constructor
  · intro i k hik
    apply le_trans _ (hlo i k hik)
    apply (le_div_iff₀ hQp).mpr
    have hh := mul_le_mul_of_nonneg_right hloCost hP
    simpa only [scheduledRadius,mul_assoc,mul_comm,mul_left_comm] using hh
  · intro k v
    calc
      _ ≤ angularConstant*(Q:ℝ)^2*D.thickness^(-seed)*
          (scheduledRadius ref j/D.thickness)^extremalExponent := hhi k v
      _ = angularConstant*((Q:ℝ)^2*D.thickness^(-seed))*
          (scheduledRadius ref j/D.thickness)^extremalExponent := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhiCost (by norm_num [angularConstant])) hP

lemma ratio_power_le {x y delta K kappa : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0<delta)
    (hK : 1 ≤ K) (hk : 0 ≤ kappa) (hk3 : kappa ≤ 3) (hxy : x ≤ K*y) :
    (x/delta)^kappa ≤ K^3*(y/delta)^kappa := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hc : K^kappa ≤ K^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hK hk3
  calc
    _ ≤ (K*(y/delta))^kappa := Real.rpow_le_rpow (div_nonneg hx hd.le)
      (by simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hxy hd.le) hk
    _ = K^kappa*(y/delta)^kappa := Real.mul_rpow hK0 (div_nonneg hy hd.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (div_nonneg hy hd.le) _)

lemma cube_le_cover_cost {K : ℝ} (hK : 1 ≤ K) : K^3 ≤ 10000*K^4 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hpow : K^3 ≤ K^4 := by
    calc
      _ = K^3*1 := (mul_one _).symm
      _ ≤ K^3*K := mul_le_mul_of_nonneg_left hK (pow_nonneg hK0 3)
      _ = _ := by ring
  have hp : 0 ≤ K^4 := pow_nonneg hK0 4
  nlinarith

/-- All real radii, including both clipped endpoints, on the unchanged E1.
Every loss is displayed before the final source-independent absorption. -/
theorem all_radius_rough_bounds {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (heta : 0 ≤ eta)
    (hseed : seed ≤ tau/16384) (hg : 0<g) (hgrid : 1/(g:ℝ)<rankWindow tau/4)
    (r : ℝ) (hr : D.thickness ≤ r) (hr1 : r ≤ 1) :
    let K := enlargement D.thickness tau
    (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 →
      D.thickness^(tau/16)*(r/D.thickness)^extremalExponent/K^3 ≤ 
        (ballDirections D ref.E1 k (direction (D.line i)) r).card) ∧
    (∀ (k : Index) (v : E4),
      ((ballDirections D ref.E1 k v r).card:ℝ) ≤ 
        10000*K^4*angularConstant*D.thickness^(-(tau/16))*(r/D.thickness)^extremalExponent) := by
  intro K
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hrp : 0<r := hd.trans_le hr
  have hK : 1 ≤ K := enlargement_one hd hd1 htau
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hK3 : 0<K^3 := pow_pos hKp 3
  have hP : 0 ≤ (r/D.thickness)^extremalExponent := by positivity
  have hA : 0 ≤ D.thickness^(tau/16) := Real.rpow_nonneg hd.le _
  have hA1 : D.thickness^(tau/16) ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity)
  have hC : 0 ≤ angularConstant := by norm_num [angularConstant]
  rcases all_radius_alternative ref hg hgrid r hr1 with ⟨j,hjr,hrj⟩ | ⟨hrlast,hlast⟩
  · have hpaid := paid_scheduled_bounds ref heta hseed j
    have hjpos := scheduledRadius_pos ref j
    have hpow := ratio_power_le hrp.le (scheduledRadius_pos ref j).le hd hK
      extremalExponent_nonneg extremalExponent_le_three hrj
    constructor
    · intro i k hik
      apply (div_le_iff₀ hK3).mpr
      have hmon : ((ballDirections D ref.E1 k (direction (D.line i)) (scheduledRadius ref j)).card:ℝ) ≤ 
          (ballDirections D ref.E1 k (direction (D.line i)) r).card := by
        exact_mod_cast ball_count_mono D ref.E1 k (direction (D.line i)) hjr
      calc
        _ ≤ D.thickness^(tau/16)*(K^3*(scheduledRadius ref j/D.thickness)^extremalExponent) :=
          mul_le_mul_of_nonneg_left hpow hA
        _ = K^3*(D.thickness^(tau/16)*(scheduledRadius ref j/D.thickness)^extremalExponent) := by ring
        _ ≤ K^3*(ballDirections D ref.E1 k (direction (D.line i)) r).card :=
          mul_le_mul_of_nonneg_left ((hpaid.1 i k hik).trans hmon) hK3.le
        _ = _ := by ring
    · intro k v
      have hPj : (scheduledRadius ref j/D.thickness)^extremalExponent ≤ (r/D.thickness)^extremalExponent :=
        Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hjr hd.le) extremalExponent_nonneg
      have hh := ball_upper_transfer h ref.E1 k v r (scheduledRadius ref j) K
        (angularConstant*D.thickness^(-(tau/16))*(scheduledRadius ref j/D.thickness)^extremalExponent)
        hrp.le (scheduledRadius_pos ref j) hK hrj (by positivity) (hpaid.2 k)
      calc
        _ ≤ 10000*K^4*(angularConstant*D.thickness^(-(tau/16))*
            (scheduledRadius ref j/D.thickness)^extremalExponent) := hh
        _ ≤ 10000*K^4*(angularConstant*D.thickness^(-(tau/16))*(r/D.thickness)^extremalExponent) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPj (by positivity)) (by positivity)
        _ = _ := by ring
  · have hpaid := paid_scheduled_bounds ref heta hseed (Fin.last g)
    have hsmall : r ≤ K*D.thickness := hrlast.trans hlast
    have hpowSmall : (r/D.thickness)^extremalExponent ≤ K^3 := by
      have hh := ratio_power_le hrp.le hd.le hd hK extremalExponent_nonneg extremalExponent_le_three hsmall
      simpa only [div_self hd.ne',Real.one_rpow,mul_one] using hh
    have hlastR : scheduledRadius ref (Fin.last g) ≤ K*r :=
      hlast.trans (mul_le_mul_of_nonneg_left hr hKp.le)
    have hpowLast := ratio_power_le (scheduledRadius_pos ref (Fin.last g)).le hrp.le hd hK
      extremalExponent_nonneg extremalExponent_le_three hlastR
    constructor
    · intro i k hik
      have hone : D.thickness^(tau/16)*(r/D.thickness)^extremalExponent/K^3 ≤ 1 := by
        apply (div_le_one hK3).mpr
        exact (mul_le_mul hA1 hpowSmall hP (by norm_num)).trans_eq (one_mul _)
      exact hone.trans (occupied_ball_one D ref.E1 i k hik hrp.le)
    · intro k v
      have hmon : ((ballDirections D ref.E1 k v r).card:ℝ) ≤ 
          (ballDirections D ref.E1 k v (scheduledRadius ref (Fin.last g))).card := by
        exact_mod_cast ball_count_mono D ref.E1 k v hrlast
      calc
        _ ≤ angularConstant*D.thickness^(-(tau/16))*
            (scheduledRadius ref (Fin.last g)/D.thickness)^extremalExponent := hmon.trans (hpaid.2 k v)
        _ ≤ angularConstant*D.thickness^(-(tau/16))*(K^3*(r/D.thickness)^extremalExponent) :=
          mul_le_mul_of_nonneg_left hpowLast (by positivity)
        _ ≤ angularConstant*D.thickness^(-(tau/16))*((10000*K^4)*(r/D.thickness)^extremalExponent) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (cube_le_cover_cost hK) hP) (by positivity)
        _ = _ := by ring

/-- Both original-scale powers and the fixed constants are explicit. -/
theorem all_radius_power_bounds {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (heta : 0 ≤ eta)
    (hseed : seed ≤ tau/16384) (hg : 0<g) (hgrid : 1/(g:ℝ)<rankWindow tau/4)
    (r : ℝ) (hr : D.thickness ≤ r) (hr1 : r ≤ 1) :
    (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 →
      D.thickness^(tau/16+3*rankWindow tau)*(r/D.thickness)^extremalExponent/(128:ℝ)^3 ≤ 
        (ballDirections D ref.E1 k (direction (D.line i)) r).card) ∧
    (∀ (k : Index) (v : E4),
      ((ballDirections D ref.E1 k v r).card:ℝ) ≤ 
        (10000*128^4*angularConstant)*D.thickness^(-(tau/16+4*rankWindow tau))*(r/D.thickness)^extremalExponent) := by
  have hd := h.1.2.1
  have hp3 : (enlargement D.thickness tau)^3=(128:ℝ)^3*D.thickness^(-(3*rankWindow tau)) := by
    rw [enlargement,mul_pow,←Real.rpow_mul_natCast hd.le]
    congr 2
    ring
  have hp4 : (enlargement D.thickness tau)^4=(128:ℝ)^4*D.thickness^(-(4*rankWindow tau)) := by
    rw [enlargement,mul_pow,←Real.rpow_mul_natCast hd.le]
    congr 2
    ring
  obtain ⟨hlo,hhi⟩ := all_radius_rough_bounds ref heta hseed hg hgrid r hr hr1
  constructor
  · intro i k hik
    have hh := hlo i k hik
    have he : D.thickness^(tau/16)*(r/D.thickness)^extremalExponent/(enlargement D.thickness tau)^3 =
        D.thickness^(tau/16+3*rankWindow tau)*(r/D.thickness)^extremalExponent/(128:ℝ)^3 := by
      rw [hp3,Real.rpow_neg hd.le]
      rw [div_mul_eq_div_div,div_inv_eq_mul,Real.rpow_add hd]
      ring
    rwa [he] at hh
  · intro k v
    have hh := hhi k v
    have he : 10000*(enlargement D.thickness tau)^4*angularConstant*D.thickness^(-(tau/16)) =
        (10000*128^4*angularConstant)*D.thickness^(-(tau/16+4*rankWindow tau)) := by
      rw [hp4]
      calc
        _ = (10000*128^4*angularConstant)*(D.thickness^(-(4*rankWindow tau))*D.thickness^(-(tau/16))) := by ring
        _ = _ := by rw [←Real.rpow_add hd]; congr 2; ring
    rwa [he] at hh

/-- A single cutoff, fixed before every native source and Reference, yields
actual angular AD at every real radius sigma ≤ r ≤ 1 on this same E1. -/
theorem exists_all_radius_cutoff (tau : ℝ) (htau : 0<tau) :
    ∃delta0 : ℝ,0<delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (seed e zeta : ℝ) (L g : ℕ),
        0 ≤ eta → seed ≤ tau/16384 → 0<g → 1/(g:ℝ)<rankWindow tau/4 → D.thickness ≤ delta0 →
        ∀ref : Reference h tau htau seed e zeta L g,
          (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 → ∀r : ℝ,D.thickness ≤ r → r ≤ 1 →
            D.thickness^tau*(r/D.thickness)^extremalExponent ≤ 
              (ballDirections D ref.E1 k (direction (D.line i)) r).card) ∧
          (∀ (k : Index) (v : E4) (r : ℝ), D.thickness ≤ r → r ≤ 1 →
            ((ballDirections D ref.E1 k v r).card:ℝ) ≤ 
              D.thickness^(-tau)*(r/D.thickness)^extremalExponent) := by
  let C : ℝ := 10000*128^4*angularConstant
  have hC : 0 ≤ C := by norm_num [C,angularConstant]
  have hC3 : (128:ℝ)^3 ≤ C := by norm_num [C,angularConstant]
  obtain ⟨delta0,hdelta0,_hdelta1,H⟩ :=
    exists_positive_rpow_absorption_threshold (half_pos htau) hC (by norm_num : (0:ℝ)<1)
  refine ⟨delta0,hdelta0,?_⟩
  intro n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hconstant : C ≤ D.thickness^(-(tau/2)) := by
    have hh := H D.thickness hd hsmall
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd (tau/2))).mpr hh
  have hw : rankWindow tau ≤ tau/16000 := by exact (min_le_right _ _).trans_eq (by ring)
  have hmargin3 : tau/16+3*rankWindow tau ≤ tau/2 := by linarith
  have hmargin4 : tau/16+4*rankWindow tau ≤ tau/2 := by linarith
  have hloCoefficient : D.thickness^tau ≤ D.thickness^(tau/16+3*rankWindow tau)/(128:ℝ)^3 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<(128:ℝ)^3)).mpr
    calc
      _ ≤ D.thickness^tau*D.thickness^(-(tau/2)) :=
        mul_le_mul_of_nonneg_left (hC3.trans hconstant) (Real.rpow_nonneg hd.le _)
      _ = D.thickness^(tau/2) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hmargin3
  have hhiCoefficient : C*D.thickness^(-(tau/16+4*rankWindow tau)) ≤ D.thickness^(-tau) := by
    calc
      _ ≤ D.thickness^(-(tau/2))*D.thickness^(-(tau/16+4*rankWindow tau)) :=
        mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hd.le _)
      _ = D.thickness^(-(tau/2+tau/16+4*rankWindow tau)) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  constructor
  · intro i k hik r hr hr1
    have hlo := (all_radius_power_bounds ref heta hseed hg hgrid r hr hr1).1 i k hik
    have hp : 0 ≤ (r/D.thickness)^extremalExponent :=
      Real.rpow_nonneg (div_nonneg (hd.le.trans hr) hd.le) _
    exact (show D.thickness^tau*(r/D.thickness)^extremalExponent ≤ 
        D.thickness^(tau/16+3*rankWindow tau)*(r/D.thickness)^extremalExponent/(128:ℝ)^3 from
      (mul_le_mul_of_nonneg_right hloCoefficient hp).trans_eq (by ring)).trans hlo
  · intro k v r hr hr1
    have hhi := (all_radius_power_bounds ref heta hseed hg hgrid r hr hr1).2 k v
    exact hhi.trans (mul_le_mul_of_nonneg_right hhiCoefficient
      (Real.rpow_nonneg (div_nonneg (hd.le.trans hr) hd.le) _))

end NativeFixedReferenceAllRadiusAngularProfile
