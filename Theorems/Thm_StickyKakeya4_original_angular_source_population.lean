import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
import Theorems.Thm_StickyKakeya4_original_separated_height_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalAngularSourcePopulation
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

/-- An actual subfamily of diameter at most one is controlled by the source AD
law at a member of that subfamily. -/
lemma unit_diameter_card (Phi S : Finset ℝ) {mesh K kappa : ℝ}
    (hm0 : 0 < mesh) (hm : mesh ≤ 1) (hK : 0 ≤ K) (hAD : ADBounds Phi mesh K kappa)
    (hS : S ⊆ Phi) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    (S.card : ℝ) ≤ K*(1/mesh)^kappa := by
  by_cases hne : S.Nonempty
  · obtain ⟨c,hc⟩ := hne
    have hsub : S ⊆ carrierBall Phi c 1 := by
      intro x hx
      exact (mem_carrierBall _ _ _ _).mpr ⟨hS hx,hdiam x hx c hc⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hAD c (hS hc) 1 hm le_rfl).2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hK (Real.rpow_nonneg (by positivity) _)

/-- The literal intervals [-1,0] and (0,1] partition the original alphabet.
Their diameters are at most one, so the source local AD law gives a global
cardinality cap, without an additional global regularity hypothesis. -/
theorem boxed_AD_card (Phi : Finset ℝ) {mesh K kappa : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hK : 0 ≤ K)
    (hAD : ADBounds Phi mesh K kappa) (hbox : ∀ x ∈ Phi, |x| ≤ 1) :
    (Phi.card : ℝ) ≤ 4*K*(1/mesh)^kappa := by
  let L := Phi.filter (fun x => x ≤ 0)
  let R := Phi.filter (fun x => ¬ x ≤ 0)
  have hL : (L.card : ℝ) ≤ K*(1/mesh)^kappa := by
    apply unit_diameter_card Phi L hm hm1 hK hAD (Finset.filter_subset _ _)
    intro x hx y hy
    obtain ⟨hxP,hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyP,hy0⟩ := Finset.mem_filter.mp hy
    have hxbox := abs_le.mp (hbox x hxP)
    have hybox := abs_le.mp (hbox y hyP)
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hR : (R.card : ℝ) ≤ K*(1/mesh)^kappa := by
    apply unit_diameter_card Phi R hm hm1 hK hAD (Finset.filter_subset _ _)
    intro x hx y hy
    obtain ⟨hxP,hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyP,hy0⟩ := Finset.mem_filter.mp hy
    have hxbox := abs_le.mp (hbox x hxP)
    have hybox := abs_le.mp (hbox y hyP)
    have hxpos : 0 < x := lt_of_not_ge hx0
    have hypos : 0 < y := lt_of_not_ge hy0
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsum : (L.card : ℝ)+(R.card : ℝ)=(Phi.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Phi) (fun x : ℝ => x ≤ 0)
  have hnonneg : 0 ≤ K*(1/mesh)^kappa := by positivity
  nlinarith only [hL,hR,hsum,hnonneg]

/-- The original local AD upper law extends to every center and every radius
at least the mesh. The large-radius case uses the literal interval count. -/
theorem boxed_AD_allcenter (Phi : Finset ℝ) {mesh K kappa : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hK : 0 ≤ K) (hk : 0 ≤ kappa)
    (hAD : ADBounds Phi mesh K kappa) (hbox : ∀ x ∈ Phi, |x| ≤ 1)
    (center r : ℝ) (hr : mesh ≤ r) :
    ((carrierBall Phi center r).card : ℝ) ≤ 4*K*(2*r/mesh)^kappa := by
  have hr0 : 0 < r := hm.trans_le hr
  by_cases hsmall : 2*r ≤ 1
  · by_cases hne : (carrierBall Phi center r).Nonempty
    · obtain ⟨c,hc⟩ := hne
      obtain ⟨hcP,hcd⟩ := (mem_carrierBall _ _ _ _).mp hc
      have hsub : carrierBall Phi center r ⊆ carrierBall Phi c (2*r) := by
        intro x hx
        obtain ⟨hxP,hxd⟩ := (mem_carrierBall _ _ _ _).mp hx
        refine (mem_carrierBall _ _ _ _).mpr ⟨hxP,?_⟩
        have htri := dist_triangle x center c
        rw [dist_comm center c] at htri
        linarith
      have hcap := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hAD c hcP (2*r) (by linarith) hsmall).2
      have hnonneg : 0 ≤ K*(2*r/mesh)^kappa := by positivity
      nlinarith only [hcap,hnonneg]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      positivity
  · have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/mesh)
      (div_le_div_of_nonneg_right (by linarith : 1 ≤ 2*r) hm.le) hk
    calc
      _ ≤ (Phi.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      _ ≤ 4*K*(1/mesh)^kappa := boxed_AD_card Phi hm hm1 hK hAD hbox
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

variable {T : Type*} [DecidableEq T]

/-- Every original fine label selects an actual source tube. Repeated tube
values are retained only once in this image. -/
def selectedTubes (fine : Finset ℝ) (source : ℝ → T) : Finset T := fine.image source

/-- Arbitrary source u-ball radii are allowed, including those larger than
one. The source AD law is extended by literal interval counting above. -/
theorem selected_ball_cap_general (fine : Finset ℝ) (source : ℝ → T) (u : T → ℝ)
    {delta K kappa C r : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hr : delta ≤ r)
    (hK : 0 ≤ K) (hk : 0 ≤ kappa) (hC : 0 ≤ C)
    (hAD : ADBounds fine delta K kappa) (hbox : ∀ phi ∈ fine, |phi| ≤ 1)
    (hrealize : ∀ phi ∈ fine, |u (source phi)-phi| ≤ C*delta) (a : ℝ) :
    (((selectedTubes fine source).filter (fun t => |u t-a| ≤ r)).card : ℝ) ≤
      4*K*(2*(r+C*delta)/delta)^kappa := by
  have hsub : (selectedTubes fine source).filter (fun t => |u t-a| ≤ r) ⊆
      (carrierBall fine a (r+C*delta)).image source := by
    intro t ht
    obtain ⟨htS,hta⟩ := Finset.mem_filter.mp ht
    obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp htS
    apply Finset.mem_image.mpr
    refine ⟨phi,(mem_carrierBall _ _ _ _).mpr ⟨hphi,?_⟩,rfl⟩
    have htri := abs_add_le (phi-u (source phi)) (u (source phi)-a)
    have herr := hrealize phi hphi
    rw [abs_sub_comm phi (u (source phi))] at htri
    rw [Real.dist_eq]
    have hid : (phi-u (source phi))+(u (source phi)-a)=phi-a := by ring
    rw [hid] at htri
    linarith
  exact (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)).trans
    (boxed_AD_allcenter fine hd hd1 hK hk hAD hbox a (r+C*delta) (by nlinarith))

/-- Source separation bounds how many fine labels can select one tube. -/
theorem source_label_fiber_cap (fine : Finset ℝ) (source : ℝ → T) (u : T → ℝ)
    {delta C : ℝ} (hd : 0 < delta) (hC : 0 ≤ C) (hsep : Separated fine delta)
    (hrealize : ∀ phi ∈ fine, |u (source phi)-phi| ≤ C*delta) (t : T) :
    ((fine.filter (fun phi => source phi=t)).card : ℝ) ≤ 2*C+2 := by
  have hsub : fine.filter (fun phi => source phi=t) ⊆
      fine.filter (fun phi => u t-C*delta ≤ phi ∧ phi ≤ u t-C*delta+2*C*delta) := by
    intro phi hp
    obtain ⟨hpf,hpt⟩ := Finset.mem_filter.mp hp
    have hh := hrealize phi hpf
    rw [hpt] at hh
    have ha := abs_le.mp hh
    exact Finset.mem_filter.mpr ⟨hpf,by linarith,by linarith⟩
  have hs : ∀ z ∈ fine, ∀ w ∈ fine, z ≠ w → delta ≤ |z-w| := by
    intro z hz w hw hne
    simpa only [Real.dist_eq] using hsep z hz w hw hne
  have hb := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (OriginalSeparatedHeightCap.separated_interval_cap fine hd hs (u t-C*delta) (2*C*delta) (by positivity))
  have heq : 2*C*delta/delta+2=2*C+2 := by field_simp
  rwa [heq] at hb

/-- The lower source AD population survives taking the actual selected tube
image, with precisely the label-fiber loss supplied by source separation. -/
theorem selected_degree_lower (fine : Finset ℝ) (source : ℝ → T) (u : T → ℝ)
    {delta K kappa C : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 0 < K)
    (hC : 0 ≤ C) (hne : fine.Nonempty) (hAD : ADBounds fine delta K kappa)
    (hsep : Separated fine delta)
    (hrealize : ∀ phi ∈ fine, |u (source phi)-phi| ≤ C*delta) :
    (1/delta)^kappa/(K*(2*C+2)) ≤ ((selectedTubes fine source).card : ℝ) := by
  have hsum : (fine.card : ℝ) = ∑ t ∈ fine.image source,
      ((fine.filter (fun phi => source phi=t)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image source fine
  have hmass : (fine.card : ℝ) ≤ ((selectedTubes fine source).card : ℝ)*(2*C+2) := by
    rw [hsum]
    calc
      _ ≤ ∑ _t ∈ fine.image source, (2*C+2) :=
        Finset.sum_le_sum (fun t _ => source_label_fiber_cap fine source u hd hC hsep hrealize t)
      _ = _ := by simp [selectedTubes]; ring
  obtain ⟨phi,hphi⟩ := hne
  have hl := (hAD phi hphi 1 hd1 le_rfl).1.trans
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
  apply (div_le_iff₀ (by positivity : 0 < K*(2*C+2))).mpr
  have hl' := (div_le_iff₀ hK).mp hl
  have hh := mul_le_mul_of_nonneg_left hmass hK.le
  nlinarith only [hl',hh]

/-- An original u-ball of selected tubes injects into the image of the actual
fine labels in the enlarged ball; no tube-to-label injectivity is assumed. -/
theorem selected_ball_cap (fine : Finset ℝ) (source : ℝ → T) (u : T → ℝ)
    {delta q K kappa C : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 0 ≤ K) (hk : 0 ≤ kappa) (hC : 0 ≤ C)
    (hAD : ADBounds fine delta K kappa) (hbox : ∀ phi ∈ fine, |phi| ≤ 1)
    (hrealize : ∀ phi ∈ fine, |u (source phi)-phi| ≤ C*delta) (a : ℝ) :
    (((selectedTubes fine source).filter (fun t => |u t-a| ≤ q)).card : ℝ) ≤
      4*K*(2*(1+C)*q/delta)^kappa := by
  have hq : 0 < q := hd.trans_le hdq
  have hsub : (selectedTubes fine source).filter (fun t => |u t-a| ≤ q) ⊆
      (carrierBall fine a ((1+C)*q)).image source := by
    intro t ht
    obtain ⟨htS,hta⟩ := Finset.mem_filter.mp ht
    obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp htS
    apply Finset.mem_image.mpr
    refine ⟨phi,(mem_carrierBall _ _ _ _).mpr ⟨hphi,?_⟩,rfl⟩
    have htri := abs_add_le (phi-u (source phi)) (u (source phi)-a)
    have herr := hrealize phi hphi
    rw [abs_sub_comm phi (u (source phi))] at htri
    rw [Real.dist_eq]
    have hid : (phi-u (source phi))+(u (source phi)-a)=phi-a := by ring
    rw [hid] at htri
    nlinarith [mul_le_mul_of_nonneg_left hdq hC]
  have hcard := Finset.card_le_card hsub |>.trans (Finset.card_image_le)
  have hb := (Nat.cast_le.mpr hcard).trans
    (boxed_AD_allcenter fine hd (hdq.trans hq1) hK hk hAD hbox a ((1+C)*q) (by nlinarith))
  simpa only [mul_assoc] using hb

def degree (delta K kappa C : ℝ) : ℝ := (1/delta)^kappa/(K*(2*C+2))
def ballCap (delta q K kappa C : ℝ) : ℝ := 4*K*(2*(1+C)*q/delta)^kappa
def populationLoss (Kfine Kcoarse C : ℝ) : ℝ := 128*Kfine^2*Kcoarse*(1+C)^3

/-- When a coarse source label covers a fine label within q, the selected
tube is within q+C delta. The resulting cap charges both realization errors
and is still obtained from the original source AD data. -/
theorem selected_reference_ball_cap (fine : Finset ℝ) (source : ℝ → T) (u : T → ℝ)
    {delta q K kappa C : ℝ} (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 0 ≤ K) (hk : 0 ≤ kappa) (hC : 0 ≤ C)
    (hAD : ADBounds fine delta K kappa) (hbox : ∀ phi ∈ fine, |phi| ≤ 1)
    (hrealize : ∀ phi ∈ fine, |u (source phi)-phi| ≤ C*delta) (a : ℝ) :
    (((selectedTubes fine source).filter (fun t => |u t-a| ≤ q+C*delta)).card : ℝ) ≤
      ballCap delta q K kappa (2*C) := by
  have hq : 0 < q := hd.trans_le hdq
  have hb := selected_ball_cap_general fine source u hd (hdq.trans hq1)
    (by nlinarith : delta ≤ q+C*delta) hK hk hC hAD hbox hrealize a
  have hbase : 2*(q+C*delta+C*delta)/delta ≤ 2*(1+2*C)*q/delta := by
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith [mul_le_mul_of_nonneg_left hdq hC]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity : 0 ≤ 2*(q+C*delta+C*delta)/delta) hbase hk) (by positivity))

lemma degree_pos {delta K kappa C : ℝ} (hd : 0 < delta) (hK : 0 < K)
    (hC : 0 ≤ C) : 0 < degree delta K kappa C := by unfold degree; positivity

lemma ballCap_pos {delta q K kappa C : ℝ} (hd : 0 < delta) (hq : 0 < q)
    (hK : 0 < K) (hC : 0 ≤ C) : 0 < ballCap delta q K kappa C := by
  unfold ballCap
  positivity

theorem ballCap_double_error_le {delta q K kappa C : ℝ} (hd : 0 < delta)
    (hq : 0 < q) (hK : 0 ≤ K) (hC : 0 ≤ C) (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2) :
    ballCap delta q K kappa (2*C) ≤ 4*ballCap delta q K kappa C := by
  have hbase : 0 ≤ 2*(1+C)*q/delta := by positivity
  have hscale : 2*(1+2*C)*q/delta ≤ 2*(2*(1+C)*q/delta) := by
    have hh : 2*(1+2*C)*q ≤ 2*(2*(1+C)*q) := by nlinarith
    have hh' := div_le_div_of_nonneg_right hh hd.le
    simpa only [mul_div_assoc] using hh'
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 2*(1+2*C)*q/delta) hscale hk
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hbase] at hp
  have htwo : (2:ℝ)^kappa ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hk2
    norm_num at hh ⊢
    exact hh
  have hp' := hp.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hbase _))
  have hh := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 4*K)
  unfold ballCap
  nlinarith only [hh]

/-- Exact cancellation of both original angular scales. The only remaining
real power is the realization constant, bounded uniformly for κ ≤ 2. -/
theorem population_ratio_from_card {delta q Kfine Kcoarse kappa C N : ℝ}
    (hd : 0 < delta) (hq : 0 < q) (hf : 0 < Kfine) (hc : 0 ≤ Kcoarse)
    (hC : 0 ≤ C) (hk2 : kappa ≤ 2)
    (hN : N ≤ 4*Kcoarse*(1/q)^kappa) :
    ballCap delta q Kfine kappa C*N/degree delta Kfine kappa C ≤
      populationLoss Kfine Kcoarse C := by
  have hdp := degree_pos (kappa := kappa) hd hf hC
  have hup := ballCap_pos (kappa := kappa) hd hq hf hC
  have hcancel : (2*(1+C)*q/delta)^kappa*(1/q)^kappa =
      (2*(1+C))^kappa*(1/delta)^kappa := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have heq : ballCap delta q Kfine kappa C*(4*Kcoarse*(1/q)^kappa)/
      degree delta Kfine kappa C = 16*Kfine^2*Kcoarse*(2*C+2)*(2*(1+C))^kappa := by
    unfold ballCap degree
    have hp : (1/delta)^kappa ≠ 0 := (Real.rpow_pos_of_pos (by positivity) kappa).ne'
    calc
      _ = 16*Kfine*Kcoarse*((2*(1+C)*q/delta)^kappa*(1/q)^kappa)*
          (Kfine*(2*C+2))/(1/delta)^kappa := by field_simp; ring
      _ = _ := by rw [hcancel]; field_simp
  have hpow : (2*(1+C))^kappa ≤ (2*(1+C))^2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 2*(1+C)) hk2 using 1
    norm_num
  calc
    _ ≤ ballCap delta q Kfine kappa C*(4*Kcoarse*(1/q)^kappa)/
        degree delta Kfine kappa C :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN hup.le) hdp.le
    _ = 16*Kfine^2*Kcoarse*(2*C+2)*(2*(1+C))^kappa := heq
    _ ≤ 16*Kfine^2*Kcoarse*(2*C+2)*(2*(1+C))^2 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by unfold populationLoss; ring

/-- The common alphabet is the literal original boxed coarse AD alphabet.
Its cardinality and both scale cancellations are proved here. -/
theorem original_population_ratio (Phi : Finset ℝ) {delta q Kfine Kcoarse kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hf : 0 < Kfine) (hc : 0 ≤ Kcoarse) (hC : 0 ≤ C) (hk2 : kappa ≤ 2)
    (hAD : ADBounds Phi q Kcoarse kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    ballCap delta q Kfine kappa C*(Phi.card : ℝ)/degree delta Kfine kappa C ≤
      populationLoss Kfine Kcoarse C :=
  population_ratio_from_card hd (hd.trans_le hdq) hf hc hC hk2
    (boxed_AD_card Phi (hd.trans_le hdq) hq1 hc hAD hbox)

/-- Coarse reference selection has original error q+C delta. Its actual
u-ball cap, charged at that enlarged radius, has a uniform cubic loss against
the SAME original q-AD common alphabet. -/
theorem original_reference_population_ratio (Phi : Finset ℝ)
    {delta q Kfine Kcoarse kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hf : 0 < Kfine) (hc : 0 ≤ Kcoarse) (hC : 0 ≤ C)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hAD : ADBounds Phi q Kcoarse kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    ballCap delta q Kfine kappa (2*C)*(Phi.card : ℝ)/degree delta Kfine kappa C ≤
      512*Kfine^2*Kcoarse*(1+C)^3 := by
  have hcap := ballCap_double_error_le hd (hd.trans_le hdq) hf.le hC hk hk2
  have hratio := original_population_ratio Phi hd hdq hq1 hf hc hC hk2 hAD hbox
  have hmul := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg Phi.card : (0:ℝ) ≤ Phi.card))
    (degree_pos (kappa := kappa) hd hf hC).le
  calc
    _ ≤ 4*(ballCap delta q Kfine kappa C*(Phi.card : ℝ)/degree delta Kfine kappa C) := by
      simpa only [mul_assoc,mul_div_assoc] using hmul
    _ ≤ 4*populationLoss Kfine Kcoarse C := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by unfold populationLoss; ring

end OriginalAngularSourcePopulation
