import Theorems.Thm_StickyKakeya4_original_scalar_literal_cover_count
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace OriginalLiteralCommonAlphabet
open Classical Finset NativeScalarCoverAD FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalScalarLiteralCoverCount
open scoped BigOperators
private lemma neighbor_card (k : ℤ) : (Icc (k-1) (k+1)).card=3 := by
  have hh : ((Icc (k-1) (k+1)).card:ℤ)=3 := by
    rw [Int.card_Icc_of_le _ _ (by omega)]
    omega
  exact_mod_cast hh
private lemma cell_neighbor {q x y : ℝ} (hq : 0 < q) (hxy : dist x y ≤ q) :
    cell q x ∈ Icc (cell q y-1) (cell q y+1) := by
  have hh := abs_le.mp (show |x-y| ≤ q by simpa only [Real.dist_eq] using hxy)
  have hlo : y/q-1 ≤ x/q := by apply (le_div_iff₀ hq).mpr; field_simp; nlinarith only [hh.1]
  have hhi : x/q ≤ y/q+1 := by apply (div_le_iff₀ hq).mpr; field_simp; nlinarith only [hh.2]
  exact mem_Icc.mpr ⟨by simpa only [cell,Int.floor_sub_one] using Int.floor_mono hlo,
    by simpa only [cell,Int.floor_add_one] using Int.floor_mono hhi⟩
/-- Actual separated original angles are counted through the literal
 covering alphabet's occupied cells. The covering alphabet may be unseparated. -/
theorem original_net_upper (C Phi : Finset ℝ) {q K kappa : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hK : 0 ≤ K) (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hsep : Separated C q) (H : CoverADBounds Phi q K kappa)
    (hbox : ∀ x ∈ Phi, |x| ≤ 1)
    (hnear : ∀ c ∈ C, ∃ phi ∈ Phi, dist c phi ≤ q)
    (a r : ℝ) (hr : q ≤ r) :
    ((carrierBall C a r).card:ℝ) ≤ 192*K*(r/q)^kappa := by
  have hr0 : 0 < r := hq.trans_le hr
  have hsub : (carrierBall C a r).image (cell q) ⊆
      ((carrierBall Phi a (r+q)).image (cell q)).biUnion (fun k => Icc (k-1) (k+1)) := by
    intro k hk'
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hk'
    obtain ⟨hcC,hca⟩ := (mem_carrierBall C c a r).mp hc
    obtain ⟨phi,hphi,hcp⟩ := hnear c hcC
    have hpa : dist phi a ≤ r+q := by
      have hh := dist_triangle phi c a
      rw [dist_comm phi c] at hh
      linarith only [hh,hcp,hca]
    exact mem_biUnion.mpr ⟨cell q phi,mem_image_of_mem _ ((mem_carrierBall Phi phi a (r+q)).mpr ⟨hphi,hpa⟩),
      cell_neighbor hq hcp⟩
  have hc : ((carrierBall C a r).card:ℝ) ≤ 3*coverCount Phi q a (r+q) := by
    have hs : Separated (carrierBall C a r) q := fun x hx y hy hxy =>
      hsep x ((mem_carrierBall C x a r).mp hx).1 y ((mem_carrierBall C y a r).mp hy).1 hxy
    have hh := (card_le_card hsub).trans
      (card_biUnion_le_card_mul _ _ 3 (fun k _hk => (neighbor_card k).le))
    rw [separated_card_eq_grid _ hq hs] at hh
    have hh' : ((carrierBall C a r).card:ℝ) ≤ coverCount Phi q a (r+q)*3 := by
      rw [cover_count_readback]
      exact_mod_cast hh
    simpa only [mul_comm] using hh'
  have hcap := boxed_cover_allcenter Phi hq hq1 hK hk H hbox a (r+q) (by linarith)
  have hratio : 2*(r+q)/q ≤ 4*(r/q) := by
    apply (div_le_iff₀ hq).mpr
    have hcancel : (4*(r/q))*q=4*r := by field_simp
    rw [hcancel]
    linarith only [hr]
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2*(r+q)/q) hratio hk
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) (by positivity : 0 ≤ r/q)] at hp
  have hfour : (4:ℝ)^kappa ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hk2
    norm_num at hh
    exact hh
  have hp' := hp.trans (mul_le_mul_of_nonneg_right hfour (by positivity))
  have h1 := mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤3)
  have h2 := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 12*K by positivity)
  nlinarith only [hc,h1,h2]
/-- A fine source alphabet containing an actual net center supplies its
 lower profile. Whole original occupied fine cells are charged to nearby
 net centers, so the source need not be separated or point-count AD. -/
theorem original_net_lower (fine C : Finset ℝ) {delta q K kappa : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1) (hK : 1 ≤ K)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (H : CoverADBounds fine delta K kappa) (hbox : ∀ x ∈ fine, |x| ≤ 1)
    (hcover : ∀ p ∈ fine, ∃ d ∈ C, dist p d < q)
    (c : ℝ) (hcf : c ∈ fine) (hcC : c ∈ C) (r : ℝ) (hqr : q ≤ r) (hr1 : r ≤ 1) :
    (r/q)^kappa/(64*K^2) ≤ ((carrierBall C c r).card:ℝ) := by
  have hq : 0 < q := hd.trans_le hdq
  have hr0 : 0 < r := hq.trans_le hqr
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have htwo : (2:ℝ)^kappa ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hk2
    norm_num at hh
    exact hh
  by_cases hlarge : 2*q ≤ r
  · have hs : (carrierBall fine c (r/2)).image (cell delta) ⊆
        (carrierBall C c r).biUnion (fun d => (carrierBall fine d q).image (cell delta)) := by
      intro k hk'
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hk'
      obtain ⟨hpf,hpc⟩ := (mem_carrierBall fine p c (r/2)).mp hp
      obtain ⟨d,hdC,hpd⟩ := hcover p hpf
      have hdc : dist d c ≤ r := by
        have hh := dist_triangle d p c
        rw [dist_comm d p] at hh
        linarith only [hh,hpd,hpc,hlarge]
      exact mem_biUnion.mpr ⟨d,(mem_carrierBall C d c r).mpr ⟨hdC,hdc⟩,
        mem_image_of_mem _ ((mem_carrierBall fine p d q).mpr ⟨hpf,hpd.le⟩)⟩
    have hcount : coverCount fine delta c (r/2) ≤
        (4*K*(2*q/delta)^kappa)*((carrierBall C c r).card:ℝ) := by
      have hh : coverCount fine delta c (r/2) ≤
          ∑ d ∈ carrierBall C c r, coverCount fine delta d q := by
        simp only [cover_count_readback]
        exact_mod_cast (card_le_card hs).trans card_biUnion_le
      calc
        _ ≤ ∑ d ∈ carrierBall C c r, coverCount fine delta d q := hh
        _ ≤ ∑ _d ∈ carrierBall C c r, 4*K*(2*q/delta)^kappa :=
          sum_le_sum (fun d _hd => boxed_cover_allcenter fine hd (hdq.trans hq1) hK0.le hk H hbox d q hdq)
        _ = _ := by simp [mul_comm]
    have hl := (H c hcf (r/2) (by linarith) (by linarith)).1.trans hcount
    have hl' := (div_le_iff₀ hK0).mp hl
    have hpowpos : 0 < (q/(2*delta))^kappa := Real.rpow_pos_of_pos (by positivity) _
    have heq1 : ((r/2)/delta)^kappa=(r/q)^kappa*(q/(2*delta))^kappa := by
      rw [←Real.mul_rpow (by positivity : 0 ≤ r/q) (by positivity : 0 ≤ q/(2*delta))]
      congr 1
      field_simp
    have heq2 : (2*q/delta)^kappa=(4:ℝ)^kappa*(q/(2*delta))^kappa := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤4) (by positivity : 0 ≤ q/(2*delta))]
      congr 1
      ring
    have hfour : (4:ℝ)^kappa ≤ 16 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hk2
      norm_num at hh
      exact hh
    have hcap := mul_le_mul_of_nonneg_right hfour hpowpos.le
    rw [←heq2] at hcap
    have hm := mul_le_mul_of_nonneg_right hcap
      (show 0 ≤ 4*K*((carrierBall C c r).card:ℝ)*K by positivity)
    rw [heq1] at hl'
    have hprod : (r/q)^kappa*(q/(2*delta))^kappa ≤
        (64*K^2*((carrierBall C c r).card:ℝ))*(q/(2*delta))^kappa := by
      nlinarith only [hl',hm]
    have hh := (mul_le_mul_iff_left₀ hpowpos).mp hprod
    apply (div_le_iff₀ (show 0 < 64*K^2 by positivity)).mpr
    nlinarith only [hh]
  · have hratio : r/q ≤ 2 := (div_le_iff₀ hq).mpr (by linarith only [lt_of_not_ge hlarge])
    have hp := (Real.rpow_le_rpow (by positivity : (0:ℝ)≤r/q) hratio hk).trans htwo
    have hcard : (1:ℝ) ≤ (carrierBall C c r).card := Nat.one_le_cast.mpr
      (card_pos.mpr ⟨c,(mem_carrierBall C c c r).mpr ⟨hcC,by simpa only [dist_self] using hq.le.trans hqr⟩⟩)
    exact ((div_le_iff₀ (show 0 < 64*K^2 by positivity)).mpr (by nlinarith only [hp,hK])).trans hcard
/-- The common alphabet is a maximal q-net of ACTUAL original fine angles.
 Its upper law comes from the literal macro alphabet; each lower law comes
 from a fine alphabet containing that actual center. The cover error is q. -/
theorem exists_actual_common_alphabet {P : Type*} (E : Finset P) (hE : E.Nonempty)
    (fine : P → Finset ℝ) (Phi : Finset ℝ) {delta q K kappa : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1) (hK : 1 ≤ K)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hfne : ∀ p ∈ E, (fine p).Nonempty)
    (hfAD : ∀ p ∈ E, CoverADBounds (fine p) delta K kappa)
    (hfbox : ∀ p ∈ E, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hPAD : CoverADBounds Phi q K kappa) (hPbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hnear : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ psi ∈ Phi, dist phi psi ≤ q) :
    ∃ C : Finset ℝ, C.Nonempty ∧ C ⊆ E.biUnion fine ∧ Separated C q ∧
      (∀ p ∈ E, ∀ phi ∈ fine p, ∃ c ∈ C, dist phi c < q) ∧
      (∀ c ∈ C, |c| ≤ 1) ∧ ADBounds C q (192*K^2) kappa := by
  have hq : 0 < q := hd.trans_le hdq
  let U := E.biUnion fine
  obtain ⟨C,hCU,hsep,hcover⟩ := exists_separated_net U (hd.trans_le hdq)
  have hC : C.Nonempty := by
    obtain ⟨p,hp⟩ := hE
    obtain ⟨phi,hphi⟩ := hfne p hp
    obtain ⟨c,hc,_⟩ := hcover phi (mem_biUnion.mpr ⟨p,hp,hphi⟩)
    exact ⟨c,hc⟩
  have hcnear : ∀ c ∈ C, ∃ psi ∈ Phi, dist c psi ≤ q := by
    intro c hc
    obtain ⟨p,hp,hcf⟩ := mem_biUnion.mp (hCU hc)
    exact hnear p hp c hcf
  refine ⟨C,hC,hCU,hsep,?_,?_,?_⟩
  · intro p hp phi hphi
    exact hcover phi (mem_biUnion.mpr ⟨p,hp,hphi⟩)
  · intro c hc
    obtain ⟨p,hp,hcf⟩ := mem_biUnion.mp (hCU hc)
    exact hfbox p hp c hcf
  · intro c hc r hqr hr1
    have hr0 : 0 < r := hq.trans_le hqr
    obtain ⟨p,hp,hcf⟩ := mem_biUnion.mp (hCU hc)
    have hlow := original_net_lower (fine p) C hd hdq hq1 hK hk hk2 (hfAD p hp) (hfbox p hp)
      (fun phi hphi => hcover phi (mem_biUnion.mpr ⟨p,hp,hphi⟩)) c hcf hc r hqr hr1
    have hhigh := original_net_upper C Phi (hd.trans_le hdq) hq1 (by linarith) hk hk2
      hsep hPAD hPbox hcnear c r hqr
    have hpow : 0 ≤ (r/q)^kappa := by positivity
    constructor
    · exact (div_le_div_of_nonneg_left hpow (by positivity : 0 < 64*K^2) (by nlinarith only [sq_nonneg K])).trans hlow
    · exact hhigh.trans (mul_le_mul_of_nonneg_right (show 192*K ≤ 192*K^2 by nlinarith only [hK]) hpow)
/-- Applying the same construction at the fine mesh supplies the genuine
 separated original fine labels used by the tube-degree counting lemmas.
 Their actual tube realization error is unchanged because C is a subset. -/
theorem exists_actual_fine_alphabet (Phi : Finset ℝ) (hPhi : Phi.Nonempty) {delta K kappa : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 1 ≤ K) (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (H : CoverADBounds Phi delta K kappa) (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) :
    ∃ C : Finset ℝ, C.Nonempty ∧ C ⊆ Phi ∧ Separated C delta ∧
      (∀ phi ∈ Phi, ∃ c ∈ C, dist phi c < delta) ∧
      (∀ c ∈ C, |c| ≤ 1) ∧ ADBounds C delta (192*K^2) kappa := by
  obtain ⟨C,hC,hCP,hsep,hcover,hboxC,hAD⟩ := exists_actual_common_alphabet
    ({()} : Finset Unit) (singleton_nonempty ()) (fun _ => Phi) Phi hd le_rfl hd1 hK hk hk2
    (fun _ _ => hPhi) (fun _ _ => H) (fun _ _ => hbox) H hbox
    (fun _ _ phi hphi => ⟨phi,hphi,by simpa only [dist_self] using hd.le⟩)
  refine ⟨C,hC,?_,hsep,?_,hboxC,hAD⟩
  · simpa only [singleton_biUnion] using hCP
  · intro phi hphi
    exact hcover () (mem_singleton_self ()) phi hphi
end OriginalLiteralCommonAlphabet
