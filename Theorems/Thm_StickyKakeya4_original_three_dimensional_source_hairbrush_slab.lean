import Theorems.Thm_StickyKakeya4_original_three_dimensional_direct_transverse_hairbrush
import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_cube_shading
import Theorems.Thm_StickyKakeya4_original_three_dimensional_near_stem_shade
import Theorems.Thm_StickyKakeya4_original_three_dimensional_shaded_brush_slab
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

noncomputable section
namespace OriginalThreeDimensionalHairbrushParameters

def gamma (K lam : ℝ) : ℝ := lam/(19200*K)
def theta (K lam : ℝ) : ℝ := gamma K lam/2
def beta (K nu : ℝ) : ℝ := nu/(8*K)
def shadeMass (K nu : ℝ) : ℝ := beta K nu/2
def stemRadius (K lam nu : ℝ) : ℝ := beta K nu*theta K lam/96000
def globalBudget (nu : ℝ) : ℝ := 768/nu
def brushPopulation (K lam nu L : ℝ) : ℝ :=
  (lam/3)^2*(theta K lam)^2*nu^2/(10000000000000000000000*L*K^4)
def slabWidth (K lam nu rho : ℝ) : ℝ := 1000000000000*K^2*rho/(lam*nu)
def clearingConstant : ℝ := 81*16^4*10^44*38400^4
def concentrationConstant : ℝ :=
  clearingConstant*(400000000000000000000000000*(4000*768*29491200000)^2)

theorem parameter_bounds (K lam nu L : ℝ) (hK : 1 ≤ K)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) :
    0 < gamma K lam ∧ gamma K lam ≤ 1/19200 ∧
    0 < theta K lam ∧ theta K lam ≤ 1 ∧
    0 < beta K nu ∧ beta K nu ≤ 1/8 ∧
    0 < shadeMass K nu ∧ 0 < stemRadius K lam nu ∧ stemRadius K lam nu ≤ 1 ∧
    stemRadius K lam nu ≤ gamma K lam/4 ∧
    stemRadius K lam nu ≤ shadeMass K nu/4800 ∧
    0 < globalBudget nu ∧ 0 < brushPopulation K lam nu L := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hg : 0 < gamma K lam := by unfold gamma; positivity
  have hg1 : gamma K lam ≤ 1/19200 := by
    unfold gamma
    apply (div_le_iff₀ (by positivity : 0 < 19200*K)).mpr
    nlinarith only [hK,hlam1]
  have ht : 0 < theta K lam := by unfold theta; positivity
  have ht1 : theta K lam ≤ 1 := by unfold theta; linarith only [hg1]
  have hb : 0 < beta K nu := by unfold beta; positivity
  have hb1 : beta K nu ≤ 1/8 := by
    unfold beta
    apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith only [hK,hnu1]
  have hs : 0 < stemRadius K lam nu := by unfold stemRadius; positivity
  have hs1 : stemRadius K lam nu ≤ 1 := by
    have hm := mul_le_mul hb1 ht1 ht.le (by norm_num : (0:ℝ) ≤ 1/8)
    unfold stemRadius
    linarith only [hm]
  have hsg : stemRadius K lam nu ≤ gamma K lam/4 := by
    have hm := mul_le_mul_of_nonneg_right hb1 hg.le
    unfold stemRadius theta
    nlinarith only [hm,hg]
  have hsb : stemRadius K lam nu ≤ shadeMass K nu/4800 := by
    have hm := mul_le_mul_of_nonneg_left ht1 hb.le
    unfold stemRadius shadeMass
    nlinarith only [hm,hb]
  refine ⟨hg,hg1,ht,ht1,hb,hb1,?_,hs,hs1,hsg,hsb,?_,?_⟩
  · unfold shadeMass; positivity
  · unfold globalBudget; positivity
  · unfold brushPopulation; positivity

theorem exact_parameter_budgets (K lam nu : ℝ) (hK : 0 < K) :
    1600*K*gamma K lam=lam/12 ∧
      96000*stemRadius K lam nu=beta K nu*theta K lam ∧
      stemRadius K lam nu=lam*nu/(29491200000*K^2) := by
  constructor
  · unfold gamma; field_simp; ring
  constructor
  · unfold stemRadius; ring
  · unfold stemRadius beta theta gamma
    field_simp
    ring

theorem small_radius_conditions (delta rho K lam nu : ℝ)
    (_hd : 0 < delta) (hquery : delta ≤ rho) (hK : 1 ≤ K)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hsmall : rho ≤ stemRadius K lam nu) :
    8*rho ≤ 1 ∧ 4*gamma K lam ≤ 1 ∧ delta ≤ 4*gamma K lam ∧
      rho ≤ gamma K lam/4 ∧ rho ≤ shadeMass K nu/4800 := by
  obtain ⟨hg,hg1,_ht,_ht1,_hb,_hb1,_hshade,_hs,_hs1,hsg,hsb,_hA,_hpop⟩ :=
    parameter_bounds K lam nu 1 hK hlam hlam1 hnu hnu1 le_rfl
  have hrg := hsmall.trans hsg
  refine ⟨?_,by linarith only [hg1],?_,hrg,hsmall.trans hsb⟩
  · linarith only [hrg,hg1]
  · linarith only [hquery,hrg,hg,_hd]

theorem slab_width_ge_hundred (K lam nu rho : ℝ) (hK : 1 ≤ K)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hrho : 0 ≤ rho) :
    100*rho ≤ slabWidth K lam nu rho := by
  have hp := mul_le_mul hlam1 hnu1 hnu.le (by norm_num : (0:ℝ) ≤ 1)
  have hs : 1 ≤ K^2 := by nlinarith only [hK]
  unfold slabWidth
  apply (le_div_iff₀ (mul_pos hlam hnu)).mpr
  have h₁ := mul_le_mul_of_nonneg_right hp hrho
  have h₂ := mul_le_mul_of_nonneg_right hs hrho
  nlinarith only [h₁,h₂,hrho]

theorem large_radius_slab_width (K lam nu rho : ℝ) (hK : 1 ≤ K)
    (hlam : 0 < lam) (hnu : 0 < nu) (hlarge : stemRadius K lam nu < rho) :
    1 ≤ slabWidth K lam nu rho := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := (exact_parameter_budgets K lam nu hKp).2.2
  rw [hs] at hlarge
  have hh := (div_lt_iff₀ (by positivity : 0 < 29491200000*K^2)).mp hlarge
  have hrho : 0 < rho := (by positivity : 0 < lam*nu/(29491200000*K^2)).trans hlarge
  unfold slabWidth
  apply (le_div_iff₀ (mul_pos hlam hnu)).mpr
  nlinarith only [hh,mul_pos (sq_pos_of_pos hKp) hrho]

/-- Exact polynomial clearing of every chosen source constant. The final
rounding is checked numerically, after all source normalizations cancel. -/
theorem source_mass_constant_conversion (K lam nu L n m : ℝ)
    (hK : 0 < K) (hlam : 0 < lam) (hnu : 0 < nu) (hL : 0 < L) (hm : 0 ≤ m)
    (hcount : (brushPopulation K lam nu L)^2*(shadeMass K nu)^4*nu^2*n ≤ 400000000000000000000000000*L*K*(4000/stemRadius K lam nu*globalBudget nu)^2*m) :
    lam^10*nu^14*n ≤ (10:ℝ)^140*K^21*L^3*m := by
  let M : ℝ := clearingConstant*L^2*K^16*lam^2*nu^4
  have hM : 0 ≤ M := by unfold M clearingConstant; positivity
  have hleft : (brushPopulation K lam nu L)^2*(shadeMass K nu)^4*nu^2*n*M=
      lam^10*nu^14*n := by
    unfold M clearingConstant brushPopulation shadeMass beta theta gamma
    field_simp
    ring
  have hright : 400000000000000000000000000*L*K*
      (4000/stemRadius K lam nu*globalBudget nu)^2*m*M=
      concentrationConstant*K^21*L^3*m := by
    unfold M concentrationConstant clearingConstant stemRadius globalBudget beta theta gamma
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_right hcount hM
  rw [hleft,hright] at hh
  have hc : concentrationConstant ≤ (10:ℝ)^140 := by norm_num [concentrationConstant,clearingConstant]
  have hm' := mul_le_mul_of_nonneg_right hc (show 0 ≤ K^21*L^3*m by positivity)
  exact hh.trans (by nlinarith only [hm'])

theorem trivial_mass_constant (K lam nu L : ℝ) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) :
    lam^10*nu^14 ≤ (10:ℝ)^140*K^21*L^3 := by
  have hlamPow : lam^10 ≤ 1 := pow_le_one₀ hlam hlam1
  have hnuPow : nu^14 ≤ 1 := pow_le_one₀ hnu hnu1
  have hsmall : lam^10*nu^14 ≤ 1 := (mul_le_mul hlamPow hnuPow (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hK' : 1 ≤ K^21 := one_le_pow₀ hK
  have hL' : 1 ≤ L^3 := one_le_pow₀ hL
  have hKL : (1:ℝ) ≤ K^21*L^3 := by
    simpa only [one_mul] using mul_le_mul hK' hL' zero_le_one (zero_le_one.trans hK')
  have hc : (1:ℝ) ≤ 10^140 := by norm_num
  have hh := mul_le_mul hc hKL zero_le_one (zero_le_one.trans hc)
  exact hsmall.trans (by simpa only [one_mul,mul_assoc] using hh)

end OriginalThreeDimensionalHairbrushParameters
end


set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalSourceHairbrushSlab
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalHeavyCubes
open OriginalThreeDimensionalNearStemShade OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalSourceHairbrush OriginalThreeDimensionalTransverseHairbrush
open OriginalThreeDimensionalShadedBrushSlab OriginalThreeDimensionalHairbrushParameters

/-- An all-original-source finite inverse hairbrush theorem. The graph,
actual representative tubes, global original heavy-cube shades, outside-stem
shades, pencil groups, and localized original mass are constructed internally.
There is no tube-family count, shading population, overlap, or slab-density
certificate among the hypotheses. -/
theorem exists_original_source_hairbrush_slab (P : Finset Point3) (G : Finset Pair3)
    (delta eta rho lam nu : ℝ) (N : ℕ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hquery : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hP : P.Nonempty) (hG : G⊆P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hdense : lam*(P.card : ℝ)^2 ≤ G.card)
    (hterminal : 1 ≤ 2*dyadicRadius rho N)
    (hbox : ∀ p∈P, ∀ j, |p j| ≤ 1)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ delta^(-eta)*r^2*P.card)
    (hrich : ∀ z∈G, nu*rho*P.card ≤ ((physicalPairTube3 P rho z).card : ℝ)) :
    ∃ n : Point3, ∃ c : ℝ, (∑ j,n j^2)=1 ∧
      lam^10*nu^14*P.card ≤ (10:ℝ)^140*(delta^(-eta))^21*((N:ℝ)+1)^3*
        ((P.filter (fun x => |(∑ j,n j*x j)-c| ≤ 1000000000000*(delta^(-eta))^2*rho/(lam*nu))).card : ℝ) := by
  let K : ℝ := delta^(-eta)
  let L : ℝ := (N:ℝ)+1
  let W : ℝ := slabWidth K lam nu rho
  have hK : 1 ≤ K := by
    simpa only [K,Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta ≤ 0 by linarith only [heta])
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hL : 1 ≤ L := by dsimp [L]; have hh:=Nat.cast_nonneg (α:=ℝ) N; linarith only [hh]
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hrho : 0 < rho := hd.trans_le hquery
  suffices ∃ n : Point3, ∃ c : ℝ, (∑ j,n j^2)=1 ∧
      lam^10*nu^14*P.card ≤ (10:ℝ)^140*K^21*L^3*
        ((P.filter (fun x => |(∑ j,n j*x j)-c| ≤ W)).card : ℝ) by
    simpa only [K,L,W,slabWidth] using this
  by_cases hsmall : rho ≤ stemRadius K lam nu
  · obtain ⟨hg,hg1,ht,ht1,hβ,_hβ1,hb,hs,hs1,_hsg,_hsb,hA,hh⟩ :=
      parameter_bounds K lam nu L hK hlam hlam1 hnu hnu1 hL
    obtain ⟨hrho8,hgamma1,hdgamma,hrhogamma,hrhob⟩ :=
      small_radius_conditions delta rho K lam nu hd hquery hK hlam hlam1 hnu hnu1 hsmall
    have hbudget : 1600*delta^(-eta)*gamma K lam ≤ lam/12 := by
      exact ((exact_parameter_budgets K lam nu hKp).1).le
    obtain ⟨i,R,stem,hstem,hRG,hcellR,hchart,hBcount,hbrush⟩ :=
      exists_original_dense_graph_hairbrush P G delta eta rho (gamma K lam) lam nu N
        hd hd1 heta hquery hrho8 hg hgamma1 hdgamma hrhogamma hlam hnu hbudget
        hP hG hdense hne hterminal hbox hfrostman hrich
    let B := brush P R rho (theta K lam) i stem
    have hBR : B⊆R := Finset.filter_subset _ _
    obtain ⟨H,hHP,hcellH,hHcount,hshade⟩ := exists_original_global_heavy_cube_shading
      P delta eta rho nu hd hd1 heta hquery hrho1 hnu.le hP hbox hfrostman
    have hchoose : ∀ z : Pair3, ∃ Y : Finset Point3, z∈B →
        Y⊆H ∧ Y⊆physicalPairTube3 P (4*rho) z ∧ beta K nu ≤ rho*Y.card := by
      intro z
      by_cases hz : z∈B
      · have hzR := hBR hz
        obtain ⟨Y,hYH,hYT,hYm⟩ := hshade z i (hchart z hzR).1 (hchart z hzR).2
          (hrich z (hRG hzR))
        refine ⟨Y,fun _ => ⟨hYH,hYT,?_⟩⟩
        unfold beta
        apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
        change nu ≤ 8*K*rho*Y.card at hYm
        calc
          nu ≤ 8*K*rho*Y.card := hYm
          _ = (rho*Y.card)*(8*K) := by ring
      · exact ⟨∅,fun hh => False.elim (hz hh)⟩
    choose Y₀ hY₀ using hchoose
    let X := H.filter (fun x => x∉physicalTube3 stem.1 stem.2 (stemRadius K lam nu))
    let Y : Pair3→Finset Point3 := fun z => (Y₀ z).filter (fun x => x∉physicalTube3 stem.1 stem.2 (stemRadius K lam nu))
    have hXP : X⊆P := (Finset.filter_subset _ _).trans hHP
    have hYX : ∀ z∈B,Y z⊆X := by
      intro z hz x hx
      obtain ⟨hxY,hout⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(hY₀ z hz).1 hxY,hout⟩
    have hYT : ∀ z∈B,Y z⊆physicalPairTube3 P (4*rho) z := by
      intro z hz
      exact (Finset.filter_subset _ _).trans (hY₀ z hz).2.1
    have hYmass : ∀ z∈B,shadeMass K nu ≤ rho*(Y z).card := by
      intro z hz
      obtain ⟨_hzR,⟨j,hgap⟩,_hroot⟩ := hbrush z hz
      have hgap' : theta K lam ≤ |slope z i j-slope stem i j| := by
        simpa only [theta,abs_sub_comm] using hgap
      exact original_shade_outside_stem_mass (Y₀ z) z stem i j rho (stemRadius K lam nu)
        (theta K lam) (beta K nu) hrho hsmall ht ht1 hβ.le
        ((exact_parameter_budgets K lam nu hKp).2.1.le)
        (hchart z (hBR hz)).1 (hchart stem hstem).1 (hchart z (hBR hz)).2 (hchart stem hstem).2
        hgap' (hcellH.mono (hY₀ z hz).1)
        (fun x hx => (Finset.mem_filter.mp ((hY₀ z hz).2.1 hx)).2) (hY₀ z hz).2.2
    have hglobal : rho^2*X.card ≤ globalBudget nu := by
      have hc : (X.card : ℝ) ≤ H.card := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ nu*rho^2 by positivity)
      unfold globalBudget
      apply (le_div_iff₀ hnu).mpr
      calc
        rho^2*(X.card : ℝ)*nu = nu*rho^2*X.card := by ring
        _ ≤ nu*rho^2*H.card := hm
        _ ≤ 768 := hHcount
    have hpop : brushPopulation K lam nu L ≤ rho^2*B.card := by
      unfold brushPopulation
      apply (div_le_iff₀ (by positivity : 0 < 10000000000000000000000*L*K^4)).mpr
      change (lam/3)^2*(theta K lam)^2*nu^2 ≤ 10000000000000000000000*L*K^4*rho^2*B.card at hBcount
      calc
        _ ≤ 10000000000000000000000*L*K^4*rho^2*B.card := hBcount
        _ = (rho^2*B.card)*(10000000000000000000000*L*K^4) := by ring
    let e : Equiv.Perm (Fin 3) := Equiv.swap 2 i
    have he : e 2=i := Equiv.swap_apply_left _ _
    have htrans : ∀ z∈B,∃ j,slope z (e 2) j≠slope stem (e 2) j := by
      intro z hz
      obtain ⟨j,hgap⟩ := (hbrush z hz).2.1
      have hp : 0 < |slope stem i j-slope z i j| := ht.trans_le hgap
      refine ⟨j,?_⟩
      rw [he]
      exact Ne.symm (sub_ne_zero.mp (abs_pos.mp hp))
    have hrich8 : ∀ z∈B,nu*rho*P.card ≤ ((physicalPairTube3 P (8*rho) z).card : ℝ) := by
      intro z hz
      apply (hrich z (hRG (hBR hz))).trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxP,l,hl⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxP,l,hl.trans (by linarith only [hrho])⟩
    obtain ⟨n,c,hunit,hsource⟩ := exists_original_shaded_brush_slab P X B Y delta rho K nu
      (shadeMass K nu) (brushPopulation K lam nu L) (globalBudget nu) (stemRadius K lam nu) N stem e
      hd hquery hrho1 hK hnu.le hP hb hrhob hh hA hs hs1 hterminal hbox hfrostman
      hXP (fun x hx => (Finset.mem_filter.mp hx).2) (hcellH.mono (Finset.filter_subset _ _))
      hYX hYT hYmass
      (by rw [he]; exact (hchart stem hstem).1)
      (by rw [he]; exact (hchart stem hstem).2)
      (hbox stem.1 (Finset.mem_product.mp (hG (hRG hstem))).1)
      (by intro z hz; rw [he]; exact (hchart z (hBR hz)).1)
      (by intro z hz; rw [he]; exact (hchart z (hBR hz)).2)
      (by rw [he]; exact hcellR.mono hBR) htrans (fun z hz => (hbrush z hz).2.2)
      hrich8 hpop hglobal
    simp only [L] at hsource
    have hmass := source_mass_constant_conversion K lam nu ((N:ℝ)+1) _ _
      hKp hlam hnu hLp (Nat.cast_nonneg _) hsource
    have hwidth : 100*rho ≤ W := slab_width_ge_hundred K lam nu rho hK hlam hlam1 hnu hnu1 hrho.le
    have hsub : P.filter (fun x => |(∑ j,n j*x j)-c| ≤ 100*rho)⊆
        P.filter (fun x => |(∑ j,n j*x j)-c| ≤ W) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.trans hwidth⟩
    have hc : ((P.filter (fun x => |(∑ j,n j*x j)-c| ≤ 100*rho)).card : ℝ) ≤ (P.filter (fun x => |(∑ j,n j*x j)-c| ≤ W)).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
    refine ⟨n,c,hunit,hmass.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  · have hwidth : 1 ≤ W := large_radius_slab_width K lam nu rho hK hlam hnu (lt_of_not_ge hsmall)
    let n : Point3 := fun j => if j=0 then 1 else 0
    have hunit : (∑ j,n j^2)=1 := by norm_num [n,Fin.sum_univ_three]
    have hvalue (x : Point3) : (∑ j,n j*x j)=x 0 := by simp [n]
    have hfull : P.filter (fun x => |(∑ j,n j*x j)-(0:ℝ)| ≤ W)=P := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      rw [hvalue,sub_zero]
      exact (hbox x hx 0).trans hwidth
    refine ⟨n,0,hunit,?_⟩
    rw [hfull]
    have hc := trivial_mass_constant K lam nu L hK hlam.le hlam1 hnu.le hnu1 hL
    exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg P.card)

end OriginalThreeDimensionalSourceHairbrushSlab
end
