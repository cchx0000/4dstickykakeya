import Theorems.Thm_StickyKakeya4_original_three_dimensional_common_chart
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_incidence_energy
/- Source section: OriginalThreeDimensionalTransverseWedgeGeometry -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalThreeDimensionalTransverseWedgeGeometry
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeFrostman OriginalThreeDimensionalPairTubeFamily
open OriginalTubeGraphPairGeometry

lemma original_endpoint_graph (z : Pair3) (i j : Fin 3)
    (hne : z.2 i-z.1 i≠0) :
    z.2 j=slope z i j*z.2 i+offset z i j := by
  have hh := original_line_graph z i j 1 hne
  simpa only [linePoint3,one_mul,add_sub_cancel] using hh

/-- A bad wedge of actual original endpoints lies in the first original
line's physical tube. Only genuine original slopes are compared. -/
theorem original_parallel_wedge_neighbor_mem (p q₁ q₂ : Point3)
    (i : Fin 3) (gamma : ℝ) (hgamma : 0≤gamma)
    (hp : ∀ j, |p j|≤1) (hq₂ : ∀ j, |q₂ j|≤1)
    (hne₁ : q₁ i-p i≠0) (hne₂ : q₂ i-p i≠0)
    (hclose : ∀ j, |slope (p,q₁) i j-slope (p,q₂) i j|≤gamma) :
    q₂∈physicalTube3 p q₁ (4*gamma) := by
  let l := (q₂ i-p i)/(q₁ i-p i)
  have herr (j : Fin 3) : |q₂ j-linePoint3 p q₁ l j|≤2*gamma := by
    rw [original_graph_point (p,q₁) i j (q₂ i) hne₁]
    have he : q₂ j=slope (p,q₂) i j*q₂ i+offset (p,q₂) i j :=
      original_endpoint_graph (p,q₂) i j hne₂
    have hid : q₂ j-(slope (p,q₁) i j*q₂ i+offset (p,q₁) i j)=
        (slope (p,q₂) i j-slope (p,q₁) i j)*(q₂ i-p i) := by
      rw [he]
      simp only [offset]
      ring
    rw [hid,abs_mul]
    have hs : |slope (p,q₂) i j-slope (p,q₁) i j|≤gamma := by
      simpa only [abs_sub_comm] using hclose j
    have hd : |q₂ i-p i|≤2 := (abs_sub _ _).trans (by linarith only [hq₂ i,hp i])
    exact (mul_le_mul hs hd (abs_nonneg _) hgamma).trans_eq (by ring)
  refine ⟨l,?_⟩
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤4*gamma)).mpr
  have hs (j : Fin 3) : (q₂ j-linePoint3 p q₁ l j)^2≤(2*gamma)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (herr j) 2
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg gamma]

/-- The original Frostman source pays each bad-wedge row directly. -/
theorem original_bad_wedge_neighbors_card (P : Finset Point3) (p q : Point3)
    (delta eta gamma : ℝ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤4*gamma) (hgamma1 : 4*gamma≤1)
    (hp : p∈P) (hne : q i-p i≠0)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun y => distance3 x y≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ((P.filter (fun y => y i-p i≠0 ∧
      ∀ j, |slope (p,q) i j-slope (p,y) i j|≤gamma)).card : ℝ)≤
      1600*delta^(-eta)*gamma*P.card := by
  have hg : 0≤gamma := by linarith only [hd,hquery]
  have hsub : P.filter (fun y => y i-p i≠0 ∧
      ∀ j, |slope (p,q) i j-slope (p,y) i j|≤gamma)⊆
      physicalPairTube3 P (4*gamma) (p,q) := by
    intro y hy
    obtain ⟨hyP,hyne,hyclose⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hyP,original_parallel_wedge_neighbor_mem p q y i gamma hg
      (hbox p hp) (hbox y hyP) hne hyne hyclose⟩
  have hc : ((P.filter (fun y => y i-p i≠0 ∧
      ∀ j, |slope (p,q) i j-slope (p,y) i j|≤gamma)).card : ℝ)≤
      (physicalPairTube3 P (4*gamma) (p,q)).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
  have ht := original_tube_two_frostman_count P (p,q) delta eta (4*gamma)
    hd hd1 heta hquery hgamma1 hbox hfrostman
  linarith only [hc,ht]

/-- Literal equality of original parameter cells transfers a good slope
coordinate to the actual selected endpoint-pair representatives. -/
theorem original_transverse_parameter_transfer (z₁ z₂ v₁ v₂ : Pair3)
    (rho gamma : ℝ) (i j : Fin 3) (hrho : 0<rho) (hsmall : rho≤gamma/4)
    (hc₁ : parameterCell rho i z₁=parameterCell rho i v₁)
    (hc₂ : parameterCell rho i z₂=parameterCell rho i v₂)
    (hgap : gamma< |slope z₁ i j-slope z₂ i j|) :
    gamma/2≤|slope v₁ i j-slope v₂ i j| := by
  have h₁ := (original_parameter_cell_error rho i z₁ v₁ hrho hc₁).1 j
  have h₂ := (original_parameter_cell_error rho i z₂ v₂ hrho hc₂).1 j
  have ht₁ := abs_sub_le (slope z₁ i j) (slope v₁ i j) (slope z₂ i j)
  have ht₂ := abs_sub_le (slope v₁ i j) (slope v₂ i j) (slope z₂ i j)
  have h₂' : |slope v₂ i j-slope z₂ i j|≤rho := by simpa only [abs_sub_comm] using h₂
  linarith only [h₁,h₂',ht₁,ht₂,hgap,hsmall]

/-- Two actual tubes with a common transverse slope coordinate have small
physical intersection diameter. No line-distance surrogate is assumed. -/
theorem original_transverse_intersection_diameter (v w : Pair3) (x y : Point3)
    (rho theta : ℝ) (i j : Fin 3) (hrho : 0≤rho) (htheta : 0<theta) (htheta1 : theta≤1)
    (hv : v.2 i-v.1 i≠0) (hw : w.2 i-w.1 i≠0)
    (hvmax : ∀ k, |v.2 k-v.1 k|≤|v.2 i-v.1 i|)
    (hwmax : ∀ k, |w.2 k-w.1 k|≤|w.2 i-w.1 i|)
    (hgap : theta≤|slope v i j-slope w i j|)
    (hxv : x∈physicalTube3 v.1 v.2 (8*rho))
    (hxw : x∈physicalTube3 w.1 w.2 (8*rho))
    (hyv : y∈physicalTube3 v.1 v.2 (8*rho))
    (hyw : y∈physicalTube3 w.1 w.2 (8*rho)) :
    distance3 x y≤192*rho/theta := by
  have hvx : ∀ k, |x k-(slope v i k*x i+offset v i k)|≤16*rho := by
    intro k; have h := original_tube_graph_residual v i x (8*rho) hv hvmax hxv k; linarith only [h]
  have hvy : ∀ k, |y k-(slope v i k*y i+offset v i k)|≤16*rho := by
    intro k; have h := original_tube_graph_residual v i y (8*rho) hv hvmax hyv k; linarith only [h]
  have hwx : ∀ k, |x k-(slope w i k*x i+offset w i k)|≤16*rho := by
    intro k; have h := original_tube_graph_residual w i x (8*rho) hw hwmax hxw k; linarith only [h]
  have hwy : ∀ k, |y k-(slope w i k*y i+offset w i k)|≤16*rho := by
    intro k; have h := original_tube_graph_residual w i y (8*rho) hw hwmax hyw k; linarith only [h]
  have hvr := graph_pair_residual x y (slope v i) (offset v i) i rho hvx hvy
  have hwr := graph_pair_residual x y (slope w i) (offset w i) i rho hwx hwy
  have ht := abs_sub ((y j-x j)-slope w i j*(y i-x i))
    ((y j-x j)-slope v i j*(y i-x i))
  have hid : ((y j-x j)-slope w i j*(y i-x i))-
      ((y j-x j)-slope v i j*(y i-x i))=
      (slope v i j-slope w i j)*(y i-x i) := by ring
  rw [hid,abs_mul] at ht
  have hm := mul_le_mul_of_nonneg_right hgap (abs_nonneg (y i-x i))
  have hi : |y i-x i|≤64*rho/theta := by
    apply (le_div_iff₀ htheta).mpr
    nlinarith only [hm,ht,hvr j,hwr j]
  have hrdiv : rho≤rho/theta := (le_div_iff₀ htheta).mpr (by nlinarith only [htheta1,hrho])
  have hcoord (k : Fin 3) : |y k-x k|≤96*rho/theta := by
    have hh := abs_add_le ((y k-x k)-slope v i k*(y i-x i)) (slope v i k*(y i-x i))
    rw [sub_add_cancel,abs_mul] at hh
    have ha := mul_le_mul_of_nonneg_right (original_slope_bound v i hv hvmax k) (abs_nonneg (y i-x i))
    have hsc : 64*rho/theta+32*rho≤96*rho/theta := by
      have he₁ : 64*rho/theta=64*(rho/theta) := by ring
      have he₂ : 96*rho/theta=96*(rho/theta) := by ring
      rw [he₁,he₂]; linarith only [hrdiv]
    linarith only [hh,ha,hvr k,hi,hsc]
  have hs (k : Fin 3) : (x k-y k)^2≤(96*rho/theta)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
    simpa only [sq_abs,sub_sq_comm (y k) (x k)] using hh
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤192*rho/theta)).mpr
  have he : 192*rho/theta=2*(96*rho/theta) := by ring
  rw [he]
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg (96*rho/theta)]

/-- Original common-point populations are charged to an original centered
Frostman ball, with the large-radius case paid by the total original mass. -/
theorem original_transverse_intersection_card (P : Finset Point3) (v w : Pair3)
    (delta eta rho theta : ℝ) (i j : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho)
    (htheta : 0<theta) (htheta1 : theta≤1)
    (hv : v.2 i-v.1 i≠0) (hw : w.2 i-w.1 i≠0)
    (hvmax : ∀ k, |v.2 k-v.1 k|≤|v.2 i-v.1 i|)
    (hwmax : ∀ k, |w.2 k-w.1 k|≤|w.2 i-w.1 i|)
    (hgap : theta≤|slope v i j-slope w i j|)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    (((physicalPairTube3 P (8*rho) v)∩(physicalPairTube3 P (8*rho) w)).card : ℝ)*theta^2≤
      40000*delta^(-eta)*rho^2*P.card := by
  let S := (physicalPairTube3 P (8*rho) v)∩(physicalPairTube3 P (8*rho) w)
  have hrho : 0<rho := hd.trans_le hquery
  have hK : 1≤delta^(-eta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta≤0 by linarith only [heta])
  have hKp : 0≤delta^(-eta) := by positivity
  have hc : (S.card : ℝ)≤P.card := Nat.cast_le.mpr (Finset.card_le_card (by
    intro p hp; exact (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).1))
  by_cases hsmall : 192*rho/theta≤1
  · by_cases hS : S.Nonempty
    · obtain ⟨p,hp⟩ := hS
      have hpv := Finset.mem_filter.mp (Finset.mem_inter.mp hp).1
      have hpw := Finset.mem_filter.mp (Finset.mem_inter.mp hp).2
      have hsub : S⊆P.filter (fun q => distance3 p q≤192*rho/theta) := by
        intro q hq
        have hqv := Finset.mem_filter.mp (Finset.mem_inter.mp hq).1
        have hqw := Finset.mem_filter.mp (Finset.mem_inter.mp hq).2
        exact Finset.mem_filter.mpr ⟨hqv.1,original_transverse_intersection_diameter v w p q rho theta
          i j hrho.le htheta htheta1 hv hw hvmax hwmax hgap hpv.2 hpw.2 hqv.2 hqw.2⟩
      have hlow : delta≤192*rho/theta := by
        apply (le_div_iff₀ htheta).mpr
        have hh := mul_le_mul_of_nonneg_left htheta1 hd.le
        nlinarith only [hh,hquery,hrho]
      have hfr := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hfrostman p hpv.1 (192*rho/theta) hlow hsmall)
      have hh := mul_le_mul_of_nonneg_right hfr (sq_nonneg theta)
      have he : delta^(-eta)*(192*rho/theta)^2*(P.card : ℝ)*theta^2=
          36864*delta^(-eta)*rho^2*P.card := by field_simp; ring
      rw [he] at hh
      change (S.card : ℝ)*theta^2≤_
      nlinarith only [hh,mul_nonneg (mul_nonneg hKp (sq_nonneg rho)) (Nat.cast_nonneg P.card)]
    · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      change (S.card : ℝ)*theta^2≤_
      rw [hz]; simp only [Finset.card_empty,Nat.cast_zero,zero_mul]; positivity
  · have hlarge : theta<192*rho := by
      simpa only [one_mul] using (lt_div_iff₀ htheta).mp (lt_of_not_ge hsmall)
    have hsq : theta^2≤36864*rho^2 := by nlinarith only [hlarge,htheta,hrho]
    have hh := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)
    have hbound := mul_le_mul_of_nonneg_right hc (sq_nonneg rho)
    have hKbound := mul_le_mul_of_nonneg_right hK (mul_nonneg (sq_nonneg rho) (Nat.cast_nonneg P.card))
    change (S.card : ℝ)*theta^2≤_
    nlinarith only [hh,hbound,hKbound,mul_nonneg (sq_nonneg rho) (Nat.cast_nonneg P.card)]

end OriginalThreeDimensionalTransverseWedgeGeometry
end

/- Source section: OriginalThreeDimensionalDenseWedgeCount -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalDenseWedgeCount
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTransverseWedgeGeometry

def graphRow (P : Finset Point3) (G : Finset Pair3) (p : Point3) : Finset Point3 :=
  P.filter (fun q => (p,q)∈G)

def goodRow (P : Finset Point3) (G : Finset Pair3) (i : Fin 3) (gamma : ℝ)
    (p : Point3) : Finset Pair3 :=
  ((graphRow P G p).product (graphRow P G p)).filter
    (fun z => ¬∀ j, |slope (p,z.1) i j-slope (p,z.2) i j|≤gamma)

def goodWedges (P : Finset Point3) (G : Finset Pair3) (i : Fin 3) (gamma : ℝ) :
    Finset (Σ _p : Point3, Pair3) := P.sigma (goodRow P G i gamma)

lemma original_graph_row_card (P : Finset Point3) (G : Finset Pair3) (p : Point3)
    (hG : G⊆P.product P) :
    (graphRow P G p).card=(G.filter (fun z => z.1=p)).card := by
  apply Finset.card_bij (fun q _ => (p,q))
  · intro q hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).2,rfl⟩
  · intro q _hq r _hr he
    exact congrArg Prod.snd he
  · intro z hz
    obtain ⟨hzG,hzp⟩ := Finset.mem_filter.mp hz
    refine ⟨z.2,Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hG hzG)).2,?_⟩,?_⟩
    · simpa only [← hzp,Prod.mk.eta] using hzG
    · exact Prod.ext hzp.symm rfl

lemma original_graph_row_sum (P : Finset Point3) (G : Finset Pair3)
    (hG : G⊆P.product P) :
    (∑ p∈P, ((graphRow P G p).card : ℝ))=G.card := by
  have hc := Finset.card_eq_sum_card_fiberwise
    (f:=fun z : Pair3 => z.1) (s:=G) (t:=P)
    (fun z hz => (Finset.mem_product.mp (hG hz)).1)
  have hh : (G.card : ℝ)=∑ p∈P, ((G.filter (fun z => z.1=p)).card : ℝ) := by exact_mod_cast hc
  simpa only [original_graph_row_card P G _ hG] using hh.symm

/-- Each actual row's discarded ordered wedges are paid by the original
4gamma-tube Frostman estimate, without any row pruning. -/
theorem original_row_bad_wedge_count (P : Finset Point3) (G : Finset Pair3)
    (delta eta gamma : ℝ) (i : Fin 3) (p : Point3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤4*gamma) (hgamma1 : 4*gamma≤1)
    (hp : p∈P) (hne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun y => distance3 x y≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ((graphRow P G p).card : ℝ)^2≤((goodRow P G i gamma p).card : ℝ)+
      (graphRow P G p).card*(1600*delta^(-eta)*gamma*P.card) := by
  let D := graphRow P G p
  let B := (D.product D).filter (fun z => ∀ j, |slope (p,z.1) i j-slope (p,z.2) i j|≤gamma)
  have hc := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers B D Prod.fst
    (1600*delta^(-eta)*gamma*P.card)
    (fun z hz => (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1) (by
      intro q hq
      let F := B.filter (fun z => z.1=q)
      let C := P.filter (fun y => y i-p i≠0 ∧
        ∀ j, |slope (p,q) i j-slope (p,y) i j|≤gamma)
      have hFC : F.card≤C.card := Finset.card_le_card_of_injOn Prod.snd (by
        intro z hz
        obtain ⟨hzB,hzq⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzD,hzclose⟩ := Finset.mem_filter.mp hzB
        have hz₂ := Finset.mem_filter.mp (Finset.mem_product.mp hzD).2
        apply Finset.mem_filter.mpr
        refine ⟨hz₂.1,hne (p,z.2) hz₂.2,?_⟩
        simpa only [hzq] using hzclose) (by
        intro z hz w hw he
        exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm) he)
      have ht := original_bad_wedge_neighbors_card P p q delta eta gamma i hd hd1 heta
        hquery hgamma1 hp (hne (p,q) (Finset.mem_filter.mp hq).2) hbox hfrostman
      exact (Nat.cast_le.mpr hFC).trans ht)
  have he := Finset.card_filter_add_card_filter_not
    (s:=D.product D) (p:=fun z => ∀ j, |slope (p,z.1) i j-slope (p,z.2) i j|≤gamma)
  have he' : (B.card : ℝ)+((goodRow P G i gamma p).card : ℝ)=((D.card : ℝ))^2 := by
    exact_mod_cast (show B.card+(goodRow P G i gamma p).card=D.card^2 by
      simpa only [B,D,goodRow,Finset.product_eq_sprod,Finset.card_product,pow_two] using he)
  change (D.card : ℝ)^2≤_
  nlinarith only [hc,he']

/-- Cauchy--Schwarz on all original graph rows, followed by the genuine
bad-wedge tube estimate, produces the full quantitative good-wedge count. -/
theorem original_dense_good_wedge_count (P : Finset Point3) (G : Finset Pair3)
    (delta eta gamma lam : ℝ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤4*gamma) (hgamma1 : 4*gamma≤1)
    (hlam : 0≤lam) (hbudget : 1600*delta^(-eta)*gamma≤lam/4)
    (hP : P.Nonempty) (hG : G⊆P.product P)
    (hdense : lam*(P.card : ℝ)^2≤G.card)
    (hne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun y => distance3 x y≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    (3/4:ℝ)*lam^2*(P.card : ℝ)^3≤(goodWedges P G i gamma).card := by
  let E : ℝ := ∑ p∈P, ((graphRow P G p).card : ℝ)^2
  have hsum := original_graph_row_sum P G hG
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => ((graphRow P G p).card : ℝ)) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,hsum] at hcs
  change (G.card : ℝ)^2≤E*(P.card : ℝ) at hcs
  have hn : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hge : lam*(P.card : ℝ)*(G.card : ℝ)≤E := by
    apply (mul_le_mul_iff_of_pos_right hn).mp
    have hh := mul_le_mul_of_nonneg_right hdense (Nat.cast_nonneg G.card)
    nlinarith only [hh,hcs]
  have hrows := Finset.sum_le_sum (fun p hp => original_row_bad_wedge_count P G delta eta gamma
    i p hd hd1 heta hquery hgamma1 hp hne hbox hfrostman)
  have hw : ((goodWedges P G i gamma).card : ℝ)=∑ p∈P, ((goodRow P G i gamma p).card : ℝ) := by
    simp only [goodWedges,Finset.card_sigma,Nat.cast_sum]
  have hrowss : E≤(goodWedges P G i gamma).card+
      (G.card : ℝ)*(1600*delta^(-eta)*gamma*P.card) := by
    simpa only [Finset.sum_add_distrib,← Finset.sum_mul,hsum,← hw,E] using hrows
  have hb := mul_le_mul_of_nonneg_right hbudget
    (mul_nonneg (Nat.cast_nonneg P.card) (Nat.cast_nonneg G.card))
  have hgd := mul_le_mul_of_nonneg_left hdense
    (show 0≤lam*(P.card : ℝ) by positivity)
  nlinarith only [hge,hrowss,hb,hgd]

end OriginalThreeDimensionalDenseWedgeCount
end

/- Source section: OriginalThreeDimensionalRepresentativeWedges -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalRepresentativeWedges
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeFrostman OriginalThreeDimensionalPairTubeFamily
open OriginalThreeDimensionalCommonChart OriginalThreeDimensionalTransverseWedgeGeometry
open OriginalThreeDimensionalDenseWedgeCount

/-- A common chart and an actual original representative map retain the
literal parameter-cell equality as well as both original endpoints. -/
theorem exists_original_cell_preserving_chart_map (P : Finset Point3) (G : Finset Pair3)
    (delta eta rho : ℝ) (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤rho) (hrho : 8*rho≤1)
    (hG : G⊆P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ∃ i : Fin 3, ∃ R : Finset Pair3, ∃ f : Pair3→Pair3,
      R⊆chartPairs G i ∧ Set.InjOn (parameterCell rho i) R ∧
      G.card≤3*(chartPairs G i).card ∧
      ∀ z∈chartPairs G i, f z∈R ∧ parameterCell rho i z=parameterCell rho i (f z) ∧
        z.1∈physicalPairTube3 P (8*rho) (f z) ∧
        z.2∈physicalPairTube3 P (8*rho) (f z) ∧
        physicalPairTube3 P rho z⊆physicalPairTube3 P (8*rho) (f z) := by
  obtain ⟨i,hchart,hcount⟩ := exists_original_common_chart G hne
  obtain ⟨R,hR,hinj,_himage,_hcard,hmap⟩ := exists_original_parameter_tube_family
    P (chartPairs G i) delta eta rho i hd hd1 heta hquery hrho (hchart.trans hG) hbox
    (fun z hz => (Finset.mem_filter.mp hz).2.1)
    (fun z hz => (Finset.mem_filter.mp hz).2.2) hfrostman
  have hall : ∀ z : Pair3, ∃ v : Pair3, z∈chartPairs G i → v∈R ∧
      parameterCell rho i z=parameterCell rho i v ∧
      physicalPairTube3 P rho z⊆physicalPairTube3 P (8*rho) v := by
    intro z
    by_cases hz : z∈chartPairs G i
    · obtain ⟨v,hv,hc,ht⟩ := hmap z hz
      exact ⟨v,fun _ => ⟨hv,hc,ht⟩⟩
    · exact ⟨z,fun h => False.elim (hz h)⟩
  choose f hf using hall
  refine ⟨i,R,f,hR,hinj,hcount,?_⟩
  intro z hz
  obtain ⟨hv,hc,ht⟩ := hf z hz
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp (hG (hchart hz))
  have he := original_endpoints_mem_tube z rho (hd.trans_le hquery).le
  exact ⟨hv,hc,ht (Finset.mem_filter.mpr ⟨hp,he.1⟩),
    ht (Finset.mem_filter.mpr ⟨hq,he.2⟩),ht⟩

def transversePairs (P : Finset Point3) (R : Finset Pair3) (rho theta : ℝ)
    (i : Fin 3) : Finset (Pair3×Pair3) :=
  (R.product R).filter (fun z => (∃ j, theta≤|slope z.1 i j-slope z.2 i j|) ∧
    ∃ p∈P, p∈physicalTube3 z.1.1 z.1.2 (8*rho) ∧
      p∈physicalTube3 z.2.1 z.2.2 (8*rho))

def wedgeRepresentatives (f : Pair3→Pair3) (w : Σ _p : Point3, Pair3) : Pair3×Pair3 :=
  (f (w.1,w.2.1),f (w.1,w.2.2))

/-- Every counted good original wedge gives an actual transverse pair
with its own original root lying in both representative tubes. -/
theorem original_good_wedge_representatives_mem (P : Finset Point3) (G R : Finset Pair3)
    (f : Pair3→Pair3) (rho gamma : ℝ) (i : Fin 3)
    (hrho : 0<rho) (hsmall : rho≤gamma/4)
    (hmap : ∀ z∈G, f z∈R ∧ parameterCell rho i z=parameterCell rho i (f z) ∧
      z.1∈physicalPairTube3 P (8*rho) (f z) ∧ z.2∈physicalPairTube3 P (8*rho) (f z)) :
    ∀ w∈goodWedges P G i gamma,
      wedgeRepresentatives f w∈transversePairs P R rho (gamma/2) i := by
  intro w hw
  obtain ⟨hp,hrow⟩ := Finset.mem_sigma.mp hw
  obtain ⟨hq,hgood⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
  have hm₁ := hmap (w.1,w.2.1) (Finset.mem_filter.mp hq₁).2
  have hm₂ := hmap (w.1,w.2.2) (Finset.mem_filter.mp hq₂).2
  push Not at hgood
  obtain ⟨j,hj⟩ := hgood
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm₁.1,hm₂.1⟩,
    ⟨j,original_transverse_parameter_transfer (w.1,w.2.1) (w.1,w.2.2)
      (f (w.1,w.2.1)) (f (w.1,w.2.2)) rho gamma i j hrho hsmall hm₁.2.1 hm₂.2.1 hj⟩,
    w.1,hp,(Finset.mem_filter.mp hm₁.2.2.1).2,(Finset.mem_filter.mp hm₂.2.2.1).2⟩

def representativeRow (P : Finset Point3) (G : Finset Pair3) (f : Pair3→Pair3)
    (p : Point3) (v : Pair3) : Finset Point3 :=
  P.filter (fun q => (p,q)∈G ∧ f (p,q)=v)

/-- Every root/representative row fiber consists of actual original points
in that representative's physical 8rho tube. -/
theorem original_representative_row_card (P : Finset Point3) (G R : Finset Pair3)
    (f : Pair3→Pair3) (p : Point3) (v : Pair3) (delta eta rho : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : 8*rho≤1)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hmap : ∀ z∈G, f z∈R ∧ z.1∈physicalPairTube3 P (8*rho) (f z) ∧
      z.2∈physicalPairTube3 P (8*rho) (f z)) :
    ((representativeRow P G f p v).card : ℝ)≤3200*delta^(-eta)*rho*P.card := by
  have hsub : representativeRow P G f p v⊆physicalPairTube3 P (8*rho) v := by
    intro q hq
    obtain ⟨_hqP,hqG,he⟩ := Finset.mem_filter.mp hq
    simpa only [he] using (hmap (p,q) hqG).2.2
  have hc : ((representativeRow P G f p v).card : ℝ)≤(physicalPairTube3 P (8*rho) v).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have ht := original_tube_two_frostman_count P v delta eta (8*rho) hd hd1 heta
    (by have hp := hd.trans_le hquery; linarith only [hp,hquery]) hrho1 hbox hfrostman
  linarith only [hc,ht]

/-- For a fixed actual representative pair, the original-root map and
actual neighbor fibers give the complete multiplicity charge. -/
theorem original_good_wedge_representative_fiber (P : Finset Point3) (G R : Finset Pair3)
    (f : Pair3→Pair3) (v w : Pair3) (delta eta rho gamma theta : ℝ) (i j : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : 8*rho≤1)
    (htheta : 0<theta) (htheta1 : theta≤1)
    (hv : v.2 i-v.1 i≠0) (hw : w.2 i-w.1 i≠0)
    (hvmax : ∀ k, |v.2 k-v.1 k|≤|v.2 i-v.1 i|)
    (hwmax : ∀ k, |w.2 k-w.1 k|≤|w.2 i-w.1 i|)
    (hgap : theta≤|slope v i j-slope w i j|)
    (hbox : ∀ x∈P, ∀ k, |x k|≤1)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hmap : ∀ z∈G, f z∈R ∧ z.1∈physicalPairTube3 P (8*rho) (f z) ∧
      z.2∈physicalPairTube3 P (8*rho) (f z)) :
    (((goodWedges P G i gamma).filter (fun a => wedgeRepresentatives f a=(v,w))).card : ℝ)*theta^2≤
      409600000000*(delta^(-eta))^3*rho^4*(P.card : ℝ)^3 := by
  let F := (goodWedges P G i gamma).filter (fun a => wedgeRepresentatives f a=(v,w))
  let S := (physicalPairTube3 P (8*rho) v)∩(physicalPairTube3 P (8*rho) w)
  let B : ℝ := 3200*delta^(-eta)*rho*P.card
  have hrho : 0<rho := hd.trans_le hquery
  have hB : 0≤B := by dsimp [B]; positivity
  have hparts : ∀ a∈F, (a.1,a.2.1)∈G ∧ (a.1,a.2.2)∈G ∧
      f (a.1,a.2.1)=v ∧ f (a.1,a.2.2)=w := by
    intro a ha
    obtain ⟨haW,he⟩ := Finset.mem_filter.mp ha
    have hrow := (Finset.mem_filter.mp (Finset.mem_sigma.mp haW).2).1
    exact ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hrow).1).2,
      (Finset.mem_filter.mp (Finset.mem_product.mp hrow).2).2,
      congrArg Prod.fst he,congrArg Prod.snd he⟩
  have hf := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers F S Sigma.fst (B^2) (by
    intro a ha
    obtain ⟨ha₁,ha₂,he₁,he₂⟩ := hparts a ha
    exact Finset.mem_inter.mpr ⟨by simpa only [he₁] using (hmap _ ha₁).2.1,
      by simpa only [he₂] using (hmap _ ha₂).2.1⟩) (by
    intro p _hp
    have hinj : (F.filter (fun a => a.1=p)).card≤
        ((representativeRow P G f p v).product (representativeRow P G f p w)).card :=
      Finset.card_le_card_of_injOn Sigma.snd (by
        intro a ha
        obtain ⟨haF,hap⟩ := Finset.mem_filter.mp ha
        obtain ⟨ha₁,ha₂,he₁,he₂⟩ := hparts a haF
        have hrow := (Finset.mem_filter.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp haF).1).2).1
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hrow).1).1,?_,?_⟩
          · simpa only [hap] using ha₁
          · simpa only [hap] using he₁
        · apply Finset.mem_filter.mpr
          refine ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hrow).2).1,?_,?_⟩
          · simpa only [hap] using ha₂
          · simpa only [hap] using he₂) (by
        intro a ha b hb he
        apply Sigma.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
        exact heq_of_eq he)
    have hc : ((F.filter (fun a => a.1=p)).card : ℝ)≤
        (representativeRow P G f p v).card*(representativeRow P G f p w).card := by
      exact_mod_cast (by simpa only [Finset.product_eq_sprod,Finset.card_product] using hinj)
    have hv' := original_representative_row_card P G R f p v delta eta rho hd hd1 heta hquery hrho1
      hbox hfrostman hmap
    have hw' := original_representative_row_card P G R f p w delta eta rho hd hd1 heta hquery hrho1
      hbox hfrostman hmap
    have hm := mul_le_mul hv' hw' (Nat.cast_nonneg (representativeRow P G f p w).card) hB
    exact hc.trans (by simpa only [← pow_two] using hm))
  have hS := original_transverse_intersection_card P v w delta eta rho theta i j hd hd1 heta
    hquery htheta htheta1 hv hw hvmax hwmax hgap hfrostman
  have hf' := mul_le_mul_of_nonneg_right hf (sq_nonneg theta)
  have hS' := mul_le_mul_of_nonneg_right hS (sq_nonneg B)
  change (F.card : ℝ)*theta^2≤_
  dsimp [B,S] at hf' hS'
  nlinarith only [hf',hS']

end OriginalThreeDimensionalRepresentativeWedges
end

/- Source section: OriginalThreeDimensionalTransverseHairbrush -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalTransverseHairbrush
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeFamilyEnergy OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalDenseWedgeCount OriginalThreeDimensionalRepresentativeWedges

def brush (P : Finset Point3) (R : Finset Pair3) (rho theta : ℝ) (i : Fin 3)
    (v : Pair3) : Finset Pair3 :=
  R.filter (fun w => (v,w)∈transversePairs P R rho theta i)

/-- The source-dense original graph forces the critical rho^-4 population
of actual transverse representative pairs with actual original roots. -/
theorem original_transverse_pairs_lower_count (P : Finset Point3) (G R : Finset Pair3)
    (f : Pair3→Pair3) (delta eta rho gamma lam : ℝ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : 8*rho≤1)
    (hgamma : 0<gamma) (hgamma1 : 4*gamma≤1) (hquerygamma : delta≤4*gamma)
    (hsmall : rho≤gamma/4) (hlam : 0≤lam)
    (hbudget : 1600*delta^(-eta)*gamma≤lam/4)
    (hP : P.Nonempty) (hG : G⊆P.product P) (hdense : lam*(P.card : ℝ)^2≤G.card)
    (hGne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hRne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hRmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hmap : ∀ z∈G, f z∈R ∧ parameterCell rho i z=parameterCell rho i (f z) ∧
      z.1∈physicalPairTube3 P (8*rho) (f z) ∧ z.2∈physicalPairTube3 P (8*rho) (f z)) :
    lam^2*(gamma/2)^2≤1000000000000*(delta^(-eta))^3*rho^4*
      (transversePairs P R rho (gamma/2) i).card := by
  let W := goodWedges P G i gamma
  let J := transversePairs P R rho (gamma/2) i
  let C : ℝ := 409600000000*(delta^(-eta))^3*rho^4*(P.card : ℝ)^3
  have hm := original_good_wedge_representatives_mem P G R f rho gamma i (hd.trans_le hquery) hsmall hmap
  have hc := Finset.card_eq_sum_card_fiberwise (s:=W) (t:=J) (f:=wedgeRepresentatives f) hm
  have hsum : (W.card : ℝ)*(gamma/2)^2≤(J.card : ℝ)*C := by
    have he : (W.card : ℝ)=∑ z∈J, ((W.filter (fun a => wedgeRepresentatives f a=z)).card : ℝ) := by
      exact_mod_cast hc
    rw [he,Finset.sum_mul]
    calc
      _ ≤ ∑ _z∈J, C := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨hzR,hgap,_hroot⟩ := Finset.mem_filter.mp hz
        obtain ⟨hv,hw⟩ := Finset.mem_product.mp hzR
        obtain ⟨j,hj⟩ := hgap
        exact original_good_wedge_representative_fiber P G R f z.1 z.2 delta eta rho gamma (gamma/2)
          i j hd hd1 heta hquery hrho1 (by positivity) (by linarith only [hgamma1])
          (hRne z.1 hv) (hRne z.2 hw) (hRmax z.1 hv) (hRmax z.2 hw) hj hbox hfrostman
          (fun a ha => ⟨(hmap a ha).1,(hmap a ha).2.2⟩)
      _ = _ := by simp
  have hlower := original_dense_good_wedge_count P G delta eta gamma lam i hd hd1 heta
    hquerygamma hgamma1 hlam hbudget hP hG hdense hGne hbox hfrostman
  have hlow := mul_le_mul_of_nonneg_right hlower (sq_nonneg (gamma/2))
  have hPc : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hn : 0<(P.card : ℝ)^3 := pow_pos hPc 3
  have hc' : (3/4:ℝ)*lam^2*(gamma/2)^2≤
      (J.card : ℝ)*(409600000000*(delta^(-eta))^3*rho^4) := by
    apply (mul_le_mul_iff_of_pos_right hn).mp
    dsimp [W,C] at hsum
    nlinarith only [hsum,hlow]
  have hnonneg : 0≤(delta^(-eta))^3*rho^4*(J.card : ℝ) := by positivity
  change lam^2*(gamma/2)^2≤1000000000000*(delta^(-eta))^3*rho^4*(J.card : ℝ)
  nlinarith only [hc',hnonneg]

lemma original_brush_pair_fiber_card (P : Finset Point3) (R : Finset Pair3)
    (rho theta : ℝ) (i : Fin 3) (v : Pair3) :
    (brush P R rho theta i v).card=
      ((transversePairs P R rho theta i).filter (fun z => z.1=v)).card := by
  apply Finset.card_bij (fun w _ => (v,w))
  · intro w hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).2,rfl⟩
  · intro w _hw z _hz he
    exact congrArg Prod.snd he
  · intro z hz
    obtain ⟨hzJ,hzv⟩ := Finset.mem_filter.mp hz
    have hzR := (Finset.mem_product.mp (Finset.mem_filter.mp hzJ).1).2
    refine ⟨z.2,Finset.mem_filter.mpr ⟨hzR,?_⟩,Prod.ext hzv.symm rfl⟩
    simpa only [← hzv,Prod.mk.eta] using hzJ

/-- A largest actual stem row contains at least the mean number of
actual transverse intersections, and every member keeps its original root. -/
theorem exists_original_largest_transverse_brush (P : Finset Point3) (R : Finset Pair3)
    (rho theta : ℝ) (i : Fin 3) (hR : R.Nonempty) :
    ∃ v∈R, (transversePairs P R rho theta i).card≤R.card*(brush P R rho theta i v).card ∧
      ∀ w∈brush P R rho theta i v,
        w∈R ∧ (∃ j, theta≤|slope v i j-slope w i j|) ∧
        ∃ p∈P, p∈physicalTube3 v.1 v.2 (8*rho) ∧ p∈physicalTube3 w.1 w.2 (8*rho) := by
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image R (fun w => (brush P R rho theta i w).card) hR
  have he := Finset.card_eq_sum_card_fiberwise
    (s:=transversePairs P R rho theta i) (t:=R) (f:=Prod.fst)
    (fun z hz => (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1)
  refine ⟨v,hv,?_,?_⟩
  · rw [he]
    calc
      _ = ∑ w∈R, (brush P R rho theta i w).card := by
        apply Finset.sum_congr rfl; intro w _hw; exact (original_brush_pair_fiber_card P R rho theta i w).symm
      _ ≤ ∑ _w∈R, (brush P R rho theta i v).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  · intro w hw
    obtain ⟨hwR,hwJ⟩ := Finset.mem_filter.mp hw
    exact ⟨hwR,(Finset.mem_filter.mp hwJ).2⟩

/-- The already proved original incidence energy bounds a genuinely rich
cell-injective family, with the original point population canceled. -/
theorem original_rich_family_scaled_upper (P : Finset Point3) (R : Finset Pair3)
    (delta eta rho nu : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : rho≤1)
    (hnu : 0<nu) (hP : P.Nonempty) (hlast : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hrich : ∀ z∈R, nu*rho*P.card≤((physicalPairTube3 P (8*rho) z).card : ℝ)) :
    (R.card : ℝ)*nu^2*rho^2≤4000000000*((N:ℝ)+1)*delta^(-eta) := by
  have hrho : 0<rho := hd.trans_le hquery
  have hn : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  have he := original_tube_family_square_energy P R delta eta rho N i hd hd1 heta hquery hrho1
    hlast hbox hne hmax hcell hfrostman
  have hl : (R.card : ℝ)*(nu*rho*P.card)^2≤
      ∑ z∈R, ((physicalPairTube3 P (8*rho) z).card : ℝ)^2 := by
    calc
      _ = ∑ _z∈R, (nu*rho*P.card)^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz => pow_le_pow_left₀ (by positivity) (hrich z hz) 2)
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hn)).mp
  nlinarith only [hl,he]

/-- Complete graph-to-hairbrush count from the original sources and their
actual cell map. The returned brush is literal, with transverse slopes
and an original common point for every one of its tubes. -/
theorem exists_original_transverse_hairbrush (P : Finset Point3) (G R : Finset Pair3)
    (f : Pair3→Pair3) (delta eta rho gamma lam nu : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : 8*rho≤1)
    (hgamma : 0<gamma) (hgamma1 : 4*gamma≤1) (hquerygamma : delta≤4*gamma)
    (hsmall : rho≤gamma/4) (hlam : 0<lam) (hnu : 0<nu)
    (hbudget : 1600*delta^(-eta)*gamma≤lam/4)
    (hP : P.Nonempty) (hG : G⊆P.product P) (hdense : lam*(P.card : ℝ)^2≤G.card)
    (hGne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hRne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hRmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hlast : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hmap : ∀ z∈G, f z∈R ∧ parameterCell rho i z=parameterCell rho i (f z) ∧
      z.1∈physicalPairTube3 P (8*rho) (f z) ∧ z.2∈physicalPairTube3 P (8*rho) (f z))
    (hrich : ∀ z∈R, nu*rho*P.card≤((physicalPairTube3 P (8*rho) z).card : ℝ)) :
    ∃ v∈R, lam^2*(gamma/2)^2*nu^2≤
      10000000000000000000000*((N:ℝ)+1)*(delta^(-eta))^4*rho^2*(brush P R rho (gamma/2) i v).card ∧
      ∀ w∈brush P R rho (gamma/2) i v,
        w∈R ∧ (∃ j, gamma/2≤|slope v i j-slope w i j|) ∧
        ∃ p∈P, p∈physicalTube3 v.1 v.2 (8*rho) ∧ p∈physicalTube3 w.1 w.2 (8*rho) := by
  have hrho : 0<rho := hd.trans_le hquery
  have hlower := original_transverse_pairs_lower_count P G R f delta eta rho gamma lam i
    hd hd1 heta hquery hrho1 hgamma hgamma1 hquerygamma hsmall hlam.le hbudget hP hG hdense
    hGne hRne hRmax hbox hfrostman hmap
  have hR : R.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he,transversePairs,Finset.product_eq_sprod] at hlower
    have hp : 0<lam^2*(gamma/2)^2 := by positivity
    exact (not_le_of_gt hp) hlower
  obtain ⟨v,hv,hstem,hbrush⟩ := exists_original_largest_transverse_brush P R rho (gamma/2) i hR
  refine ⟨v,hv,?_,hbrush⟩
  have hupper := original_rich_family_scaled_upper P R delta eta rho nu N i hd hd1 heta hquery
    (by linarith only [hrho1,hrho]) hnu hP hlast hbox hRne hRmax hcell hfrostman hrich
  have hstem' : ((transversePairs P R rho (gamma/2) i).card : ℝ)≤
      (R.card : ℝ)*(brush P R rho (gamma/2) i v).card := by exact_mod_cast hstem
  have hmul := mul_le_mul_of_nonneg_left hstem'
    (show 0≤1000000000000*(delta^(-eta))^3*rho^4 by positivity)
  have hl := mul_le_mul_of_nonneg_right (hlower.trans hmul) (sq_nonneg nu)
  have hu := mul_le_mul_of_nonneg_left hupper
    (show 0≤1000000000000*(delta^(-eta))^3*rho^2*(brush P R rho (gamma/2) i v).card by positivity)
  have hp : 0≤((N:ℝ)+1)*(delta^(-eta))^4*rho^2*(brush P R rho (gamma/2) i v).card := by positivity
  nlinarith only [hl,hu,hp]

end OriginalThreeDimensionalTransverseHairbrush
end

/- Source section: OriginalThreeDimensionalSourceHairbrush -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
namespace OriginalThreeDimensionalSourceHairbrush
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalPairEnergy OriginalThreeDimensionalCommonChart
open OriginalThreeDimensionalRepresentativeWedges OriginalThreeDimensionalTransverseHairbrush

/-- The original dense ordered graph alone supplies an actual critical
transverse hairbrush. Representative counts, cell maps, and original common
points are constructed; no brush or intersection population is a premise. -/
theorem exists_original_dense_graph_hairbrush (P : Finset Point3) (G : Finset Pair3)
    (delta eta rho gamma lam nu : ℝ) (N : ℕ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho) (hrho1 : 8*rho≤1)
    (hgamma : 0<gamma) (hgamma1 : 4*gamma≤1) (hquerygamma : delta≤4*gamma)
    (hsmall : rho≤gamma/4) (hlam : 0<lam) (hnu : 0<nu)
    (hbudget : 1600*delta^(-eta)*gamma≤lam/12)
    (hP : P.Nonempty) (hG : G⊆P.product P) (hdense : lam*(P.card : ℝ)^2≤G.card)
    (hne : ∀ z∈G, z.1≠z.2) (hlast : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hfrostman : ∀ x∈P, ∀ a : ℝ, delta≤a → a≤1 →
      ((P.filter (fun y => distance3 x y≤a)).card : ℝ)≤delta^(-eta)*a^2*P.card)
    (hrich : ∀ z∈G, nu*rho*P.card≤((physicalPairTube3 P rho z).card : ℝ)) :
    ∃ i : Fin 3, ∃ R : Finset Pair3, ∃ v∈R,
      R⊆G ∧ Set.InjOn (parameterCell rho i) R ∧
      (∀ z∈R, z.2 i-z.1 i≠0 ∧ ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|) ∧
      (lam/3)^2*(gamma/2)^2*nu^2≤
        10000000000000000000000*((N:ℝ)+1)*(delta^(-eta))^4*rho^2*(brush P R rho (gamma/2) i v).card ∧
      ∀ w∈brush P R rho (gamma/2) i v,
        w∈R ∧ (∃ j, gamma/2≤|slope v i j-slope w i j|) ∧
        ∃ p∈P, p∈physicalTube3 v.1 v.2 (8*rho) ∧ p∈physicalTube3 w.1 w.2 (8*rho) := by
  have hrho : 0<rho := hd.trans_le hquery
  obtain ⟨i,R,f,hR,hcell,hcard,hmap⟩ := exists_original_cell_preserving_chart_map
    P G delta eta rho hd hd1 heta hquery hrho1 hG hne hbox hfrostman
  have hchart : chartPairs G i⊆G := Finset.filter_subset _ _
  have hRchart : ∀ z∈R, z.2 i-z.1 i≠0 ∧ ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i| :=
    fun z hz => (Finset.mem_filter.mp (hR hz)).2
  have hdense' : (lam/3)*(P.card : ℝ)^2≤(chartPairs G i).card := by
    have hc : (G.card : ℝ)≤3*(chartPairs G i).card := by exact_mod_cast hcard
    nlinarith only [hc,hdense]
  have hrich' : ∀ z∈R, nu*rho*P.card≤((physicalPairTube3 P (8*rho) z).card : ℝ) := by
    intro z hz
    apply (hrich z (hchart (hR hz))).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hpP,l,hl⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpP,l,hl.trans (by linarith only [hrho])⟩
  obtain ⟨v,hv,hcount,hbrush⟩ := exists_original_transverse_hairbrush
    P (chartPairs G i) R f delta eta rho gamma (lam/3) nu N i hd hd1 heta hquery hrho1
    hgamma hgamma1 hquerygamma hsmall (by positivity) hnu (by linarith only [hbudget]) hP
    (hchart.trans hG) hdense' (fun z hz => (Finset.mem_filter.mp hz).2.1)
    (fun z hz => (hRchart z hz).1) (fun z hz => (hRchart z hz).2) hcell hlast hbox hfrostman
    (fun z hz => ⟨(hmap z hz).1,(hmap z hz).2.1,(hmap z hz).2.2.1,(hmap z hz).2.2.2.1⟩) hrich'
  exact ⟨i,R,v,hv,hR.trans hchart,hcell,hRchart,hcount,hbrush⟩

end OriginalThreeDimensionalSourceHairbrush
end
