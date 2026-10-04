import Theorems.Thm_StickyKakeya4_native_original_annular_row_bound
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped BigOperators
noncomputable section
namespace OriginalAnnularGraphDeletion
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalAnnularRowCover NativeOriginalAnnularRowBound

/-- Reversing the two original endpoints leaves the actual affine line and
its physical neighbourhood unchanged. -/
theorem physical_pair_tube_swap (Pts : Finset Point) (w : ℝ) (z : Pair) :
    physicalPairTube Pts w z.swap=physicalPairTube Pts w z := by
  classical
  have hline (z : Pair) (u : ℝ) : linePoint z.swap u=linePoint z (1-u) := by
    apply Prod.ext <;> dsimp [linePoint] <;> ring
  ext q
  simp only [physicalPairTube,Finset.mem_filter]
  constructor
  · rintro ⟨hq,u,hu⟩
    exact ⟨hq,1-u,by simpa only [hline] using hu⟩
  · rintro ⟨hq,u,hu⟩
    refine ⟨hq,1-u,?_⟩
    rw [hline,show (1:ℝ)-(1-u)=u by ring]
    exact hu

def badPairGraph (Pts : Finset Point) (G : Finset Pair) (w tau H : ℝ) : Finset Pair := by
  classical
  exact (Pts.product Pts).filter (fun z => z∈G ∧
    H≤((annularSupport Pts z.1 z.2 w tau).card : ℝ))

/-- Exact counting of the original bad graph by its original rooted rows. -/
theorem bad_pair_graph_card (Pts : Finset Point) (G : Finset Pair) (w tau H : ℝ) :
    (badPairGraph Pts G w tau H).card=
      ∑ p∈Pts, (badPartners Pts G p w tau H).card := by
  classical
  simp only [badPairGraph,badPartners,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product]

private theorem bad_pair_graph_bound (Pts : Finset Point) (G : Finset Pair)
    (w tau H B : ℝ)
    (hrow : ∀ p∈Pts, ((badPartners Pts G p w tau H).card : ℝ)≤B*Pts.card) :
    ((badPairGraph Pts G w tau H).card : ℝ)≤B*(Pts.card : ℝ)^2 := by
  rw [bad_pair_graph_card,Nat.cast_sum]
  calc
    _ ≤ ∑ _p∈Pts, B*(Pts.card : ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

def retainedAnnularGraph (Pts : Finset Point) (G : Finset Pair)
    (S : Finset ℝ) (w : ℝ) (H : ℝ→ℝ) : Finset Pair := by
  classical
  exact G.filter (fun z => ∀ tau∈S,
    ((annularSupport Pts z.1 z.2 w tau).card : ℝ)<H tau ∧
    ((annularSupport Pts z.2 z.1 w tau).card : ℝ)<H tau)

/-- Delete every actual bad annular pair in either orientation at every
selected scale. The total loss is derived from original Frostman and the
original physical densest-tube profile, not supplied as a retention bound. -/
theorem native_original_annular_graph_deletion
    (Pts : Finset Point) (G : Finset Pair) (S : Finset ℝ) (n : ℕ)
    (delta eta eta' t sigma rho m r : ℝ)
    (hd : 0<delta) (ht2 : t≤2) (hsigma : 0≤sigma) (hsigma1 : sigma≤1)
    (hm : 0<m) (hr : 0<r) (hr1 : r≤1) (hrho : rho∈scaleMenu n)
    (hS : ∀ tau∈S, 0<tau ∧ tau≤1/2 ∧ delta≤2*tau)
    (hGP : G⊆Pts.product Pts)
    (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hlocal : ∀ z∈G, ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤2^(sigma+1)*(R/rho)^sigma*m)
    (hsource : rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m)
    (hfrostman : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) :
    let H := retainedAnnularGraph Pts G S (r^(-3:ℝ)*rho)
      (fun tau => delta^(-eta')*tau^(t-sigma)*m)
    H⊆G ∧
    (∀ z∈H, ∀ tau∈S,
      ((annularSupport Pts z.1 z.2 (r^(-3:ℝ)*rho) tau).card : ℝ)<
        delta^(-eta')*tau^(t-sigma)*m ∧
      ((annularSupport Pts z.2 z.1 (r^(-3:ℝ)*rho) tau).card : ℝ)<
        delta^(-eta')*tau^(t-sigma)*m) ∧
    (G.card : ℝ)≤H.card+1216*S.card*r^(-3*sigma)*delta^(eta'-eta)*(Pts.card : ℝ)^2 := by
  classical
  let w := r^(-3:ℝ)*rho
  let threshold := fun tau => delta^(-eta')*tau^(t-sigma)*m
  let Gt := G.image Prod.swap
  let B : ℝ := 608*r^(-3*sigma)*delta^(eta'-eta)
  have htranspose (z : Pair) (hz : z∈Gt) : z.swap∈G := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    simpa only [Prod.swap_swap] using hy
  have hbad (tau : ℝ) (htau : tau∈S) :
      ((badPairGraph Pts G w tau (threshold tau)).card : ℝ)≤B*(Pts.card : ℝ)^2 := by
    apply bad_pair_graph_bound
    intro p hp
    obtain ⟨hpos,hhalf,hquery⟩ := hS tau htau
    exact native_original_annular_bad_row Pts G p n delta eta eta' t sigma rho m r tau
      hd ht2 hsigma hsigma1 hm hr hr1 hpos hhalf hquery hrho hp hbox
      hdistinct hlocal hsource hfrostman
  have hbadt (tau : ℝ) (htau : tau∈S) :
      ((badPairGraph Pts Gt w tau (threshold tau)).card : ℝ)≤B*(Pts.card : ℝ)^2 := by
    apply bad_pair_graph_bound
    intro p hp
    obtain ⟨hpos,hhalf,hquery⟩ := hS tau htau
    apply native_original_annular_bad_row Pts Gt p n delta eta eta' t sigma rho m r tau
      hd ht2 hsigma hsigma1 hm hr hr1 hpos hhalf hquery hrho hp hbox
    · intro z hz h
      exact hdistinct z.swap (htranspose z hz) h.symm
    · intro z hz R hR hR1
      simpa only [physical_pair_tube_swap] using hlocal z.swap (htranspose z hz) R hR hR1
    · exact hsource
    · exact hfrostman
  let D := S.biUnion (fun tau => badPairGraph Pts G w tau (threshold tau) ∪
    (badPairGraph Pts Gt w tau (threshold tau)).image Prod.swap)
  let H := retainedAnnularGraph Pts G S w threshold
  have hD : (D.card : ℝ)≤2*S.card*B*(Pts.card : ℝ)^2 := by
    have hbound (tau : ℝ) (htau : tau∈S) :
        ((badPairGraph Pts G w tau (threshold tau) ∪
          (badPairGraph Pts Gt w tau (threshold tau)).image Prod.swap).card : ℝ)≤
            2*B*(Pts.card : ℝ)^2 := by
      have hcard := (Finset.card_union_le
        (badPairGraph Pts G w tau (threshold tau))
        ((badPairGraph Pts Gt w tau (threshold tau)).image Prod.swap)).trans
        (Nat.add_le_add_left Finset.card_image_le _)
      have hcardR : ((badPairGraph Pts G w tau (threshold tau) ∪
          (badPairGraph Pts Gt w tau (threshold tau)).image Prod.swap).card : ℝ)≤
          (badPairGraph Pts G w tau (threshold tau)).card+
          (badPairGraph Pts Gt w tau (threshold tau)).card := by exact_mod_cast hcard
      linarith only [hcardR,hbad tau htau,hbadt tau htau]
    calc
      _ ≤ ∑ tau∈S, ((badPairGraph Pts G w tau (threshold tau) ∪
          (badPairGraph Pts Gt w tau (threshold tau)).image Prod.swap).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : D.card≤_)
      _ ≤ ∑ _tau∈S, 2*B*(Pts.card : ℝ)^2 := Finset.sum_le_sum hbound
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcover : G⊆H∪D := by
    intro z hz
    by_cases hh : ∀ tau∈S,
        ((annularSupport Pts z.1 z.2 w tau).card : ℝ)<threshold tau ∧
        ((annularSupport Pts z.2 z.1 w tau).card : ℝ)<threshold tau
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz,hh⟩))
    · push Not at hh
      obtain ⟨tau,htau,hh⟩ := hh
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨tau,htau,?_⟩
      by_cases hfirst : threshold tau≤((annularSupport Pts z.1 z.2 w tau).card : ℝ)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hGP hz,hz,hfirst⟩))
      · have hsecond := hh (lt_of_not_ge hfirst)
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨z.swap,Finset.mem_filter.mpr ⟨?_,?_,hsecond⟩,Prod.swap_swap z⟩
        · exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hGP hz)).2,
            (Finset.mem_product.mp (hGP hz)).1⟩
        · exact Finset.mem_image_of_mem Prod.swap hz
  have hcard : (G.card : ℝ)≤H.card+D.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le H D)
  refine ⟨Finset.filter_subset _ _,?_,?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · change (G.card : ℝ)≤H.card+_
    dsimp [B] at hD
    nlinarith only [hcard,hD]

end OriginalAnnularGraphDeletion
