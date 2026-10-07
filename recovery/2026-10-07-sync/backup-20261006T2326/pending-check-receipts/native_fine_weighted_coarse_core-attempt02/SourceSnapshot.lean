import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning
import Theorems.Thm_StickyKakeya4_native_coarse_native_admissibility

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFineWeightedCoarseCore
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCoarseDirectionThinning NativeCoarsePruningBudget
open NativeDyadicParentCells NativeCoarseCellSource NativeCoarseShadingPruning
open NativeCoarsePowerWindow NativeCoarseRelativeCW NativeUnitParentNormalization
open scoped BigOperators ENNReal

/-- The fixed-height fine-pair capacity supplied by the source geometry. -/
def fineCapacity : ℝ := 130^3*5832*66^3
def colorCost : ℝ := 23328*512^3
def pruneCost : ℝ := 746496*(18*fineCapacity)*64^3

lemma fineCapacity_pos : 0 < fineCapacity := by norm_num [fineCapacity]
lemma colorCost_pos : 0 < colorCost := by norm_num [colorCost]
lemma pruneCost_pos : 0 < pruneCost := by norm_num [pruneCost,fineCapacity]

/-- The coloring loss is charged at the original thickness. The lower
normalized total and one extra power give a positive normalized color. -/
lemma color_weight_retention {r p z eps total chosen : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hpz : p ≤ z) (heps : 0 < eps)
    (htotal : r^z ≤ eps^4*total)
    (hcolor : total ≤ (colorCost*r^(-p))*chosen)
    (hsmall : colorCost*r^z ≤ 1) :
    r^p/colorCost*total ≤ chosen ∧ r^(3*z) ≤ eps^4*chosen := by
  have hc := colorCost_pos
  have hret' : r^p*total ≤ colorCost*chosen := by
    have hh := mul_le_mul_of_nonneg_left hcolor (Real.rpow_pos_of_pos hr p).le
    have he : r^p*((colorCost*r^(-p))*chosen)=colorCost*chosen := by
      rw [Real.rpow_neg hr.le]
      field_simp [(Real.rpow_pos_of_pos hr p).ne']
    rwa [he] at hh
  have hret : r^p/colorCost*total ≤ chosen := by
    have hh : (r^p*total)/colorCost ≤ chosen :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hret')
    convert hh using 1 <;> ring
  have hbase : r^(3*z) ≤ r^p/colorCost*r^z := by
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      colorCost*r^(3*z) = (colorCost*r^z)*r^(2*z) := by
        rw [mul_assoc,←Real.rpow_add hr]
        congr 2
        ring
      _ ≤ 1*r^(2*z) := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hr _).le
      _ = r^(2*z) := one_mul _
      _ ≤ r^(p+z) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
      _ = colorCost*(r^p/colorCost*r^z) := by
        rw [Real.rpow_add hr]
        field_simp [hc.ne']
  refine ⟨hret,hbase.trans ?_⟩
  calc
    r^p/colorCost*r^z ≤ r^p/colorCost*(eps^4*total) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = eps^4*(r^p/colorCost*total) := by ring
    _ ≤ eps^4*chosen := mul_le_mul_of_nonneg_left hret (by positivity)

/-- Pruning fine-pair weights at threshold r^(8z) loses at most half the
same color. The eps^-4 normalization has already canceled from the ledger. -/
lemma pruned_weight_retention {r p z eps chosen kept : ℝ} (b : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hpz : p ≤ z) (heps : 0 < eps)
    (hcolor : r^(3*z) ≤ eps^4*chosen)
    (hprune : eps^4*chosen ≤ eps^4*kept+pruneCost*((b:ℝ)+1)*r^(8*z-2*p))
    (hsmall : 2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 1) :
    chosen ≤ 2*kept ∧ r^(3*z)/2 ≤ eps^4*kept := by
  have hc := pruneCost_pos
  have hcost : 2*(pruneCost*((b:ℝ)+1)*r^(8*z-2*p)) ≤ r^(3*z) := by
    calc
      _ ≤ 2*(pruneCost*((b:ℝ)+1)*r^(6*z)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) (by positivity)
      _ = (2*pruneCost*((b:ℝ)+1)*r^(3*z))*r^(3*z) := by
        rw [show 6*z=3*z+3*z by ring,Real.rpow_add hr]
        ring
      _ ≤ 1*r^(3*z) := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hr _).le
      _ = _ := one_mul _
  have hhalf : eps^4*chosen ≤ eps^4*(2*kept) := by nlinarith only [hcolor,hprune,hcost]
  exact ⟨(mul_le_mul_iff_right₀ (show 0 < eps^4 by positivity)).mp hhalf,
    by linarith only [hcolor,hprune,hcost]⟩

/-- The fine-pair cap cancels the cubic parent count and the old mesh
normalization, leaving only the original-thickness power and depth. -/
lemma normalized_pruning_charge {r p z eps : ℝ} (b : ℕ)
    (hr : 0 < r) (heps : 0 < eps) :
    eps^4*(746496*(18*fineCapacity*r^(-p)*(64/((2^b:ℕ):ℝ))^3/eps^4)*
      ((b:ℝ)+1)*r^(8*z-p)*((2^b:ℕ):ℝ)^3) =
      pruneCost*((b:ℝ)+1)*r^(8*z-2*p) := by
  have hN : (0:ℝ) < ((2^b:ℕ):ℝ) := by positivity
  calc
    _ = pruneCost*((b:ℝ)+1)*(r^(-p)*r^(8*z-p)) := by
      unfold pruneCost
      field_simp [heps.ne',hN.ne']
    _ = _ := by
      rw [←Real.rpow_add hr]
      congr 2
      ring

/-- One color, then one pruning of that color, produces the literal final Q.
Weights may be the actual current fine configured-pair counts. All occupancy
premises concern original labels, and no native output is assumed. -/
theorem same_Q_selection {n : ℕ} {D : FiniteScaleSource n} {eta a p z eps : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hp : 0 ≤ p) (hpz : p ≤ z)
    (heps : 0 < eps) (R : Finset (Fin n)) (b : ℕ)
    (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (H : ∀ell : Fin (b+1),∀q : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=q)).Nonempty →
        D.thickness^p*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=q)).card:ℝ))
    (W : Parent → ℝ)
    (hW : ∀q∈R.image (parentLabel D a (2^b)),0 ≤ W q)
    (hU : ∀q∈R.image (parentLabel D a (2^b)),
      W q ≤ 18*fineCapacity*D.thickness^(-p)*(64/((2^b:ℕ):ℝ))^3/eps^4)
    (htotal : D.thickness^z ≤ eps^4*(∑q∈R.image (parentLabel D a (2^b)),W q))
    (hcolorCost : colorCost*D.thickness^z ≤ 1)
    (hpruneCost : 2*pruneCost*((b:ℝ)+1)*D.thickness^(3*z) ≤ 1) :
    ∃Q : Finset Parent,Q⊆R.image (parentLabel D a (2^b)) ∧ Q.Nonempty ∧
      (∀q∈Q,representative h R a (2^b) q∈R ∧
        parentLabel D a (2^b) (representative h R a (2^b) q)=q) ∧
      (∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
        dist (direction (D.line (representative h R a (2^b) q)))
          (direction (D.line (representative h R a (2^b) q')))) ∧
      D.thickness^p/(2*colorCost)*(∑q∈R.image (parentLabel D a (2^b)),W q) ≤ ∑q∈Q,W q ∧
      D.thickness^(3*z)/2 ≤ eps^4*(∑q∈Q,W q) ∧
      D.thickness^(3*z)/(2*eps^4) ≤ ∑q∈Q,W q ∧
      (∀ell : Fin (b+1),∀q : Parent,
        (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
          D.thickness^(8*z)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
            ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ)) := by
  have hr := h.1.2.1
  let P := R.image (parentLabel D a (2^b))
  have htotalpos : 0 < ∑q∈P,W q := by
    exact (mul_pos_iff_of_pos_left (show 0 < eps^4 by positivity)).mp
      ((Real.rpow_pos_of_pos hr z).trans_le htotal)
  have hP : P.Nonempty := by
    by_contra hn
    simp only [not_nonempty_iff_eq_empty.mp hn,sum_empty,lt_self_iff_false] at htotalpos
  have hTube : 0 < ∑_q∈P,(1:ℝ) := by
    simpa using (show (0:ℝ) < P.card by exact_mod_cast card_pos.mpr hP)
  obtain ⟨C,hCP,_hC,_hCpos,_hCrep,hCsep,hCret,_hCden⟩ :=
    exists_dense_direction_thinning h hp R (2^b) (by positivity) hscale
      (H ⟨b,by omega⟩) W (fun _ => 1) hW (fun _ _ => by norm_num) htotalpos hTube
  have hcolor := color_weight_retention hr h.1.2.2.1 hpz heps htotal hCret hcolorCost
  let U := 18*fineCapacity*D.thickness^(-p)*(64/((2^b:ℕ):ℝ))^3/eps^4
  have hU0 : 0 ≤ U := by
    have hc := fineCapacity_pos
    dsimp [U]
    positivity
  obtain ⟨Q,hQC,hQret,hterminal⟩ := weighted_pruning_power_budget (t:=8*z)
    h R b H C hCP W hU0 (fun q hq => hU q (hCP hq))
  have hnormalized : eps^4*(∑q∈C,W q) ≤ eps^4*(∑q∈Q,W q)+
      pruneCost*((b:ℝ)+1)*D.thickness^(8*z-2*p) := by
    have hh := mul_le_mul_of_nonneg_left hQret (show 0 ≤ eps^4 by positivity)
    rw [mul_add] at hh
    simpa only [U,normalized_pruning_charge b hr heps] using hh
  have hkept := pruned_weight_retention b hr h.1.2.2.1 hpz heps hcolor.2 hnormalized hpruneCost
  have hQP : Q⊆P := hQC.trans hCP
  have hQne : Q.Nonempty := by
    by_contra hn
    have hh := hkept.2
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty,mul_zero] at hh
    exact (not_le_of_gt (div_pos (Real.rpow_pos_of_pos hr _) (by norm_num))) hh
  refine ⟨Q,hQP,hQne,fun q hq => representative_spec h R a (2^b) (hQP hq),
    fun q hq q' hq' hne => hCsep q (hQC hq) q' (hQC hq') hne,?_,hkept.2,?_,hterminal⟩
  · have hh := hcolor.1.trans hkept.1
    calc
      _ = (D.thickness^p/colorCost*(∑q∈P,W q))/2 := by ring
      _ ≤ ∑q∈Q,W q := (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by simpa only [mul_comm] using hh)
  · apply (div_le_iff₀ (show 0 < 2*eps^4 by positivity)).mpr
    nlinarith only [hkept.2]

/-- The geometric bridge is used on the SAME Q. Its constant records the
fixed-height fine-pair capacity, at most 34d/eps old heights, and (d/2)^4
actual cell volume. The source geometry must supply the bridge separately. -/
lemma actual_shading_from_fine_weights {r p z eps kept shade : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hpz : p ≤ z)
    (hkept : r^(3*z)/2 ≤ eps^4*kept)
    (hbridge : r^p*eps^4*kept/(544*fineCapacity) ≤ shade)
    (hsmall : 1088*fineCapacity*r^z ≤ 1) : r^(5*z) ≤ shade := by
  have hCf := fineCapacity_pos
  have hbase : r^(5*z) ≤ r^(4*z)/(1088*fineCapacity) := by
    apply (le_div_iff₀ (show 0 < 1088*fineCapacity by positivity)).mpr
    calc
      _ = (1088*fineCapacity*r^z)*r^(4*z) := by
        rw [show 5*z=z+4*z by ring,Real.rpow_add hr]
        ring
      _ ≤ 1*r^(4*z) := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hr _).le
      _ = _ := one_mul _
  calc
    r^(5*z) ≤ r^(4*z)/(1088*fineCapacity) := hbase
    _ ≤ r^(p+3*z)/(1088*fineCapacity) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) (by positivity)
    _ = (r^p/(544*fineCapacity))*(r^(3*z)/2) := by rw [Real.rpow_add hr]; ring
    _ ≤ (r^p/(544*fineCapacity))*(eps^4*kept) :=
      mul_le_mul_of_nonneg_left hkept (by positivity)
    _ = r^p*eps^4*kept/(544*fineCapacity) := by ring
    _ ≤ shade := hbridge

/-- An intermediate original-E admission operator. The universally quantified
geometric inequality must be proved from actual configured-pair source geometry
before this theorem can be applied to the final source. Neither output native
admissibility nor output shading mass is a premise. -/
theorem same_Q_native_input {n : ℕ} {D : FiniteScaleSource n} {eta a p z eps e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (hp : 0 ≤ p) (hpz : p ≤ z) (heps : 0 < eps)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hb : b ≤ level) (h6 : 6 ≤ b) (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : ∀x∈E,x.2∈original x.1)
    (H : ∀ell : Fin (b+1),∀q : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=q)).Nonempty →
        D.thickness^p*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=q)).card:ℝ))
    (W : Parent → ℝ)
    (hW : ∀q∈R.image (parentLabel D a (2^b)),0 ≤ W q)
    (hU : ∀q∈R.image (parentLabel D a (2^b)),
      W q ≤ 18*fineCapacity*D.thickness^(-p)*(64/((2^b:ℕ):ℝ))^3/eps^4)
    (htotal : D.thickness^z ≤ eps^4*(∑q∈R.image (parentLabel D a (2^b)),W q))
    (hcolorCost : colorCost*D.thickness^z ≤ 1)
    (hpruneCost : 2*pruneCost*((b:ℝ)+1)*D.thickness^(3*z) ≤ 1)
    (hbridge : ∀Q : Finset Parent,Q⊆R.image (parentLabel D a (2^b)) →
      D.thickness^p*eps^4*(∑q∈Q,W q)/(544*fineCapacity) ≤
        ∑q∈Q,weight D a level b (representative h R a (2^b)) E q)
    (hshadeCost : 1088*fineCapacity*D.thickness^z ≤ 1)
    (hpower : (64/((2^b:ℕ):ℝ))^e ≤ D.thickness^(8*z))
    (hupper : 10077696*D.thickness^(8*z) ≤ 1)
    (hdensity : densityCost*D.thickness^z ≤ 1)
    (hcw : cwCost*D.thickness^(2*z-eta) ≤ 1) :
    let rep := representative h R a (2^b)
    ∃ (Q : Finset Parent)
      (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
        dist (direction (D.line (rep q))) (direction (D.line (rep q')))),
      Q⊆R.image (parentLabel D a (2^b)) ∧ Q.Nonempty ∧
      (∀q∈Q,rep q∈R ∧ parentLabel D a (2^b) (rep q)=q) ∧
      D.thickness^p/(2*colorCost)*(∑q∈R.image (parentLabel D a (2^b)),W q) ≤ ∑q∈Q,W q ∧
      D.thickness^(3*z)/2 ≤ eps^4*(∑q∈Q,W q) ∧
      D.thickness^(5*z) ≤ (wzTotalShadingVolume (source h a level b Q rep E hsep)).toReal ∧
      IsWangZakharovNativeFiniteInput (source h a level b Q rep E hsep) e := by
  let rep := representative h R a (2^b)
  obtain ⟨Q,hQP,hQne,hrep,hsep,hret,hnorm,_hbare,hterminal⟩ :=
    same_Q_selection h hp hpz heps R b hscale H W hW hU htotal hcolorCost hpruneCost
  have hz : 0 ≤ z := hp.trans hpz
  have hshade : D.thickness^(5*z) ≤ ∑q∈Q,weight D a level b rep E q :=
    actual_shading_from_fine_weights h.1.2.1 h.1.2.2.1 hpz hnorm (hbridge Q hQP) hshadeCost
  have Horiginal : ∀q : Parent,(R.filter (fun i => parentLabel D a (2^b) i=q)).Nonempty →
      D.thickness^z*((1/((2^b:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^b) i=q)).card:ℝ) := by
    intro q hq
    have hratio : 0 ≤ ((1/((2^b:ℕ):ℝ))/D.thickness)^3 :=
      pow_nonneg (div_nonneg (by positivity) h.1.2.1.le) 3
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 hpz) hratio).trans
      (H ⟨b,by omega⟩ q hq)
  refine ⟨Q,hsep,hQP,hQne,hrep,hret,hnorm,?_,?_⟩
  · rwa [NativeCoarseSourceMass.source_total_shading_real]
  · exact NativeCoarseNativeAdmissibility.native_input h hK hz original horiginal ha R level b hdy hb h6
      hscale Q hQP hQne rep (fun q hq => (hrep q hq).2) E hE hsep Horiginal hterminal hshade
      hpower hupper hdensity (by simpa only [show 8*z-(eta+6*z)=2*z-eta by ring] using hcw)

end NativeFineWeightedCoarseCore
