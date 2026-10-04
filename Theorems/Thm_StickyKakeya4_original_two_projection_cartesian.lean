import Theorems.Thm_StickyKakeya4_original_separated_packing
import Theorems.Thm_StickyKakeya4_projection_annulus_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalTwoProjectionCartesian
open ProjectionAnnulusEnergy ActualRoundedAdditiveEnergy OriginalSeparatedPacking

def scalarCode (delta lam : ℝ) (p : Point) : ℤ := rounded delta (projection lam p)
def code (delta lam0 lam1 : ℝ) (p : Point) : ℤ × ℤ :=
  (scalarCode delta lam0 p,scalarCode delta lam1 p)
def alphabet (P : Finset Point) (delta lam : ℝ) : Finset ℤ :=
  P.image (scalarCode delta lam)
def graph (P : Finset Point) (delta lam0 lam1 : ℝ) : Finset (ℤ × ℤ) :=
  P.image (code delta lam0 lam1)
def fiberBound (h : ℝ) : ℝ := (6/h+2)^2

lemma same_scalar_code_close {delta lam : ℝ} (hd : 0 < delta) {p q : Point}
    (he : scalarCode delta lam p=scalarCode delta lam q) :
    |projection lam p-projection lam q| ≤ delta := by
  have hp := round_error hd (projection lam p)
  have hq := round_error hd (projection lam q)
  change rounded delta (projection lam p)=rounded delta (projection lam q) at he
  rw [he] at hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two literal transverse projection measurements locate the original point. -/
theorem two_projection_distance {delta h lam0 lam1 : ℝ} {p q : Point}
    (hd : 0 ≤ delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (hlam0 : |lam0| ≤ 1)
    (h0 : |projection lam0 p-projection lam0 q| ≤ delta)
    (h1 : |projection lam1 p-projection lam1 q| ≤ delta) :
    ‖p-q‖ ≤ 3*delta/h := by
  have hid : (lam1-lam0)*(p.2-q.2)=
      (projection lam0 p-projection lam0 q)-(projection lam1 p-projection lam1 q) := by
    dsimp [projection]; ring
  have htri := abs_add_le (projection lam0 p-projection lam0 q)
    (-(projection lam1 p-projection lam1 q))
  simp only [← sub_eq_add_neg,abs_neg] at htri
  rw [← hid,abs_mul] at htri
  have hmul := mul_le_mul_of_nonneg_right htrans (abs_nonneg (p.2-q.2))
  have hy : |p.2-q.2| ≤ 2*delta/h := by
    apply (le_div_iff₀ hh).mpr
    nlinarith only [htri,h0,h1,hmul]
  have hxid : p.1-q.1=(projection lam0 p-projection lam0 q)+lam0*(p.2-q.2) := by
    dsimp [projection]; ring
  have hxtri := abs_add_le (projection lam0 p-projection lam0 q) (lam0*(p.2-q.2))
  rw [← hxid,abs_mul] at hxtri
  have hmx := mul_le_mul_of_nonneg_right hlam0 (abs_nonneg (p.2-q.2))
  have hddiv : delta ≤ delta/h := (le_div_iff₀ hh).mpr (by nlinarith)
  have hx : |p.1-q.1| ≤ 3*delta/h := by
    calc
      _ ≤ delta+|p.2-q.2| := by linarith only [hxtri,hmx,h0]
      _ ≤ delta+2*delta/h := by linarith only [hy]
      _ ≤ delta/h+2*delta/h := by linarith only [hddiv]
      _ = _ := by ring
  have hyd : |p.2-q.2| ≤ 3*delta/h := hy.trans (by gcongr; norm_num)
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,max_le_iff] using
    And.intro hx hyd

/-- Bounded original-point fibers are derived from transversality and native
separation, before any Cartesian graph is selected. -/
theorem original_code_fiber_card (P : Finset Point) {delta h lam0 lam1 : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (hlam0 : |lam0| ≤ 1)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p≠q → delta ≤ ‖p-q‖)
    {z : ℤ × ℤ} (hz : z ∈ graph P delta lam0 lam1) :
    ((P.filter (fun p => code delta lam0 lam1 p=z)).card : ℝ) ≤ fiberBound h := by
  obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
  have hsub : P.filter (fun q => code delta lam0 lam1 q=z) ⊆
      P.filter (fun q => ‖q-p‖ ≤ 3*delta/h) := by
    intro q hq
    obtain ⟨hqP,hqz⟩ := Finset.mem_filter.mp hq
    have he : code delta lam0 lam1 q=code delta lam0 lam1 p := hqz.trans hpz.symm
    refine Finset.mem_filter.mpr ⟨hqP,?_⟩
    exact two_projection_distance hd.le hh hh1 htrans hlam0
      (same_scalar_code_close hd (congrArg Prod.fst he))
      (same_scalar_code_close hd (congrArg Prod.snd he))
  have hbound := planar_ball_card P hd (show 0 ≤ 3*delta/h by positivity) hsep p
  have he : (2*((3*delta/h)/delta)+2)^2=fiberBound h := by
    dsimp [fiberBound]
    field_simp
    ring
  rw [he] at hbound
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hbound

theorem graph_subset_product (P : Finset Point) (delta lam0 lam1 : ℝ) :
    graph P delta lam0 lam1 ⊆ (alphabet P delta lam0).product (alphabet P delta lam1) := by
  rintro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩

/-- Every quotient edge has a literal original source witness. -/
theorem original_graph_witness (P : Finset Point) (delta lam0 lam1 : ℝ)
    {z : ℤ × ℤ} (hz : z ∈ graph P delta lam0 lam1) :
    ∃ p ∈ P, scalarCode delta lam0 p=z.1 ∧ scalarCode delta lam1 p=z.2 := by
  obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
  exact ⟨p,hp,congrArg Prod.fst hpz,congrArg Prod.snd hpz⟩

/-- This same quantitative quotient bound holds for every original query. -/
theorem original_query_graph_mass (P : Finset Point) {delta h lam0 lam1 : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (hlam0 : |lam0| ≤ 1)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p≠q → delta ≤ ‖p-q‖)
    (Q : Finset Point) (hQ : Q ⊆ P) :
    (Q.card : ℝ) ≤ fiberBound h*(graph Q delta lam0 lam1).card := by
  apply card_le_real_mul_image Q (code delta lam0 lam1)
  intro z hz
  exact original_code_fiber_card Q hd hh hh1 htrans hlam0
    (fun p hp q hq hpq => hsep p (hQ hp) q (hQ hq) hpq) hz

/-- Two actual small projection images produce a dense Cartesian graph and
two large alphabets. All bounds refer to the original point population. -/
theorem small_projections_cartesian_density (P : Finset Point) {delta h lam0 lam1 K : ℝ}
    (hP : P.Nonempty) (hd : 0 < delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (hlam0 : |lam0| ≤ 1) (hK : 0 < K)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p≠q → delta ≤ ‖p-q‖)
    (hA : ((alphabet P delta lam0).card : ℝ) ≤ K*Real.sqrt P.card)
    (hB : ((alphabet P delta lam1).card : ℝ) ≤ K*Real.sqrt P.card) :
    ((alphabet P delta lam0).card : ℝ)*(alphabet P delta lam1).card ≤
      fiberBound h*K^2*(graph P delta lam0 lam1).card ∧
    Real.sqrt P.card ≤ fiberBound h*K*(alphabet P delta lam0).card ∧
    Real.sqrt P.card ≤ fiberBound h*K*(alphabet P delta lam1).card := by
  have hmass := original_query_graph_mass P hd hh hh1 htrans hlam0 hsep P (Finset.Subset.refl P)
  have hprod : ((graph P delta lam0 lam1).card : ℝ) ≤
      (alphabet P delta lam0).card*(alphabet P delta lam1).card := by
    have hc := Finset.card_le_card (graph_subset_product P delta lam0 lam1)
    rw [Finset.product_eq_sprod,Finset.card_product] at hc
    exact_mod_cast hc
  have hD : 0 ≤ fiberBound h := sq_nonneg _
  have hA0 : (0 : ℝ) ≤ (alphabet P delta lam0).card := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (alphabet P delta lam1).card := Nat.cast_nonneg _
  have hN : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hs : 0 < Real.sqrt P.card := Real.sqrt_pos.2 hN
  have hsq : (Real.sqrt P.card)^2=(P.card : ℝ) := Real.sq_sqrt hN.le
  have hab := mul_le_mul hA hB hB0 (by positivity : 0 ≤ K*Real.sqrt P.card)
  have hmain : (P.card : ℝ) ≤ fiberBound h*((alphabet P delta lam0).card*(alphabet P delta lam1).card) :=
    hmass.trans (mul_le_mul_of_nonneg_left hprod hD)
  constructor
  · have hhK := mul_le_mul_of_nonneg_left hmass (sq_nonneg K)
    nlinarith only [hab,hsq,hhK]
  constructor
  · have hb := mul_le_mul_of_nonneg_left hB (mul_nonneg hD hA0)
    nlinarith only [hb,hmain,hsq,hs]
  · have ha := mul_le_mul_of_nonneg_left hA (mul_nonneg hD hB0)
    nlinarith only [ha,hmain,hsq,hs]

def leftWeight (lam0 lam1 lam : ℝ) : ℝ := (lam1-lam)/(lam1-lam0)
def rightWeight (lam0 lam1 lam : ℝ) : ℝ := (lam-lam0)/(lam1-lam0)
def syntheticProjection (delta lam0 lam1 lam : ℝ) (z : ℤ × ℤ) : ℝ :=
  leftWeight lam0 lam1 lam*(delta*(z.1 : ℝ))+
    rightWeight lam0 lam1 lam*(delta*(z.2 : ℝ))

lemma projection_linear_identity (lam0 lam1 lam : ℝ) (hneq : lam1≠lam0) (p : Point) :
    projection lam p=leftWeight lam0 lam1 lam*projection lam0 p+
      rightWeight lam0 lam1 lam*projection lam1 p := by
  dsimp [projection,leftWeight,rightWeight]
  field_simp
  ring

/-- The quotient graph preserves every third actual projection with a proved
floor error. The original witness is unchanged. -/
theorem synthetic_projection_error {delta lam0 lam1 lam : ℝ}
    (hd : 0 < delta) (hneq : lam1≠lam0) (p : Point) :
    |projection lam p-syntheticProjection delta lam0 lam1 lam (code delta lam0 lam1 p)| ≤
      delta*(|leftWeight lam0 lam1 lam|+|rightWeight lam0 lam1 lam|) := by
  have h0 := round_error hd (projection lam0 p)
  have h1 := round_error hd (projection lam1 p)
  have e0 : |projection lam0 p-delta*(scalarCode delta lam0 p : ℝ)| ≤ delta :=
    abs_le.mpr ⟨by simpa only [scalarCode] using (show -delta ≤
      projection lam0 p-delta*(rounded delta (projection lam0 p) : ℝ) by linarith), h0.2.le⟩
  have e1 : |projection lam1 p-delta*(scalarCode delta lam1 p : ℝ)| ≤ delta :=
    abs_le.mpr ⟨by simpa only [scalarCode] using (show -delta ≤
      projection lam1 p-delta*(rounded delta (projection lam1 p) : ℝ) by linarith), h1.2.le⟩
  have hid : projection lam p-syntheticProjection delta lam0 lam1 lam (code delta lam0 lam1 p)=
      leftWeight lam0 lam1 lam*(projection lam0 p-delta*(scalarCode delta lam0 p : ℝ))+
      rightWeight lam0 lam1 lam*(projection lam1 p-delta*(scalarCode delta lam1 p : ℝ)) := by
    rw [projection_linear_identity lam0 lam1 lam hneq p]
    dsimp [syntheticProjection,code]
    ring
  rw [hid]
  have ht := abs_add_le
    (leftWeight lam0 lam1 lam*(projection lam0 p-delta*(scalarCode delta lam0 p : ℝ)))
    (rightWeight lam0 lam1 lam*(projection lam1 p-delta*(scalarCode delta lam1 p : ℝ)))
  rw [abs_mul,abs_mul] at ht
  have hmul0 := mul_le_mul_of_nonneg_left e0 (abs_nonneg (leftWeight lam0 lam1 lam))
  have hmul1 := mul_le_mul_of_nonneg_left e1 (abs_nonneg (rightWeight lam0 lam1 lam))
  nlinarith only [ht,hmul0,hmul1]

end OriginalTwoProjectionCartesian
