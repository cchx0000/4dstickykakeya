import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeDenseOriginalParent
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalParentPhysicalData
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open scoped BigOperators

/-- A finite original class is selected with both half-average density and
large original mass. No regularity profile is inserted as an assumption. -/
theorem exists_mass_and_density {A : Type*} (P : Finset A) (m w : A → ℝ)
    (hm : ∀ p∈P, 0≤ m p) (hw : ∀ p∈P, 0≤w p)
    (hS : 0<∑p∈P,m p) (hW : 0<∑p∈P,w p) :
    ∃ p∈P, 0< m p ∧ (∑q∈P,m q)≤2*(P.card:ℝ)*m p ∧
      (∑q∈P,m q)*w p≤2*(∑q∈P,w q)*m p := by
  let S := ∑p∈P,m p
  let W := ∑p∈P,w p
  have hWp : 0 < W := hW
  have hSp : 0 < S := hS
  let good := P.filter fun p=>S*w p≤2*W*m p
  have hpoint (p : A) (hp : p∈P) :
      m p ≤ (if p∈good then m p else 0) + (S/(2*W))*w p := by
    by_cases hg : p∈good
    · rw [if_pos hg]
      have hh : 0≤S/(2*W)*w p := mul_nonneg (by positivity) (hw p hp)
      linarith
    · rw [if_neg hg, zero_add]
      have hb : ¬S*w p≤2*W*m p := by
        intro hh
        exact hg (mem_filter.mpr ⟨hp,hh⟩)
      apply (mul_le_mul_iff_right₀ (show 0<2*W by positivity)).mp
      have he : (S/(2*W)*w p)*(2*W)=S*w p := by field_simp [hWp.ne']
      nlinarith only [he, le_of_not_ge hb]
  have hsum : S≤(∑p∈good,m p)+S/2 := by
    have hh := sum_le_sum hpoint
    have hid : (∑p∈P, if p∈good then m p else 0)=∑p∈good,m p := by
      rw [← sum_filter]
      congr 1
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp=> (mem_filter.mp hp).1)
    have hid2 : (∑p∈P,S/(2*W)*w p)=S/2 := by
      rw [← mul_sum]
      change S/(2*W)*W=S/2
      field_simp [hWp.ne']
    rw [sum_add_distrib, hid, hid2] at hh
    exact hh
  have hgood : good.Nonempty := by
    by_contra hn
    have he : good=∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,sum_empty] at hsum
    dsimp [S] at hsum
    linarith
  obtain ⟨p,hp,hmax⟩ := exists_max_image good m hgood
  have hpP := (mem_filter.mp hp).1
  have hmax0 := hm p hpP
  have hmaxsum : (∑q∈good,m q)≤(P.card:ℝ)*m p := by
    calc
      _ ≤ ∑_q∈good,m p := sum_le_sum hmax
      _ = (good.card:ℝ)*m p := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ _)) hmax0
  have hmp : 0< m p := by
    by_contra hn
    have hzero : m p=0 := le_antisymm (le_of_not_gt hn) hmax0
    rw [hzero,mul_zero] at hmaxsum
    dsimp [S] at hsum
    linarith
  exact ⟨p,hpP,hmp,by dsimp [S] at hsum; linarith,(mem_filter.mp hp).2⟩

lemma sum_parentIncidences {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) :
    ∑p∈parents D a N,(parentIncidences D cells a N p).card=(incidences cells).card := by
  symm
  exact card_eq_sum_card_fiberwise (fun z _hz => mem_image_of_mem _ (mem_univ z.1))

lemma sum_backbones {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) :
    ∑p∈parents D a N,(backbone D a N p).card=n := by
  have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := parents D a N) (f := parentLabel D a N) (fun i _hi=>mem_image_of_mem _ (mem_univ i))
  simpa only [card_univ,Fintype.card_fin,backbone] using hh.symm

/-- The same actual original parent has large mass and preserves half the
original average number of shading cells per original tube. -/
theorem exists_dense_parent {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ)
    (hn : 0<n) (hne : (incidences cells).Nonempty) :
    ∃ p∈parents D a N, (parentIncidences D cells a N p).Nonempty ∧
      (incidences cells).card≤2*(parents D a N).card*(data D cells a N p).incidences.card ∧
      (incidences cells).card*(backbone D a N p).card≤2*n*(data D cells a N p).incidences.card := by
  have hsumM : (∑p∈parents D a N,((parentIncidences D cells a N p).card:ℝ))=
      (incidences cells).card := by exact_mod_cast sum_parentIncidences D cells a N
  have hsumW : (∑p∈parents D a N,((backbone D a N p).card:ℝ))=n := by
    exact_mod_cast sum_backbones D a N
  obtain ⟨p,hp,hm,hret,hden⟩ := exists_mass_and_density (parents D a N)
    (fun p=>(parentIncidences D cells a N p).card) (fun p=>(backbone D a N p).card)
    (fun _ _=>by positivity) (fun _ _=>by positivity)
    (by rw [hsumM]; exact_mod_cast card_pos.mpr hne) (by rw [hsumW]; exact_mod_cast hn)
  rw [hsumM] at hret hden
  rw [hsumW] at hden
  refine ⟨p,hp,card_pos.mp (by exact_mod_cast hm),?_,?_⟩
  · change (incidences cells).card≤2*(parents D a N).card*(chartIncidences D cells a N p).card
    rw [chartIncidences_card]
    exact_mod_cast hret
  · change (incidences cells).card*(backbone D a N p).card≤2*n*(chartIncidences D cells a N p).card
    rw [chartIncidences_card]
    exact_mod_cast hden

end NativeDenseOriginalParent
