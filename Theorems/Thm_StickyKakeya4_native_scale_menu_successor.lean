import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu
import Theorems.Thm_StickyKakeya4_native_local_menu_interpolation
import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeScaleMenuSuccessor
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeFixedSizeScaleMenu NativeOriginalParentDensityCore NativeDyadicParentCells
open NativeIncidenceMultiplicityTower NativeLocalMenuInterpolation
open scoped BigOperators

/-- A successor of the raw fixed menu has a gap at most level/g, without
the extra rounding allowance needed for the predecessor estimate. -/
theorem exists_successor (g level m : ℕ) (hg : 0 < g)
    (hlevel : 0 < level) (hm : m ≤ level) :
    ∃ j : Fin (g+1), m ≤ (schedule g level j).val ∧
      (schedule g level j).val-m ≤ level/g ∧
      (((schedule g level j).val-m:ℕ):ℝ) ≤ (level:ℝ)/g := by
  by_cases he : m=level
  · subst m
    refine ⟨Fin.last g,?_,?_,?_⟩
    · simpa only [schedule_last g level hg] using (le_rfl : level ≤ level)
    · simpa only [schedule_last g level hg,Nat.sub_self] using (Nat.zero_le (level/g))
    · simpa only [schedule_last g level hg,Nat.sub_self,Nat.cast_zero] using
        (div_nonneg (Nat.cast_nonneg level) (Nat.cast_nonneg g) : (0:ℝ) ≤ (level:ℝ)/g)
  · have hml : m < level := by omega
    let q : ℕ := m*g/level
    have hq : q < g := (Nat.div_lt_iff_lt_mul hlevel).mpr (by nlinarith)
    let j : Fin (g+1) := ⟨q+1,by omega⟩
    let d : ℕ := (q+1)*level/g
    have hqlo : q*level ≤ m*g := Nat.div_mul_le_self (m*g) level
    have hqhi : m*g < level*(q+1) := Nat.lt_mul_div_succ (m*g) hlevel
    have hdlo : d*g ≤ (q+1)*level := Nat.div_mul_le_self ((q+1)*level) g
    have hmd : m ≤ d := (Nat.le_div_iff_mul_le hg).mpr (by nlinarith)
    have hsub : d-m+m=d := Nat.sub_add_cancel hmd
    have hdiff : (d-m)*g ≤ level := by nlinarith
    have hgap : d-m ≤ level/g := (Nat.le_div_iff_mul_le hg).mpr hdiff
    have hgr : (0:ℝ) < g := by exact_mod_cast hg
    have hdiffR : ((d-m:ℕ):ℝ)*(g:ℝ) ≤ level := by exact_mod_cast hdiff
    exact ⟨j,hmd,hgap,(le_div_iff₀ hgr).mpr hdiffR⟩

/-- Clipping a raw successor toward an interval containing m preserves
successorship and only decreases its gap. -/
theorem exists_clipped_successor (g level lo hi m : ℕ) (hg : 0 < g)
    (hlevel : 0 < level) (hhi : hi ≤ level) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    ∃ j : Fin (g+1), m ≤ (clippedSchedule g level lo hi hhi j).val ∧
      (clippedSchedule g level lo hi hhi j).val-m ≤ level/g ∧
      (((clippedSchedule g level lo hi hhi j).val-m:ℕ):ℝ) ≤ (level:ℝ)/g := by
  obtain ⟨j,hmd,hgap,hgapR⟩ := exists_successor g level m hg hlevel (hmhi.trans hhi)
  have hlo : lo ≤ (schedule g level j).val := hlom.trans hmd
  have he : (clippedSchedule g level lo hi hhi j).val = min hi (schedule g level j).val := by
    simp only [clippedSchedule,max_eq_right hlo]
  have hmd' : m ≤ (clippedSchedule g level lo hi hhi j).val := by
    rw [he]
    exact le_min hmhi hmd
  have hdd' : (clippedSchedule g level lo hi hhi j).val ≤ (schedule g level j).val := by
    rw [he]
    exact min_le_right _ _
  have hsub : (clippedSchedule g level lo hi hhi j).val-m ≤ (schedule g level j).val-m := by omega
  exact ⟨j,hmd',hsub.trans hgap,(show (((clippedSchedule g level lo hi hhi j).val-m:ℕ):ℝ) ≤
    (((schedule g level j).val-m:ℕ):ℝ) by exact_mod_cast hsub).trans hgapR⟩

/-- The same clipped finite schedule supplies a successor for every target
depth in the middle window. Its fractional gap is exactly 1/g. -/
theorem exists_window_successor (w : ℝ) (hw : 0 < w) (_hwsmall : w < 1/2)
    (g level m : ℕ) (hg : 0 < g) (hlarge : 4 ≤ w*(level:ℝ))
    (hlo : w*(level:ℝ) ≤ m) (hhi : (m:ℝ) ≤ (1-w)*(level:ℝ)) :
    ∃ j : Fin (g+1), m ≤ (windowSchedule w hw.le g level j).val ∧
      (windowSchedule w hw.le g level j).val-m ≤ level/g ∧
      (((windowSchedule w hw.le g level j).val-m:ℕ):ℝ) ≤
        (1/(g:ℝ))*(level:ℝ) := by
  have hlpos : 0 < level := by
    by_contra hnot
    have he : level=0 := by omega
    simp only [he,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hlom : lowerDepth w level ≤ m := Nat.ceil_le.mpr (by nlinarith)
  have hmhi : m ≤ upperDepth w level := Nat.le_floor (by nlinarith)
  obtain ⟨j,hmd,hgap,hgapR⟩ := exists_clipped_successor g level (lowerDepth w level)
    (upperDepth w level) m hg hlpos (upperDepth_le w hw.le level) hlom hmhi
  refine ⟨j,hmd,hgap,?_⟩
  rw [show (1/(g:ℝ))*(level:ℝ)=(level:ℝ)/g by ring]
  exact hgapR

/-- A common lower bound for all conditional old-incidence multiplicities
survives their union. The child supports may overlap arbitrarily. -/
theorem partition_multiplicity_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) (L : ℝ) (hL : 0 ≤ L) (hne : I.Nonempty)
    (H : ∀ p ∈ I.image (fun z => f z.1), L ≤ multiplicity (parent I f p)) :
    L ≤ multiplicity I := by
  have hc : ((coarse I f).card:ℝ) =
      ∑p∈I.image (fun z => f z.1),(((parent I f p).image Prod.snd).card:ℝ) := by
    exact_mod_cast coarse_card_sum I f
  have hf : (I.card:ℝ) = ∑p∈I.image (fun z => f z.1),((parent I f p).card:ℝ) := by
    exact_mod_cast fine_card_sum I f
  have hcount : L*((coarse I f).card:ℝ) ≤ I.card := by
    rw [hc,hf,mul_sum]
    apply sum_le_sum
    intro p hp
    have hs : (0:ℝ) < ((parent I f p).image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((parent_nonempty I f hp).image Prod.snd)
    exact (le_div_iff₀ hs).mp (H p hp)
  have hsupport : ((I.image Prod.snd).card:ℝ) ≤ (coarse I f).card := by
    rw [←coarse_support I f]
    exact_mod_cast (card_image_le (s:=coarse I f) (f:=Prod.snd))
  have hs : (0:ℝ) < (I.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  exact (le_div_iff₀ hs).mpr ((mul_le_mul_of_nonneg_left hsupport hL).trans hcount)

/-- Every occupied finer child inside an original parent is its complete
literal E-fiber, by exact dyadic ancestor nesting. -/
lemma nested_parentEdges_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) {coarse fine : ℕ} (hcf : coarse ≤ fine) (p q : Parent)
    (hne : (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q).Nonempty) :
    parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q =
      parentEdges D a (2^fine) E q := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨hzp,hzq⟩ := mem_filter.mp hz
  have hqp : ancestor fine coarse q=p := by
    rw [←hzq,parent_ancestor_eq D a hcf z.1]
    exact (mem_filter.mp hzp).2
  ext y
  constructor
  · intro hy
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩
  · intro hy
    obtain ⟨hyE,hyq⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hyE,?_⟩,hyq⟩
    rw [←parent_ancestor_eq D a hcf y.1,hyq,hqp]

/-- An off-menu parent inherits a lower old-incidence multiplicity bound
from all of its active finer menu children. E and every fine cell stay fixed. -/
theorem off_menu_parent_lower {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E : Finset (Fin n × Index)) {coarse fine : ℕ} (hcf : coarse ≤ fine)
    (L : ℝ) (hL : 0 ≤ L)
    (H : ∀ q, (parentEdges D a (2^fine) E q).Nonempty →
      L ≤ edgeMultiplicity (parentEdges D a (2^fine) E q))
    (p : Parent) (hp : (parentEdges D a (2^coarse) E p).Nonempty) :
    L ≤ edgeMultiplicity (parentEdges D a (2^coarse) E p) := by
  apply partition_multiplicity_lower (parentEdges D a (2^coarse) E p)
    (parentLabel D a (2^fine)) L hL hp
  intro q hq
  have hqn := parent_nonempty (parentEdges D a (2^coarse) E p) (parentLabel D a (2^fine)) hq
  change (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q).Nonempty at hqn
  have he := nested_parentEdges_eq D a E hcf p q hqn
  change L ≤ edgeMultiplicity (parentEdges D a (2^fine) (parentEdges D a (2^coarse) E p) q)
  rw [he]
  exact H q (he ▸ hqn)

/-- Successor interpolation pays only the relative scale power tau*s.
No point uniformity, shading retention, or off-menu native input is used. -/
theorem off_menu_parent_power_lower {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (E : Finset (Fin n × Index))
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (tau theta s : ℝ)
    (hgap : ((fine-coarse:ℕ):ℝ) ≤ tau*level) (hs : 0 ≤ s)
    (H : ∀ q, (parentEdges D a (2^fine) E q).Nonempty →
      D.thickness^theta*(localScale D.thickness fine)^(-s) ≤
        edgeMultiplicity (parentEdges D a (2^fine) E q))
    (p : Parent) (hp : (parentEdges D a (2^coarse) E p).Nonempty) :
    D.thickness^(theta+tau*s)*(localScale D.thickness coarse)^(-s) ≤
      edgeMultiplicity (parentEdges D a (2^coarse) E p) := by
  have hpower := localScale_negative_power hd hdy hcf hgap hs
  have hscale : D.thickness^(tau*s)*(localScale D.thickness coarse)^(-s) ≤
      (localScale D.thickness fine)^(-s) := by
    have hh := mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hd (tau*s)).le
    have he : D.thickness^(tau*s)*D.thickness^(-tau*s)=1 := by
      rw [←Real.rpow_add hd,show tau*s + -tau*s=0 by ring,Real.rpow_zero]
    simpa only [←mul_assoc,he,one_mul] using hh
  calc
    _ = D.thickness^theta*(D.thickness^(tau*s)*(localScale D.thickness coarse)^(-s)) := by
      rw [Real.rpow_add hd]
      ring
    _ ≤ D.thickness^theta*(localScale D.thickness fine)^(-s) :=
      mul_le_mul_of_nonneg_left hscale (Real.rpow_pos_of_pos hd theta).le
    _ ≤ _ := off_menu_parent_lower D a E hcf _
      (mul_nonneg (Real.rpow_pos_of_pos hd theta).le
        (Real.rpow_pos_of_pos (localScale_pos hd fine) (-s)).le) H p hp

end NativeScaleMenuSuccessor
