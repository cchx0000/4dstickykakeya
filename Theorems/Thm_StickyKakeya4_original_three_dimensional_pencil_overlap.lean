import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_geometry
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalThreeDimensionalPencilOverlap
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalPencilGeometry NativeTangentGridCoarsening

/-- The original line point at the query height converts physical exclusion
into a genuine transverse residual. -/
theorem original_outside_stem_residual (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (x : Point3) (s : ℝ) (hs : 0 < s)
    (hne : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hout : x ∉ physicalTube3 stem.1 stem.2 s) :
    s/2 < |graphResidual stem (e 2) x (e 0)| ∨
      s/2 < |graphResidual stem (e 2) x (e 1)| := by
  by_contra! h
  apply hout
  let l := (x (e 2)-stem.1 (e 2))/(stem.2 (e 2)-stem.1 (e 2))
  have hm : graphResidual stem (e 2) x (e 2)=0 := by
    simp [graphResidual,OriginalThreeDimensionalTubeParameters.slope,offset,hne]
  have hb (k : Fin 3) : |graphResidual stem (e 2) x (e k)| ≤ s/2 := by
    fin_cases k
    · exact h.1
    · exact h.2
    · change |graphResidual stem (e 2) x (e 2)| ≤ s/2
      rw [hm,abs_zero]
      positivity
  have he (j : Fin 3) : |x j-linePoint3 stem.1 stem.2 l j| ≤ s/2 := by
    rw [original_graph_point stem (e 2) j (x (e 2)) hne]
    simpa only [graphResidual,Equiv.apply_symm_apply] using hb (e.symm j)
  refine ⟨l,?_⟩
  unfold distance3
  apply (Real.sqrt_le_left hs.le).mpr
  have hsq (j : Fin 3) : (x j-linePoint3 stem.1 stem.2 l j)^2 ≤ (s/2)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he j) 2
  nlinarith only [hsq 0,hsq 1,hsq 2,sq_nonneg s]

/-- One literal scalar chart has bounded overlap. The large-mesh branch
uses the total interval of coefficients; no small-cap estimate is used
outside its range. -/
theorem original_scalar_pencil_overlap {X : Type*} (S : Finset X) (t : X → ℝ)
    (rho s A B : ℝ) (hrho : 0 < rho) (hs : 0 < s) (hs1 : s ≤ 1)
    (hinj : Set.InjOn (fun v => ⌊t v/rho⌋) S)
    (ht : ∀ v∈S, |t v| ≤ 1)
    (hband : ∀ v∈S, |A+t v*B| ≤ 100*rho)
    (hout : s/2 < |A| ∨ s/2 < |B|) :
    (S.card : ℝ) ≤ 1602/s := by
  have hcard : (scalarCells S t rho).card=S.card := Finset.card_image_of_injOn hinj
  by_cases hsmall : rho ≤ s/800
  · by_cases hS : S.Nonempty
    · obtain ⟨v₀,hv₀⟩ := hS
      have hden : s/4 ≤ |B| := by
        by_contra! hden
        have hA : s/2 < |A| := hout.resolve_right (by linarith only [hden,hs])
        have hprod := mul_le_mul_of_nonneg_right (ht v₀ hv₀) (abs_nonneg B)
        have hh := abs_sub (A+t v₀*B) (t v₀*B)
        have heq : A+t v₀*B-t v₀*B=A := by ring
        rw [heq,abs_mul] at hh
        linarith only [hA,hh,hprod,hband v₀ hv₀,hden,hsmall,hs]
      have hclose (v : X) (hv : v∈S) : |t v-t v₀| ≤ 800*rho/s := by
        have hh := abs_sub (A+t v*B) (A+t v₀*B)
        have heq : A+t v*B-(A+t v₀*B)=(t v-t v₀)*B := by ring
        rw [heq,abs_mul] at hh
        have hp := mul_le_mul_of_nonneg_left hden (abs_nonneg (t v-t v₀))
        apply (le_div_iff₀ hs).mpr
        nlinarith only [hh,hp,hband v hv,hband v₀ hv₀]
      have hc := scalar_interval_grid_card S t (r:=rho)
        (c:=t v₀-800*rho/s) (L:=1600*rho/s) hrho (by positivity) (by
          intro v hv
          have hh := abs_le.mp (hclose v hv)
          constructor
          · linarith only [hh.1]
          · have heq : t v₀-800*rho/s+1600*rho/s=t v₀+800*rho/s := by ring
            rw [heq]
            linarith only [hh.2])
      rw [hcard] at hc
      have heq : (1600*rho/s)/rho+2=1600/s+2 := by field_simp
      rw [heq] at hc
      have hb : 1600/s+2 ≤ 1602/s := by
        apply (le_div_iff₀ hs).mpr
        field_simp
        linarith only [hs1]
      exact hc.trans hb
    · have hzero : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp only [hzero,Finset.card_empty,Nat.cast_zero]
      positivity
  · have hc := scalar_interval_grid_card S t (r:=rho) (c:=(-1:ℝ)) (L:=2)
      hrho (by norm_num) (by
        intro v hv
        have hh := abs_le.mp (ht v hv)
        constructor
        · exact hh.1
        · linarith only [hh.2])
    rw [hcard] at hc
    have hinv : 2/rho ≤ 1600/s := by
      apply (div_le_div_iff₀ hrho hs).mpr
      linarith only [lt_of_not_ge hsmall]
    have hb : 1600/s+2 ≤ 1602/s := by
      apply (le_div_iff₀ hs).mpr
      field_simp
      linarith only [hs1]
    have hh : 2/rho+2 ≤ 1600/s+2 := by linarith only [hinv]
    exact hc.trans (hh.trans hb)

/-- Two actual coefficient charts and actual integer cells bound overlap
of exact unnormalized plane bands away from the original physical stem. -/
theorem original_pencil_band_overlap {X : Type*} (S : Finset X)
    (chart : X → Bool) (t : X → ℝ) (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (x : Point3) (rho s : ℝ) (hrho : 0 < rho) (hs : 0 < s) (hs1 : s ≤ 1)
    (hne : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hout : x ∉ physicalTube3 stem.1 stem.2 s)
    (hinj : Set.InjOn (fun v => (chart v,⌊t v/rho⌋)) S)
    (ht : ∀ v∈S, |t v| ≤ 1) :
    ((S.filter (fun v => |pencilValue stem e (chart v) (t v) x| ≤ 100*rho)).card : ℝ)
      ≤ 4000/s := by
  let F := S.filter (fun v => |pencilValue stem e (chart v) (t v) x| ≤ 100*rho)
  let F₀ := F.filter (fun v => chart v=false)
  let F₁ := F.filter (fun v => chart v=true)
  have haway := original_outside_stem_residual stem e x s hs hne hout
  have hsub₀ : F₀⊆S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hsub₁ : F₁⊆S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have h₀ : (F₀.card : ℝ) ≤ 1602/s := by
    apply original_scalar_pencil_overlap F₀ t rho s
      (graphResidual stem (e 2) x (e 0)) (graphResidual stem (e 2) x (e 1))
      hrho hs hs1
    · intro v hv w hw heq
      apply hinj (hsub₀ hv) (hsub₀ hw)
      exact Prod.ext ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) heq
    · exact fun v hv => ht v (hsub₀ hv)
    · intro v hv
      have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      simpa only [pencilValue,(Finset.mem_filter.mp hv).2,Bool.false_eq_true,↓reduceIte] using hh
    · exact haway
  have h₁ : (F₁.card : ℝ) ≤ 1602/s := by
    apply original_scalar_pencil_overlap F₁ t rho s
      (graphResidual stem (e 2) x (e 1)) (graphResidual stem (e 2) x (e 0))
      hrho hs hs1
    · intro v hv w hw heq
      apply hinj (hsub₁ hv) (hsub₁ hw)
      exact Prod.ext ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) heq
    · exact fun v hv => ht v (hsub₁ hv)
    · intro v hv
      have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      simpa only [pencilValue,(Finset.mem_filter.mp hv).2,↓reduceIte,add_comm] using hh
    · exact haway.symm
  have hcover : F⊆F₀∪F₁ := by
    intro v hv
    cases h : chart v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,h⟩)
  have hc : (F.card : ℝ) ≤ F₀.card+F₁.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le F₀ F₁)
  change (F.card : ℝ) ≤ 4000/s
  calc
    _ ≤ (F₀.card : ℝ)+(F₁.card : ℝ) := hc
    _ ≤ 1602/s+1602/s := add_le_add h₀ h₁
    _ = 3204/s := by ring
    _ ≤ 4000/s := div_le_div_of_nonneg_right (by norm_num) hs.le

end OriginalThreeDimensionalPencilOverlap
