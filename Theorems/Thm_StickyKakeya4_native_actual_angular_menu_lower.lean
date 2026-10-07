import Theorems.Thm_StickyKakeya4_native_original_angular_tuple_menu
import Theorems.Thm_StickyKakeya4_native_actual_squared_grain_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section

namespace NativeActualAngularMenuLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeJointUniformCoarseRelations NativeIncidentRankSelection
open NativeDirectionRankDichotomy NativeOriginalCoarseTupleMenu NativeOriginalAngularTupleMenu
open NativeIncidenceMultiplicityTower NativeOriginalParentDensityCore SelfUniform
open scoped BigOperators

/-- The installed E2 point relation bounds its actual global mean by every
surviving literal point fiber. No occupancy or retained-point fraction is assumed. -/
lemma mean_le_point_fiber {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E : Finset (T × X)) (Q : ℕ) (H : HasUniformFibers E Q Prod.snd)
    (k : X) (hk : k∈E.image Prod.snd) :
    NativeIncidenceMultiplicityTower.multiplicity E ≤ (Q:ℝ)^2*((E.filter (fun z => z.2=k)).card:ℝ) := by
  obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
  have hs : (0:ℝ) < (E.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (show (E.image Prod.snd).Nonempty from ⟨k,hk⟩)
  have hc : E.card ≤ Q^2*(E.image Prod.snd).card*(E.filter (fun z => z.2=k)).card := by
    calc
      _ = ∑x∈E.image Prod.snd,(E.filter (fun z => z.2=x)).card := card_eq_sum_card_image Prod.snd E
      _ ≤ ∑_x∈E.image Prod.snd,Q^2*(E.filter (fun z => z.2=k)).card := by
        apply sum_le_sum
        intro x hx
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
        simpa only [hzk] using H y hy z hz
      _ = _ := by simp; ring
  have hcR : (E.card:ℝ) ≤ (Q:ℝ)^2*(E.image Prod.snd).card*(E.filter (fun z => z.2=k)).card := by
    exact_mod_cast hc
  apply (div_le_iff₀ hs).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hcR

/-- Genuine terminal angular-menu cardinality, using the actual E2 chain
count and E2 point uniformity, but only ORIGINAL E1 parent fiber uppers.
The explicit denominator is exactly the half-mass factor2 times343. -/
theorem point_angular_menu_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2⊆incidences original)
    (m Q1 Q2 : ℕ) (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (Href : HasUniformFibers E1 Q1 (formalPair D a m))
    (Hpoint : HasUniformFibers E2 Q2 Prod.snd) (U : ℝ) (hU : 0 < U)
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤ U)
    (q : ℝ) (ell : ℕ)
    (Hchains : ∀k∈E2.image Prod.snd,
      (((pointSet E2 k).card:ℝ)/2)^ell ≤
        ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q ell).card:ℝ)) :
    ∀k∈E2.image Prod.snd,
      (NativeIncidenceMultiplicityTower.multiplicity E2/(686*(Q1:ℝ)^2*(Q2:ℝ)^2*U))^ell ≤
        ((angularMenu D a m E2 k q ell).card:ℝ) := by
  intro k hk
  let A := pointSet E2 k
  let C := chains A (fun z => slopeVector D z.1) q ell
  let f := fun z : Fin n × Index => parentLabel D a (2^m) z.1
  let B := (Q1:ℝ)^2*U
  have hQ1R : (0:ℝ) < Q1 := by exact_mod_cast hQ1
  have hQ2R : (0:ℝ) < Q2 := by exact_mod_cast hQ2
  have hB : 0 < B := by dsimp [B]; positivity
  have hmu : 0 ≤ NativeIncidenceMultiplicityTower.multiplicity E2 := by unfold NativeIncidenceMultiplicityTower.multiplicity; positivity
  have hpoint : NativeIncidenceMultiplicityTower.multiplicity E2 ≤ (Q2:ℝ)^2*(A.card:ℝ) := mean_le_point_fiber E2 Q2 Hpoint k hk
  have hbase : NativeIncidenceMultiplicityTower.multiplicity E2/(2*(Q2:ℝ)^2) ≤ (A.card:ℝ)/2 := by
    apply (div_le_iff₀ (show (0:ℝ)<2*(Q2:ℝ)^2 by positivity)).mpr
    calc
      _ ≤ (Q2:ℝ)^2*(A.card:ℝ) := hpoint
      _ = _ := by ring
  have hcount : (NativeIncidenceMultiplicityTower.multiplicity E2/(2*(Q2:ℝ)^2))^ell ≤ (C.card:ℝ) :=
    (pow_le_pow_left₀ (by positivity) hbase ell).trans (Hchains k hk)
  have hfiber (p : Parent) : ((A.filter (fun z => f z=p)).card:ℝ) ≤ B :=
    retained_point_parent_fiber_upper D E1 E2 h21 a m Q1 Href U hU.le hupper k p
  have hcoarse : (NativeIncidenceMultiplicityTower.multiplicity E2/(2*(Q2:ℝ)^2))^ell/B^ell ≤
      ((coarseMenu D a m E2 k q ell).card:ℝ) :=
    NativeFiniteTupleFibers.coarse_tuple_card_lower A C f ell
      (fun xs hxs => chains_length _ _ _ _ xs hxs)
      (fun xs hxs z hz => chains_labels _ _ _ _ xs hxs z hz)
      B hB hfiber _ hcount
  have hangular := coarse_to_angular_card_lower h original horiginal ha m hscale E2 hE2 k q ell
  calc
    _ = ((NativeIncidenceMultiplicityTower.multiplicity E2/(2*(Q2:ℝ)^2))^ell/B^ell)/(343:ℝ)^ell := by
      rw [←div_pow,←div_pow]
      congr 1
      simp only [div_div]
      congr 1
      dsimp [B]
      ring
    _ ≤ ((coarseMenu D a m E2 k q ell).card:ℝ)/(343:ℝ)^ell :=
      div_le_div_of_nonneg_right hcoarse (by positivity)
    _ ≤ _ := hangular

/-- The candidate selector's exact weighted terminal numerator has the
proved angular lower at every original surviving point. Weights remain literal
original-label Nat weights; no assumed small-f retention parameter occurs. -/
theorem weighted_angular_numerator_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2⊆incidences original)
    (m Q1 Q2 : ℕ) (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (Href : HasUniformFibers E1 Q1 (formalPair D a m))
    (Hpoint : HasUniformFibers E2 Q2 Prod.snd) (U : ℝ) (hU : 0 < U)
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤ U)
    (q : ℝ) (ell : ℕ)
    (Hchains : ∀k∈E2.image Prod.snd,
      (((pointSet E2 k).card:ℝ)/2)^ell ≤
        ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q ell).card:ℝ))
    (w : Index → ℕ) :
    (NativeIncidenceMultiplicityTower.multiplicity E2/(686*(Q1:ℝ)^2*(Q2:ℝ)^2*U))^ell*
        (SelfUniform.mass w (E2.image Prod.snd):ℝ) ≤
      ((∑k∈E2.image Prod.snd,w k*(angularMenu D a m E2 k q ell).card:ℕ):ℝ) := by
  have H := point_angular_menu_lower h original horiginal ha E1 E2 h21 hE2 m Q1 Q2 hQ1 hQ2
    hscale Href Hpoint U hU hupper q ell Hchains
  simp only [SelfUniform.mass,Nat.cast_sum,Nat.cast_mul]
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (H k hk) (Nat.cast_nonneg (α := ℝ) (w k))

end NativeActualAngularMenuLower
