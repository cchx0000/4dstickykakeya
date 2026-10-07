import Theorems.Thm_StickyKakeya4_native_original_phase_chart_gaps
import Theorems.Thm_StickyKakeya4_native_full_reference_carrier_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeCappedOldAncestors
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeFullCoarseShadow
open NativeDyadicParentCells NativeCoarseAncestorCounts NativeCoarseSourceProfiles
open NativeUnitParentNormalization NativeOriginalCellChartGeometry NativeOriginalPhaseChartGaps

/-- A dyadic ancestor is capped at the ACTUAL output phase. The terminal
case will use equality of representatives, instead of a false fine-cell AD law. -/
theorem exists_capped_depth (b : ℕ) {sigma : ℝ} (hsigma : sigma ≤ 1) :
    ∃ k ≤ b, sigma ≤ 1344/((2^k:ℕ):ℝ) ∧ (672/((2^k:ℕ):ℝ) ≤ sigma ∨ k=b) := by
  induction b with
  | zero =>
      refine ⟨0, le_rfl, ?_, Or.inr rfl⟩
      norm_num
      linarith
  | succ b ih =>
      by_cases hb : 672/((2^b:ℕ):ℝ) ≤ sigma
      · obtain ⟨k, hk, hupper, hcase⟩ := ih
        rcases hcase with hlower | hkb
        · exact ⟨k, by omega, hupper, Or.inl hlower⟩
        · exact ⟨k, by omega, hupper, Or.inl (by simpa only [hkb] using hb)⟩
      · refine ⟨b+1, le_rfl, ?_, Or.inr rfl⟩
        have he : (1344:ℝ)/((2^(b+1):ℕ):ℝ)=672/((2^b:ℕ):ℝ) := by
          rw [pow_succ]
          push_cast
          field_simp
          norm_num
        rw [he]
        exact le_of_lt (lt_of_not_ge hb)

/-- Literal original phase ancestor on the fullSource index set. -/
def oldAncestor {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    (b k : ℕ) (i : Fin (R.image (parentLabel D a (2^b))).card) : Parent :=
  ancestor b k (parentIndex (R.image (parentLabel D a (2^b))) i)

lemma terminal_injective {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (b : ℕ) : Function.Injective (oldAncestor D R a b b) := by
  intro i j he
  apply parentIndex_injective (R.image (parentLabel D a (2^b)))
  simpa only [oldAncestor, ancestor, Nat.sub_self, pow_zero, Nat.cast_one, Int.ediv_one,
    Prod.mk.eta] using he

lemma representative_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (b k : ℕ) (hk : k ≤ b) (i : Fin (R.image (parentLabel D a (2^b))).card) :
    parentLabel D a (2^k) (representative h R a (2^b)
      (parentIndex (R.image (parentLabel D a (2^b))) i)) = oldAncestor D R a b k i := by
  rw [← parent_ancestor_eq D a hk]
  rw [(representative_spec h R a (2^b) (parentIndex_mem _ i)).2]
  rfl

/-- Exact equality of the indexed fullSource fiber with its original
occupied-parent descendant population. Shading never enters the equality. -/
theorem fiber_card {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    (b k : ℕ) (q : Parent) :
    ((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
      (fun i => oldAncestor D R a b k i=q)).card = (descendants D R a b k q).card := by
  exact card_filter_parentIndex (R.image (parentLabel D a (2^b)))
    (fun t => ancestor b k t=q)

theorem full_fiber_population {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (b : ℕ)
    (H : ∀ j : Fin (b+1), ∀ q : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=q)).Nonempty →
        D.thickness^e*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ≤
          D.thickness^(-e)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (k : ℕ) (hk : k ≤ b) (i : Fin (R.image (parentLabel D a (2^b))).card) :
    D.thickness^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3 ≤
      (((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
        (fun j => oldAncestor D R a b k j=oldAncestor D R a b k i)).card:ℝ) := by
  rw [fiber_card]
  apply (coarse_ancestor_AD h R a e b H hk le_rfl _ ?_).1
  exact ⟨parentIndex _ i, mem_filter.mpr ⟨parentIndex_mem _ i, rfl⟩⟩

/-- Both branches give actual sigma-gaps for the fullSource's unchanged
representatives. The terminal branch uses the same INDEX, hence same line. -/
theorem capped_chart_gaps {n : ℕ} {D : FiniteScaleSource n} {eta a sigma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i∈fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b k : ℕ) (hk : k ≤ b)
    (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (hsigma : 0 ≤ sigma)
    (hcap : 672/((2^k:ℕ):ℝ) ≤ sigma ∨ k=b)
    (i j : Fin (R.image (parentLabel D a (2^b))).card)
    (he : oldAncestor D R a b k i=oldAncestor D R a b k j) :
    let li := MarkedIsometricChart.line O c ((fullSource h R a level b E).line i)
    let lj := MarkedIsometricChart.line O c ((fullSource h R a level b E).line j)
    (∀ v : Fin 3, |slope li v-slope lj v| ≤ sigma) ∧
      ∀ v : Fin 3, |intercept li v-intercept lj v| ≤ sigma := by
  intro li lj
  rcases hcap with hsmall | hkb
  · have hphase : parentLabel D a (2^k) (representative h R a (2^b) (parentIndex _ i)) =
        parentLabel D a (2^k) (representative h R a (2^b) (parentIndex _ j)) := by
      rw [representative_readback h R a b k hk i, representative_readback h R a b k hk j]
      exact he
    have hh := original_phase_chart_gaps h hK ha O hO c hc (2^k) (by positivity)
      (representative h R a (2^b) (parentIndex _ i))
      (representative h R a (2^b) (parentIndex _ j)) hphase
    exact ⟨fun v => (hh.1 v).trans hsmall, fun v => (hh.2 v).trans hsmall⟩
  · subst k
    have hij : i=j := terminal_injective D R a b he
    subst j
    exact ⟨fun _ => by simpa only [sub_self, abs_zero] using hsigma,
      fun _ => by simpa only [sub_self, abs_zero] using hsigma⟩

/-- Exact native64 scale cancellation: the old ancestor choice pays21^3
in carrier normalization. The original reference power is left visible. -/
theorem carrier_scale_normalization (epsilon e sigma : ℝ) (hepsilon : 0 < epsilon)
    (hsigma : 0 ≤ sigma) (b k : ℕ) (hupper : sigma ≤ 1344/((2^k:ℕ):ℝ)) :
    sigma^3 ≤ (21^3*epsilon^(-(2*e)))*
      (epsilon^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3)*(64/((2^b:ℕ):ℝ))^3 := by
  have hp : epsilon^(2*e) ≠ 0 := (Real.rpow_pos_of_pos hepsilon _).ne'
  have hpowb : (((2^b:ℕ):ℝ)) ≠ 0 := by positivity
  have hpowk : (((2^k:ℕ):ℝ)) ≠ 0 := by positivity
  have he : (21^3*epsilon^(-(2*e)))*
      (epsilon^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3)*(64/((2^b:ℕ):ℝ))^3 =
      (1344/((2^k:ℕ):ℝ))^3 := by
    rw [Real.rpow_neg hepsilon.le]
    field_simp [hp, hpowb, hpowk]
    ring
  rw [he]
  exact pow_le_pow_left₀ hsigma hupper 3

/-- One actual capped old ancestor supplies geometry, its full original
population, and scale normalization simultaneously. The complete ambient
coarse source and all its representatives remain unchanged. -/
theorem exists_full_source_ancestors {n : ℕ} {D : FiniteScaleSource n} {eta a e sigma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i∈fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level b : ℕ) (E : Finset (Fin n × Index))
    (H : ∀ j : Fin (b+1), ∀ q : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=q)).Nonempty →
        D.thickness^e*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=q)).card:ℝ) ≤
          D.thickness^(-e)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ∃ k ≤ b, let L := D.thickness^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3
      (∀ i, L ≤
        (((univ : Finset (Fin (R.image (parentLabel D a (2^b))).card)).filter
          (fun j => oldAncestor D R a b k j=oldAncestor D R a b k i)).card:ℝ)) ∧
      sigma^3 ≤ (21^3*D.thickness^(-(2*e)))*L*(64/((2^b:ℕ):ℝ))^3 ∧
      ∀ i j : Fin (R.image (parentLabel D a (2^b))).card,
        oldAncestor D R a b k i=oldAncestor D R a b k j →
        let li := MarkedIsometricChart.line O c ((fullSource h R a level b E).line i)
        let lj := MarkedIsometricChart.line O c ((fullSource h R a level b E).line j)
        (∀ v : Fin 3, |slope li v-slope lj v| ≤ sigma) ∧
          ∀ v : Fin 3, |intercept li v-intercept lj v| ≤ sigma := by
  obtain ⟨k, hk, hu, hl⟩ := exists_capped_depth b hsigma1
  refine ⟨k, hk, ?_⟩
  dsimp only
  refine ⟨fun i => full_fiber_population h R a b H k hk i, ?_, ?_⟩
  · exact carrier_scale_normalization D.thickness e sigma h.1.2.1 hsigma b k hu
  · exact capped_chart_gaps h hK ha R level b k hk E O hO c hc hsigma hl

end NativeCappedOldAncestors
