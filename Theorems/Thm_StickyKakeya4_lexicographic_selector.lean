import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-!
A Borel selector specialized to compact families of marked lines.

For a fixed direction, order the remaining five real coordinates -- the four
offset coordinates followed by the affine mark -- lexicographically.  Every
nonempty compact fibre has a lexicographic minimum.  The points which are not
minimal form a countable union of compact projections: the strict inequality
at the first differing coordinate is replaced by the closed inequalities
`other + 1 / (n + 1) ≤ line`.  Hence the lexicographic minima form a Borel set.
-/

/-- The five coordinates left after fixing the direction of a marked line. -/
def markedLineLexKey (line : MarkedLine) : Fin 5 → ℝ :=
  ![offset line 0, offset line 1, offset line 2, offset line 3, mark line]

theorem continuous_direction : Continuous (direction : MarkedLine → E4) := by
  exact continuous_fst.comp continuous_fst

theorem continuous_markedLineLexKey : Continuous markedLineLexKey := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp [markedLineLexKey, offset, mark] <;> fun_prop

theorem continuous_markedLineLexKey_apply (j : Fin 5) :
    Continuous (fun line : MarkedLine => markedLineLexKey line j) :=
  (continuous_apply j).comp continuous_markedLineLexKey

/-- Closed rational-margin witnesses that `other` is lexicographically below
`line` in their common direction fibre.  The first component is `line`, the
second is `other`. -/
def lexCompetitorClosed (lines : Set MarkedLine) (j : Fin 5) (n : ℕ) :
    Set (MarkedLine × MarkedLine) :=
  (lines ×ˢ lines) ∩
    {p |
      direction p.2 = direction p.1 ∧
      (∀ k, k < j → markedLineLexKey p.2 k = markedLineLexKey p.1 k) ∧
      markedLineLexKey p.2 j + 1 / ((n : ℝ) + 1) ≤ markedLineLexKey p.1 j}

theorem isClosed_lexCompetitorCondition (j : Fin 5) (n : ℕ) :
    IsClosed {p : MarkedLine × MarkedLine |
      direction p.2 = direction p.1 ∧
      (∀ k, k < j → markedLineLexKey p.2 k = markedLineLexKey p.1 k) ∧
      markedLineLexKey p.2 j + 1 / ((n : ℝ) + 1) ≤ markedLineLexKey p.1 j} := by
  have hdir : IsClosed {p : MarkedLine × MarkedLine |
      direction p.2 = direction p.1} :=
    isClosed_eq (continuous_direction.comp continuous_snd)
      (continuous_direction.comp continuous_fst)
  have hprev : IsClosed {p : MarkedLine × MarkedLine |
      ∀ k, k < j → markedLineLexKey p.2 k = markedLineLexKey p.1 k} := by
    rw [show {p : MarkedLine × MarkedLine |
        ∀ k, k < j → markedLineLexKey p.2 k = markedLineLexKey p.1 k} =
      ⋂ k ∈ Set.Iio j, {p : MarkedLine × MarkedLine |
        markedLineLexKey p.2 k = markedLineLexKey p.1 k} by
          ext p
          simp]
    exact isClosed_biInter fun k _hk =>
      isClosed_eq
        ((continuous_markedLineLexKey_apply k).comp continuous_snd)
        ((continuous_markedLineLexKey_apply k).comp continuous_fst)
  have hmargin : IsClosed {p : MarkedLine × MarkedLine |
      markedLineLexKey p.2 j + 1 / ((n : ℝ) + 1) ≤ markedLineLexKey p.1 j} :=
    isClosed_le
      (((continuous_markedLineLexKey_apply j).comp continuous_snd).add continuous_const)
      ((continuous_markedLineLexKey_apply j).comp continuous_fst)
  exact hdir.inter (hprev.inter hmargin)

theorem isCompact_lexCompetitorClosed (lines : Set MarkedLine)
    (hcompact : IsCompact lines) (j : Fin 5) (n : ℕ) :
    IsCompact (lexCompetitorClosed lines j n) := by
  exact (hcompact.prod hcompact).inter_right
    (isClosed_lexCompetitorCondition j n)

theorem isCompact_fst_image_lexCompetitorClosed (lines : Set MarkedLine)
    (hcompact : IsCompact lines) (j : Fin 5) (n : ℕ) :
    IsCompact (Prod.fst '' lexCompetitorClosed lines j n) :=
  (isCompact_lexCompetitorClosed lines hcompact j n).image continuous_fst

/-- A line is dominated when another line in the same direction fibre has a
strictly smaller five-coordinate lexicographic key. -/
def lexDominatedLines (lines : Set MarkedLine) : Set MarkedLine :=
  {line | line ∈ lines ∧ ∃ other ∈ lines,
    direction other = direction line ∧
      toLex (markedLineLexKey other) < toLex (markedLineLexKey line)}

/-- The canonical selector consists of the undominated lines. -/
def lexicographicDirectionSelector (lines : Set MarkedLine) : Set MarkedLine :=
  lines \ lexDominatedLines lines

theorem lexDominatedLines_eq_iUnion_compact_images (lines : Set MarkedLine) :
    lexDominatedLines lines =
      ⋃ j : Fin 5, ⋃ n : ℕ, Prod.fst '' lexCompetitorClosed lines j n := by
  ext line
  constructor
  · rintro ⟨hline, other, hother, hdir, hlt⟩
    rcases hlt with ⟨j, hprev, hj⟩
    have hprevKey : ∀ k, k < j →
        markedLineLexKey other k = markedLineLexKey line k := by
      intro k hk
      simpa using hprev k hk
    have hjKey : markedLineLexKey other j < markedLineLexKey line j := by
      simpa using hj
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hjKey)
    refine mem_iUnion_of_mem j (mem_iUnion_of_mem n ?_)
    refine ⟨(line, other), ?_, rfl⟩
    refine ⟨⟨hline, hother⟩, hdir, hprevKey, ?_⟩
    linarith
  · simp only [mem_iUnion, mem_image]
    rintro ⟨j, n, pair, hpair, rfl⟩
    rcases hpair with ⟨⟨hline, hother⟩, hdir, hprev, hmargin⟩
    refine ⟨hline, pair.2, hother, hdir, ?_⟩
    refine ⟨j, ?_, ?_⟩
    · intro k hk
      simpa using hprev k hk
    have hpositive : 0 < 1 / ((n : ℝ) + 1) := by positivity
    change markedLineLexKey pair.2 j < markedLineLexKey pair.1 j
    linarith

theorem measurableSet_lexDominatedLines (lines : Set MarkedLine)
    (hcompact : IsCompact lines) : MeasurableSet (lexDominatedLines lines) := by
  rw [lexDominatedLines_eq_iUnion_compact_images]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun n =>
    (isCompact_fst_image_lexCompetitorClosed lines hcompact j n).measurableSet

theorem measurableSet_lexicographicDirectionSelector (lines : Set MarkedLine)
    (hcompact : IsCompact lines) :
    MeasurableSet (lexicographicDirectionSelector lines) := by
  exact hcompact.measurableSet.diff (measurableSet_lexDominatedLines lines hcompact)

theorem lexicographicDirectionSelector_subset (lines : Set MarkedLine) :
    lexicographicDirectionSelector lines ⊆ lines :=
  sdiff_subset

/-- A nonempty compact family of marked lines has a least five-coordinate key
in lexicographic order.  This is a finite sequence of ordinary real minima,
one for each offset coordinate and finally the affine mark. -/
theorem IsCompact.exists_markedLineLexKey_min
    {s : Set MarkedLine} (hcompact : IsCompact s) (hnonempty : s.Nonempty) :
    ∃ line ∈ s, ∀ other ∈ s,
      ¬toLex (markedLineLexKey other) < toLex (markedLineLexKey line) := by
  obtain ⟨x0, hx0, hmin0⟩ := hcompact.exists_isMinOn hnonempty
    (continuous_markedLineLexKey_apply 0).continuousOn
  let F1 : Set MarkedLine :=
    s ∩ {x | markedLineLexKey x 0 = markedLineLexKey x0 0}
  have hF1compact : IsCompact F1 := by
    apply hcompact.inter_right
    exact isClosed_eq (continuous_markedLineLexKey_apply 0) continuous_const
  have hx0F1 : x0 ∈ F1 := ⟨hx0, rfl⟩
  obtain ⟨x1, hx1, hmin1⟩ := hF1compact.exists_isMinOn ⟨x0, hx0F1⟩
    (continuous_markedLineLexKey_apply 1).continuousOn
  let F2 : Set MarkedLine :=
    F1 ∩ {x | markedLineLexKey x 1 = markedLineLexKey x1 1}
  have hF2compact : IsCompact F2 := by
    apply hF1compact.inter_right
    exact isClosed_eq (continuous_markedLineLexKey_apply 1) continuous_const
  have hx1F2 : x1 ∈ F2 := ⟨hx1, rfl⟩
  obtain ⟨x2, hx2, hmin2⟩ := hF2compact.exists_isMinOn ⟨x1, hx1F2⟩
    (continuous_markedLineLexKey_apply 2).continuousOn
  let F3 : Set MarkedLine :=
    F2 ∩ {x | markedLineLexKey x 2 = markedLineLexKey x2 2}
  have hF3compact : IsCompact F3 := by
    apply hF2compact.inter_right
    exact isClosed_eq (continuous_markedLineLexKey_apply 2) continuous_const
  have hx2F3 : x2 ∈ F3 := ⟨hx2, rfl⟩
  obtain ⟨x3, hx3, hmin3⟩ := hF3compact.exists_isMinOn ⟨x2, hx2F3⟩
    (continuous_markedLineLexKey_apply 3).continuousOn
  let F4 : Set MarkedLine :=
    F3 ∩ {x | markedLineLexKey x 3 = markedLineLexKey x3 3}
  have hF4compact : IsCompact F4 := by
    apply hF3compact.inter_right
    exact isClosed_eq (continuous_markedLineLexKey_apply 3) continuous_const
  have hx3F4 : x3 ∈ F4 := ⟨hx3, rfl⟩
  obtain ⟨x4, hx4, hmin4⟩ := hF4compact.exists_isMinOn ⟨x3, hx3F4⟩
    (continuous_markedLineLexKey_apply 4).continuousOn
  rcases hx4 with ⟨⟨⟨⟨hx4s, hx4c0⟩, hx4c1⟩, hx4c2⟩, hx4c3⟩
  change markedLineLexKey x4 0 = markedLineLexKey x0 0 at hx4c0
  change markedLineLexKey x4 1 = markedLineLexKey x1 1 at hx4c1
  change markedLineLexKey x4 2 = markedLineLexKey x2 2 at hx4c2
  change markedLineLexKey x4 3 = markedLineLexKey x3 3 at hx4c3
  refine ⟨x4, hx4s, ?_⟩
  intro other hother hlt
  rcases hlt with ⟨j, hprev, hj⟩
  have hprevKey : ∀ k, k < j →
      markedLineLexKey other k = markedLineLexKey x4 k := by
    intro k hk
    simpa using hprev k hk
  have hjKey : markedLineLexKey other j < markedLineLexKey x4 j := by
    simpa using hj
  fin_cases j
  · have hj0 : markedLineLexKey other 0 < markedLineLexKey x4 0 := by
      simpa using hjKey
    rw [hx4c0] at hj0
    exact (not_lt_of_ge (hmin0 hother)) hj0
  · have hotherF1 : other ∈ F1 := by
      refine ⟨hother, ?_⟩
      exact (hprevKey 0 (by decide)).trans hx4c0
    have hj1 : markedLineLexKey other 1 < markedLineLexKey x4 1 := by
      simpa using hjKey
    rw [hx4c1] at hj1
    exact (not_lt_of_ge (hmin1 hotherF1)) hj1
  · have hotherF2 : other ∈ F2 := by
      refine ⟨⟨hother, (hprevKey 0 (by decide)).trans hx4c0⟩, ?_⟩
      exact (hprevKey 1 (by decide)).trans hx4c1
    have hj2 : markedLineLexKey other 2 < markedLineLexKey x4 2 := by
      simpa using hjKey
    rw [hx4c2] at hj2
    exact (not_lt_of_ge (hmin2 hotherF2)) hj2
  · have hotherF3 : other ∈ F3 := by
      refine ⟨⟨⟨hother, (hprevKey 0 (by decide)).trans hx4c0⟩,
        (hprevKey 1 (by decide)).trans hx4c1⟩, ?_⟩
      exact (hprevKey 2 (by decide)).trans hx4c2
    have hj3 : markedLineLexKey other 3 < markedLineLexKey x4 3 := by
      simpa using hjKey
    rw [hx4c3] at hj3
    exact (not_lt_of_ge (hmin3 hotherF3)) hj3
  · have hotherF4 : other ∈ F4 := by
      refine ⟨⟨⟨⟨hother, (hprevKey 0 (by decide)).trans hx4c0⟩,
        (hprevKey 1 (by decide)).trans hx4c1⟩,
        (hprevKey 2 (by decide)).trans hx4c2⟩, ?_⟩
      exact (hprevKey 3 (by decide)).trans hx4c3
    have hj4 : markedLineLexKey other 4 < markedLineLexKey x4 4 := by
      simpa using hjKey
    exact (not_lt_of_ge (hmin4 hotherF4)) hj4

theorem markedLine_eq_of_direction_eq_of_lexKey_eq
    {line other : MarkedLine}
    (hdir : direction line = direction other)
    (hkey : markedLineLexKey line = markedLineLexKey other) :
    line = other := by
  apply Prod.ext
  · apply Prod.ext
    · exact hdir
    · ext j
      fin_cases j
      · simpa [markedLineLexKey, offset, mark] using congrFun hkey (0 : Fin 5)
      · simpa [markedLineLexKey, offset, mark] using congrFun hkey (1 : Fin 5)
      · simpa [markedLineLexKey, offset, mark] using congrFun hkey (2 : Fin 5)
      · simpa [markedLineLexKey, offset, mark] using congrFun hkey (3 : Fin 5)
  · simpa [markedLineLexKey, offset, mark] using congrFun hkey (4 : Fin 5)

/-- The lexicographic minimum construction gives a Borel, exactly
one-line-per-direction subfamily of every compact full-direction family. -/
theorem compact_full_direction_lexicographic_selector
    (lines : Set MarkedLine)
    (hcompact : IsCompact lines)
    (hfull : FullDirection lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧
      selector ⊆ lines ∧
      IsDirectionSelector selector := by
  refine ⟨lexicographicDirectionSelector lines,
    measurableSet_lexicographicDirectionSelector lines hcompact,
    lexicographicDirectionSelector_subset lines, ?_⟩
  intro theta htheta
  obtain ⟨seed, hseedLines, hseedDir⟩ := hfull theta htheta
  let fibre : Set MarkedLine := lines ∩ {line | direction line = theta}
  have hfibreCompact : IsCompact fibre := by
    apply hcompact.inter_right
    exact isClosed_eq continuous_direction continuous_const
  have hseedFibre : seed ∈ fibre := ⟨hseedLines, hseedDir⟩
  obtain ⟨line, hlineFibre, hlineMinimal⟩ :=
    IsCompact.exists_markedLineLexKey_min hfibreCompact ⟨seed, hseedFibre⟩
  rcases hlineFibre with ⟨hlineLines, hlineDir⟩
  have hlineNotDominated : line ∉ lexDominatedLines lines := by
    rintro ⟨_hlineLines, other, hotherLines, hotherDir, hotherLt⟩
    have hotherFibre : other ∈ fibre :=
      ⟨hotherLines, hotherDir.trans hlineDir⟩
    exact hlineMinimal other hotherFibre hotherLt
  have hlineSelector : line ∈ lexicographicDirectionSelector lines :=
    ⟨hlineLines, hlineNotDominated⟩
  refine ⟨line, ⟨hlineSelector, hlineDir⟩, ?_⟩
  intro other hother
  rcases hother with ⟨hotherSelector, hotherDir⟩
  rcases hotherSelector with ⟨hotherLines, hotherNotDominated⟩
  rcases lt_trichotomy
      (toLex (markedLineLexKey other))
      (toLex (markedLineLexKey line)) with hotherLt | hkeyEq | hlineLt
  · exfalso
    exact hlineNotDominated
      ⟨hlineLines, other, hotherLines,
        hotherDir.trans hlineDir.symm, hotherLt⟩
  · apply markedLine_eq_of_direction_eq_of_lexKey_eq
    · exact hotherDir.trans hlineDir.symm
    · exact toLex_inj.mp hkeyEq
  · exfalso
    exact hotherNotDominated
      ⟨hotherLines, line, hlineLines,
        hlineDir.trans hotherDir.symm, hlineLt⟩

end StickyKakeya4
