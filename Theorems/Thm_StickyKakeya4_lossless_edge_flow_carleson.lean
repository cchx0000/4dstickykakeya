import Definitions.Def_sticky_kakeya4_core

namespace StickyKakeya4

theorem lossless_edge_flow_carleson
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming : Fin n → ENNReal)
    (paid : Fin n → ENNReal)
    (leafMass : Fin n → ENNReal)
    (hconserve : ∀ i,
      incoming i = paid i + leafMass i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) :
    Finset.univ.sum (fun i : Fin n => paid i + leafMass i) ≤
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) := by
  classical
  let roots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then incoming i else 0)
  let nonroots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then 0 else incoming i)
  let payments : ENNReal := Finset.univ.sum (fun i : Fin n => paid i + leafMass i)
  by_cases hroots : roots = ⊤
  · simpa [roots, hroots]
  have hincoming_ne_top : ∀ i, incoming i ≠ ⊤ := by
    intro i
    induction hlevel : T.level i using Nat.strong_induction_on generalizing i with
    | h k ih =>
        cases hp : T.parent i with
        | none =>
            have hle : incoming i ≤ roots := by
              calc
                incoming i = (if T.parent i = none then incoming i else 0) := by simp [hp]
                _ ≤ roots := by
                  dsimp [roots]
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = none then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
            intro hitop
            apply hroots
            apply top_unique
            simpa [hitop] using hle
        | some p =>
            have hpfinite : incoming p ≠ ⊤ :=
              ih (T.level p) (by simpa [hlevel] using T.parent_level hp) p rfl
            have hchild : incoming i ≤ incoming p := by
              calc
                incoming i =
                    (if T.parent i = some p then incoming i else 0) := by simp [hp]
                _ ≤ Finset.univ.sum (fun j : Fin n =>
                    if T.parent j = some p then incoming j else 0) := by
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
                _ ≤ paid p + leafMass p +
                    Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0) := by
                  simpa using add_le_add_right
                    (show (0 : ENNReal) ≤ paid p + leafMass p from bot_le)
                    (Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0))
                _ = incoming p := by simpa only [hconserve p]
            intro hitop
            apply hpfinite
            apply top_unique
            simpa [hitop] using hchild
  have hnonroots : nonroots ≠ ⊤ := by
    dsimp [nonroots]
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hp : T.parent i = none
    · simp [hp]
    · simp [hp, hincoming_ne_top i]
  have hdouble :
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) = nonroots := by
    rw [Finset.sum_comm]
    dsimp [nonroots]
    apply Finset.sum_congr rfl
    intro j hj
    cases hp : T.parent j with
    | none => simp [hp]
    | some p => simp [hp]
  have hsplit : Finset.univ.sum incoming = roots + nonroots := by
    calc
      Finset.univ.sum incoming = Finset.univ.sum (fun i : Fin n =>
          (if T.parent i = none then incoming i else 0) +
          (if T.parent i = none then 0 else incoming i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        cases hp : T.parent i <;> simp [hp]
      _ = roots + nonroots := by
        rw [Finset.sum_add_distrib]
  have hbalance : roots + nonroots = payments + nonroots := by
    calc
      roots + nonroots = Finset.univ.sum incoming := by simpa only [hsplit]
      _ = Finset.univ.sum (fun i : Fin n =>
            paid i + leafMass i +
              Finset.univ.sum (fun j : Fin n =>
                if T.parent j = some i then incoming j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hconserve i
      _ = payments + nonroots := by
          rw [Finset.sum_add_distrib, hdouble]
  change payments ≤ roots
  apply (ENNReal.add_le_add_iff_right hnonroots).mp
  exact hbalance.ge

/-- On a finite level-decreasing carrier forest, finite root flow gives exact
telescoping: every internal child occurrence is counted once on each side, so
the root flow is exactly the sum of the paid and terminal flows. -/
theorem lossless_edge_flow_exact_of_roots_ne_top
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming : Fin n → ENNReal)
    (paid : Fin n → ENNReal)
    (leafMass : Fin n → ENNReal)
    (hconserve : ∀ i,
      incoming i = paid i + leafMass i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (hroots : Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0) ≠ ⊤) :
    Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0) =
      Finset.univ.sum (fun i : Fin n => paid i + leafMass i) := by
  classical
  let roots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then incoming i else 0)
  let nonroots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then 0 else incoming i)
  let payments : ENNReal := Finset.univ.sum (fun i : Fin n => paid i + leafMass i)
  have hroots' : roots ≠ ⊤ := by simpa [roots] using hroots
  have hincoming_ne_top : ∀ i, incoming i ≠ ⊤ := by
    intro i
    induction hlevel : T.level i using Nat.strong_induction_on generalizing i with
    | h k ih =>
        cases hp : T.parent i with
        | none =>
            have hle : incoming i ≤ roots := by
              calc
                incoming i = (if T.parent i = none then incoming i else 0) := by simp [hp]
                _ ≤ roots := by
                  dsimp [roots]
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = none then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
            intro hitop
            apply hroots'
            apply top_unique
            simpa [hitop] using hle
        | some p =>
            have hpfinite : incoming p ≠ ⊤ :=
              ih (T.level p) (by simpa [hlevel] using T.parent_level hp) p rfl
            have hchild : incoming i ≤ incoming p := by
              calc
                incoming i =
                    (if T.parent i = some p then incoming i else 0) := by simp [hp]
                _ ≤ Finset.univ.sum (fun j : Fin n =>
                    if T.parent j = some p then incoming j else 0) := by
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
                _ ≤ paid p + leafMass p +
                    Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0) := by
                  simpa using add_le_add_right
                    (show (0 : ENNReal) ≤ paid p + leafMass p from bot_le)
                    (Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0))
                _ = incoming p := by simpa only [hconserve p]
            intro hitop
            apply hpfinite
            apply top_unique
            simpa [hitop] using hchild
  have hnonroots : nonroots ≠ ⊤ := by
    dsimp [nonroots]
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hp : T.parent i = none
    · simp [hp]
    · simp [hp, hincoming_ne_top i]
  have hdouble :
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) = nonroots := by
    rw [Finset.sum_comm]
    dsimp [nonroots]
    apply Finset.sum_congr rfl
    intro j hj
    cases hp : T.parent j with
    | none => simp [hp]
    | some p => simp [hp]
  have hsplit : Finset.univ.sum incoming = roots + nonroots := by
    calc
      Finset.univ.sum incoming = Finset.univ.sum (fun i : Fin n =>
          (if T.parent i = none then incoming i else 0) +
          (if T.parent i = none then 0 else incoming i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        cases hp : T.parent i <;> simp [hp]
      _ = roots + nonroots := by
        rw [Finset.sum_add_distrib]
  have hbalance : roots + nonroots = payments + nonroots := by
    calc
      roots + nonroots = Finset.univ.sum incoming := by simpa only [hsplit]
      _ = Finset.univ.sum (fun i : Fin n =>
            paid i + leafMass i +
              Finset.univ.sum (fun j : Fin n =>
                if T.parent j = some i then incoming j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hconserve i
      _ = payments + nonroots := by
          rw [Finset.sum_add_distrib, hdouble]
  have hrootPayment : roots = payments :=
    (ENNReal.add_left_inj hnonroots).mp hbalance
  simpa [roots, payments] using hrootPayment

/-- A finite routing error of at most one half of the root flow is absorbed on
the left, with the sharp harmless factor two on the paid flow. -/
theorem ennreal_half_error_absorption
    (rootFlow paidFlow errorFlow : ENNReal)
    (hrootFinite : rootFlow ≠ ⊤)
    (hidentity : rootFlow = paidFlow + errorFlow)
    (hhalf : errorFlow + errorFlow ≤ rootFlow) :
    rootFlow ≤ paidFlow + paidFlow := by
  have hpaidLe : paidFlow ≤ rootFlow := by
    rw [hidentity]
    exact le_add_right (le_refl paidFlow)
  have herrorLe : errorFlow ≤ rootFlow := by
    rw [hidentity]
    exact le_add_left (le_refl errorFlow)
  have hpaidFinite : paidFlow ≠ ⊤ := ne_top_of_le_ne_top hrootFinite hpaidLe
  have herrorFinite : errorFlow ≠ ⊤ := ne_top_of_le_ne_top hrootFinite herrorLe
  have hpaidTwiceFinite : paidFlow + paidFlow ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hpaidFinite, hpaidFinite⟩
  have herrorTwiceFinite : errorFlow + errorFlow ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨herrorFinite, herrorFinite⟩
  have hidentityReal :
      rootFlow.toReal = paidFlow.toReal + errorFlow.toReal := by
    rw [hidentity, ENNReal.toReal_add hpaidFinite herrorFinite]
  have hhalfReal :
      errorFlow.toReal + errorFlow.toReal ≤ rootFlow.toReal := by
    rw [← ENNReal.toReal_add herrorFinite herrorFinite]
    exact (ENNReal.toReal_le_toReal herrorTwiceFinite hrootFinite).2 hhalf
  apply (ENNReal.toReal_le_toReal hrootFinite hpaidTwiceFinite).1
  rw [ENNReal.toReal_add hpaidFinite hpaidFinite]
  linarith

/-- Approximate nodewise conservation on a finite level-decreasing forest.
The continuing child flow still telescopes exactly; a global half-root error
is then absorbed once, not once per generation. -/
theorem lossless_edge_flow_with_half_error
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminalMass routingError : Fin n → ENNReal)
    (hconservation : ∀ i,
      incoming i = paid i + terminalMass i + routingError i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (hrootsFinite :
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) ≠ ⊤)
    (hhalf :
      Finset.univ.sum (fun i : Fin n => routingError i) +
        Finset.univ.sum (fun i : Fin n => routingError i) ≤
        Finset.univ.sum (fun i : Fin n =>
          if T.parent i = none then incoming i else 0)) :
    Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) ≤
      Finset.univ.sum (fun i : Fin n => paid i + terminalMass i) +
        Finset.univ.sum (fun i : Fin n => paid i + terminalMass i) := by
  have hexact := lossless_edge_flow_exact_of_roots_ne_top T incoming
    (fun i => paid i + terminalMass i) routingError hconservation hrootsFinite
  have hsplit :
      Finset.univ.sum (fun i : Fin n =>
          if T.parent i = none then incoming i else 0) =
        Finset.univ.sum (fun i : Fin n => paid i + terminalMass i) +
          Finset.univ.sum (fun i : Fin n => routingError i) := by
    calc
      Finset.univ.sum (fun i : Fin n =>
          if T.parent i = none then incoming i else 0) =
          Finset.univ.sum (fun i : Fin n =>
            (paid i + terminalMass i) + routingError i) := hexact
      _ = Finset.univ.sum (fun i : Fin n => paid i + terminalMass i) +
          Finset.univ.sum (fun i : Fin n => routingError i) := by
        rw [Finset.sum_add_distrib]
  exact ennreal_half_error_absorption
    (Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0))
    (Finset.univ.sum (fun i : Fin n => paid i + terminalMass i))
      (Finset.univ.sum (fun i : Fin n => routingError i))
      hrootsFinite hsplit hhalf

end StickyKakeya4
