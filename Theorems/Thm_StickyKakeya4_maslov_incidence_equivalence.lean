import Definitions.Def_sticky_kakeya4_core

namespace StickyKakeya4

theorem maslov_incidence_equivalence (A B : Mat3) (s : ℝ)
    (hframe : Function.Injective (fun c : E3 => (A.mulVec c, B.mulVec c))) :
    Matrix.det (pencil A B s) = 0 ↔
      ∃ point : E3 × E3,
        point ∈ graphPlane A B ∧
        point ∈ lagrangianPencil s ∧
        point ≠ 0 := by
  constructor
  · intro hdet
    obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    let cE : E3 := WithLp.toLp 2 c
    let x : E3 := WithLp.toLp 2 (A.mulVec c)
    let y : E3 := WithLp.toLp 2 (B.mulVec c)
    have hcE_ne : cE ≠ 0 := by
      intro hcE
      apply hcne
      have hcE' := congrArg WithLp.ofLp hcE
      simpa [cE] using hcE'
    have hlagVec : B.mulVec c = (-s) • A.mulVec c := by
      simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec] at hc
      calc
        B.mulVec c = -(s • A.mulVec c) := eq_neg_of_add_eq_zero_left hc
        _ = (-s) • A.mulVec c := by simp
    have hlag : y = (-s) • x := by
      apply (WithLp.ext_iff 2).mpr
      simpa [x, y] using hlagVec
    refine Exists.intro (x, y) ?_
    refine And.intro ?_ ?_
    · change ∃ d : E3,
          x.ofLp = A.mulVec d.ofLp ∧ y.ofLp = B.mulVec d.ofLp
      exact ⟨cE, by simp [x, cE], by simp [y, cE]⟩
    · refine And.intro hlag ?_
      intro hzero
      apply hcE_ne
      apply hframe
      apply Prod.ext
      · have hxzero : x = 0 := congrArg Prod.fst hzero
        have hxzero' := congrArg WithLp.ofLp hxzero
        simpa [x, cE] using hxzero'
      · have hyzero : y = 0 := congrArg Prod.snd hzero
        have hyzero' := congrArg WithLp.ofLp hyzero
        simpa [y, cE] using hyzero'
  · rintro ⟨⟨x, y⟩, hgraph, hlag, hpne⟩
    simp only [graphPlane, Set.mem_ofPred_eq] at hgraph
    rcases hgraph with ⟨c, hx, hy⟩
    change y = (-s) • x at hlag
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨c.ofLp, ?_, ?_⟩
    · intro hczero
      have hxzero : x = 0 := by
        apply (WithLp.ext_iff 2).mpr
        calc
          x.ofLp = A.mulVec c.ofLp := hx
          _ = 0 := by simp [hczero]
      have hyzero : y = 0 := by
        apply (WithLp.ext_iff 2).mpr
        calc
          y.ofLp = B.mulVec c.ofLp := hy
          _ = 0 := by simp [hczero]
      apply hpne
      simp [hxzero, hyzero]
    · simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec]
      have hlagVec : B.mulVec c.ofLp = (-s) • A.mulVec c.ofLp := by
        have hlag' := congrArg WithLp.ofLp hlag
        simpa [hx, hy] using hlag'
      rw [hlagVec]
      module

end StickyKakeya4
