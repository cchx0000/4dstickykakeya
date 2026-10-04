import Theorems.Thm_StickyKakeya4_original_edge_retaining_bsg
import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalSourceEdgeBSG
open OriginalUnequalEdgeRetainingBSG OriginalSeparatedPacking
variable {X : Type*}

def sourceCore (Q : Finset X) (e : X → ℤ × ℤ) (A B : Finset ℤ) : Finset X :=
  Q.filter (fun p => e p∈A.product B)

lemma original_source_core_subset (Q : Finset X) (e : X → ℤ × ℤ) (A B : Finset ℤ) :
    sourceCore Q e A B⊆Q := Finset.filter_subset _ _

/-- The retained integer edges and the pulled-back original source have
exactly the same image. No representative can erase a retained edge. -/
theorem original_source_core_image (Q : Finset X) (e : X → ℤ × ℤ) (A B : Finset ℤ) :
    (sourceCore Q e A B).image e=(Q.image e)∩(A.product B) := by
  ext z
  constructor
  · intro hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hpQ,hpe⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hpQ,hpe⟩
  · intro hz
    obtain ⟨hzQ,hzAB⟩ := Finset.mem_inter.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hzQ
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,hzAB⟩)

theorem original_source_core_query (Q Q' : Finset X) (e : X → ℤ × ℤ) (A B : Finset ℤ)
    (hQ : Q'⊆sourceCore Q e A B) : Q'.image e⊆A.product B := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp (hQ hp)).2

/-- Original point mass and the actual geometric fiber cap produce the
BSG density. The returned core is a literal subset of the original source,
with its admissible mass derived from retained ORIGINAL edges. -/
theorem exists_original_source_edge_bsg (Q : Finset X) (e : X → ℤ × ℤ)
    (A B : Finset ℤ) (q N J M K : ℝ)
    (hq : 0<q) (hN : 0<N) (hJ : 0<J) (hM : 0<M) (hK : 0<K)
    (hQ : q*N≤Q.card) (hA : (A.card:ℝ)≤M) (hB : (B.card:ℝ)≤M)
    (hE : Q.image e⊆A.product B)
    (hfiber : ∀ z∈Q.image e, ((Q.filter (fun p => e p=z)).card:ℝ)≤J)
    (hsum : (((Q.image e).image (fun z => z.1+z.2)).card:ℝ)≤K*M) :
    let lam := q*N/(J*M^2)
    ∃ A' B' : Finset ℤ, A'⊆A ∧ B'⊆B ∧
      (lam^4/4096)*M≤(A'.card:ℝ) ∧ (lam^4/4096)*M≤(B'.card:ℝ) ∧
      ((A'+B').card:ℝ)≤(536870912*K^3/lam^9)*M ∧
      ∃ F : Finset X, F=sourceCore Q e A' B' ∧ F⊆Q ∧
        (lam^4/4096)*M^2≤(F.card:ℝ) ∧
        F.image e=(Q.image e)∩(A'.product B') ∧
        ∀ Q' : Finset X, Q'⊆F → Q'.image e⊆A'.product B' := by
  dsimp only
  let lam := q*N/(J*M^2)
  have hlam : 0<lam := by dsimp [lam]; positivity
  have hcap : (Q.card:ℝ)≤J*(Q.image e).card := card_le_real_mul_image Q e hfiber
  have hdense : lam*M^2≤(Q.image e).card := by
    have he : lam*M^2=q*N/J := by dsimp [lam]; field_simp
    rw [he]
    apply (div_le_iff₀ hJ).mpr
    nlinarith only [hQ,hcap]
  obtain ⟨A',B',hA'A,hB'B,hAc,hBc,hret,hsums⟩ :=
    exists_original_size_normalized_edge_retaining_bsg lam K M hlam hK hM
      A B hA hB (Q.image e) hE hdense hsum
  let F := sourceCore Q e A' B'
  have hid : F.image e=(Q.image e)∩(A'.product B') := original_source_core_image Q e A' B'
  have hmass : (lam^4/4096)*M^2≤(F.card:ℝ) := by
    have hc : ((F.image e).card:ℝ)≤F.card := Nat.cast_le.mpr (Finset.card_image_le)
    rw [hid] at hc
    exact hret.trans hc
  exact ⟨A',B',hA'A,hB'B,hAc,hBc,hsums,F,rfl,original_source_core_subset Q e A' B',
    hmass,hid,fun Q' hQ' => original_source_core_query Q Q' e A' B' hQ'⟩

end OriginalSourceEdgeBSG
