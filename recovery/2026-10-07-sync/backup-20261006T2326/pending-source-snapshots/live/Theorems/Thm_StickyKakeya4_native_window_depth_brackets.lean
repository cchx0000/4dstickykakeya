import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace NativeWindowDepthBrackets
open Classical Finset

/-- A fixed finite depth menu brackets every intermediate dyadic depth.
Repeated entries are allowed. Both distances to the selected tests are
bounded by the original maximum adjacent gap. -/
theorem bracket_depth (J first last gap : ℕ) (depth : Fin (J+1) → ℕ)
    (hfirst : depth 0=first) (hlast : depth (Fin.last J)=last)
    (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ gap)
    (m : ℕ) (hfm : first ≤ m) (hml : m ≤ last) :
    ∃lo hi : Fin (J+1), depth lo ≤ m ∧ m ≤ depth hi ∧
      m-depth lo ≤ gap ∧ depth hi-m ≤ gap := by
  by_cases he : m=last
  · refine ⟨Fin.last J,Fin.last J,?_,?_,?_,?_⟩ <;> rw [hlast,he] <;> omega
  · have hstrict : m < last := lt_of_le_of_ne hml he
    let A := univ.filter (fun j : Fin (J+1) => depth j ≤ m)
    have hA : A.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,by simpa only [hfirst] using hfm⟩⟩
    obtain ⟨j,hj,hmax⟩ := exists_max_image A (fun j => j.val) hA
    have hjm := (mem_filter.mp hj).2
    have hjJ : j.val < J := by
      by_contra hn
      have heq : j=Fin.last J := by
        apply Fin.ext
        change j.val=J
        have hh := j.isLt
        omega
      rw [heq,hlast] at hjm
      omega
    let i : Fin J := ⟨j.val,hjJ⟩
    have hij : i.castSucc=j := Fin.ext rfl
    have him : depth i.castSucc ≤ m := by simpa only [hij] using hjm
    have hmi : m ≤ depth i.succ := by
      by_contra hn
      have hiA : i.succ∈A := mem_filter.mpr ⟨mem_univ _,by omega⟩
      have hh := hmax i.succ hiA
      dsimp [i] at hh
      omega
    have hg := hgap i
    exact ⟨i.castSucc,i.succ,him,hmi,by omega,by omega⟩

/-- The selected depth bracket gives exact integer scale factors, rather
than rounding or selecting a different source. -/
theorem dyadic_factors (last lo middle hi gap : ℕ)
    (hlo : lo ≤ middle) (hmid : middle ≤ hi) (hhi : hi ≤ last)
    (hgaplo : middle-lo ≤ gap) (hgaphigh : hi-middle ≤ gap) :
    2^(last-hi)*2^(hi-middle)=(2:ℕ)^(last-middle) ∧
    2^(last-middle)*2^(middle-lo)=(2:ℕ)^(last-lo) ∧
    (2:ℕ)^(hi-middle) ≤ 2^gap ∧ (2:ℕ)^(middle-lo) ≤ 2^gap := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [←pow_add]
    congr 1
    omega
  · rw [←pow_add]
    congr 1
    omega
  · exact Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hgaphigh
  · exact Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hgaplo

end NativeWindowDepthBrackets
