module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.SmulListSum

private theorem smul_list_sum {U : Type u_1} [AddCommGroup U] [Module Complex U]
    (c : Complex) (l : List U) : c • l.sum = (l.map (fun w => c • w)).sum := by
  induction l with
  | nil => simp only [List.sum_nil, List.map_nil, smul_zero]
  | cons a t ih => simp only [List.sum_cons, List.map_cons, smul_add, ih]

theorem goal1 :
    ∀ {U : Type u_1} [inst : AddCommGroup U] [inst_1 : _root_.Module ℂ U] {G : Set U},
      (∀ w ∈ G, ∀ (c : ℂ), c • w ∈ G) →
        ∀ {y : U}, y ∈ Submodule.span ℂ G → ∃ (l : List U), (∀ w ∈ l, w ∈ G) ∧ y = l.sum := by
  intro U _ _ G hG y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    refine ⟨[x], ?_, ?_⟩
    · intro w hw
      rw [List.mem_singleton] at hw
      rw [hw]; exact hx
    · simp only [List.sum_cons, List.sum_nil, add_zero]
  | zero => exact ⟨[], fun w hw => absurd hw (List.not_mem_nil), by simp only [List.sum_nil]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨la, hla, rfl⟩ := iha
    obtain ⟨lb, hlb, rfl⟩ := ihb
    refine ⟨la ++ lb, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hla w h
      · exact hlb w h
    · rw [List.sum_append]
  | smul c a _ iha =>
    obtain ⟨la, hla, rfl⟩ := iha
    refine ⟨la.map (fun w => c • w), ?_, smul_list_sum c la⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hG v (hla v hv) c

end Bl.SmulListSum
