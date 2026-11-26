module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ConsMemUniMIffMapSubSmul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem SeqCx.exactAt_of_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
    (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S hF p h c hc hcb
  have hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q := by
    intro q
    apply Finsupp.supported_mono
    rintro l ⟨⟨_, hl⟩, hlen⟩
    exact ⟨by simpa using hl, hlen⟩
  by_cases h0 : ([] : List V) ∈ F
  · obtain ⟨b, hb, hcb', hcyc⟩ :=
      T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb
    obtain ⟨b', hb', hbd⟩ := h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc
    refine ⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩
    rw [map_add (f := _), hbd]
    abel
  · have hFe : ∀ l, l ∉ F := fun l hl => h0 (hF l hl [] (List.nil_sublist l))
    have hc0 : c = 0 := by
      have : {l : List V | l ∈ F ∧ l.length = p} = ∅ := by
        ext l
        simp [hFe l]
      have hc' := hc
      simp only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'
      exact hc'
    exact ⟨0, Submodule.zero_mem _, by simp [hc0]⟩

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqComplex_exactAt_of_all_links_exactAt : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_of_links
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkInUniMEqShorterOfFormEqOne
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem linkIn_uniM_eq_of_form :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M),
      (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 →
        ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧
          linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  intro R M _ _ _ φ S hS τ hτ v hv hφv
  classical
  have hperm := (GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.1
  have hmod := GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul R M φ v hφv
  have hp : τ.Perm (v :: τ.erase v) := List.perm_cons_erase hv
  refine ⟨(τ.erase v).map (fun x => x - φ x • v), ?_, ?_, ?_⟩
  · exact (hmod _).1 (hperm _ _ hp hτ)
  · simp [List.length_erase_of_mem hv]
    have := List.length_pos_of_mem hv
    omega
  · ext w
    simp only [linkIn, Set.mem_setOf_eq]
    refine and_congr_right fun hw => ?_
    have hpw : (τ ++ w).Perm (v :: (τ.erase v ++ w)) := hp.append_right w
    have hwfix : w.map (fun x => x - φ x • v) = w := by
      conv_rhs => rw [← List.map_id w]
      apply List.map_congr_left
      intro x hx
      simp [hS x (hw x hx)]
    constructor
    · intro h
      have h1 := (hmod _).1 (hperm _ _ hpw h)
      rwa [List.map_append, hwfix] at h1
    · intro h
      have h1 : (τ.erase v ++ w).map (fun x => x - φ x • v) ∈ uniM R M := by
        rwa [List.map_append, hwfix]
      exact hperm _ _ hpw.symm ((hmod _).2 h1)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.linkIn_uniM_eq_shorter_of_form_eq_one : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M), (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 → ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧ linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_uniM_eq_of_form
end
end
