module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.ClozelPurityOfBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Purity
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem purity : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) → ∃ w₀ : ℤ, ∀ τ : E →+* ℂ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z := by
  intro hB E _ _ _ a ha π hinf hint
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_right_haar_measure E a
  haveI := h1
  haveI := h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.aux_statement_20 E a ha π hinf
  obtain ⟨B, hH⟩ := GlobalTheory.T.exists_invariant_hermitian_form hB E a μ (π.twist (GlobalTheory.CuspRep.Model.absC E s)) hs
  have hm : ∀ τ, π.HasInfChar τ ((CG.mk π).infChar τ) := fun τ => by
    obtain ⟨m, h⟩ := hinf τ
    have e : (CG.mk π).infChar τ = m := CG.HasInfChar.infChar_eq (π := CG.mk π) h
    rw [e]
    exact h
  have hreal : ∀ τ, ∀ z ∈ (CG.mk π).infChar τ, (starRingEnd ℂ) z = z := fun τ z hz => by
    obtain ⟨n, rfl⟩ := hint τ z hz
    have c2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    simp [c2]
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => (-(starRingEnd ℂ) s - s) - z := fun τ => by
    have t1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    have t2 := (hm (NumberField.ComplexEmbedding.conjugate τ)).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at t1 t2
    have e := GlobalTheory.T.infinitesimal_character_conjugate E a _ B hH τ _ _ t1 t2
    have e2 := congrArg (Multiset.map fun z => z - s) e
    simp only [Multiset.map_map, Function.comp_def, add_sub_cancel_right, Multiset.map_id'] at e2
    rw [e2]
    refine Multiset.map_congr rfl fun z hz => ?_
    rw [map_add (f := _), hreal τ z hz]
    ring
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ₀ := by
    apply Multiset.card_pos_iff_exists_mem.1
    rw [CG.card_infChar]
    exact ha
  have hz' : (-(starRingEnd ℂ) s - s) - z ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ₀) := by
    rw [key]
    exact Multiset.mem_map_of_mem _ hz
  obtain ⟨n, hn⟩ := hint _ z hz
  obtain ⟨n', hn'⟩ := hint _ _ hz'
  refine ⟨n + n' + (a : ℤ) - 1, fun τ => ?_⟩
  have e : (-(starRingEnd ℂ) s - s) = (((n + n' + (a : ℤ) - 1 : ℤ)) : ℂ) := by
    push_cast
    linear_combination hn' + hn
  have e2 : (starRingEnd ℂ).comp τ = NumberField.ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl
  rw [e2, key, e]

end GlobalTheory.CompanionTheory.ClozelPurity
end

open NumberField GlobalTheory.CuspRep

namespace PositivityTheory.S2.Clozel

theorem clozelPurity_of_bounded : GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.ClozelPurity :=
  fun hB E _ _ _ a ha π h =>
    GlobalTheory.CompanionTheory.ClozelPurity.purity hB E a ha π (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ⟩) h

end PositivityTheory.S2.Clozel
end

namespace PositivityTheory.Lit1.ClozelPurity

theorem clozelPurity : GlobalTheory.Published.ClozelPurity :=
  PositivityTheory.S2.Clozel.clozelPurity_of_bounded GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL

end PositivityTheory.Lit1.ClozelPurity
