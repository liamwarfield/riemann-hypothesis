module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.AdmUnitary

theorem admissible_and_kFin_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  intro n ε H _ _ _ σ hσ hirr
  refine ⟨fun S hS hst v hv => ?_, fun v hv => CompanionTheory.D.gk.admitted.kFin_smooth n ε H σ hσ hirr v hv⟩
  obtain ⟨Y, hY, -, hvY, hT⟩ := CompanionTheory.D.gk.admitted.unitary_group_admissible n ε H σ hσ hirr S hst v hv
  exact ⟨Y, hY, hvY, hT⟩

end GlobalTheory.AdmUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_K_stable_finite_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  first | exact @GlobalTheory.AdmUnitary.admissible_and_kFin_smooth | exact GlobalTheory.AdmUnitary.admissible_and_kFin_smooth | (intros; apply GlobalTheory.AdmUnitary.admissible_and_kFin_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory.LocalResidue

theorem card_residue_of_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  intro F _ _ v k _ _ _ _ φ hφ
  let ψ : 𝒪[k] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun a => ⟨φ a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((hφ a).2 a.2)⟩
      invFun := fun b => ⟨φ.symm b, (hφ _).1 (by
        rw [RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (φ.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (φ.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : k) (b : k))
      map_add' := fun a b => Subtype.ext (map_add φ (a : k) (b : k)) }
  have e := IsLocalRing.ResidueField.mapEquiv ψ
  have hF : ∀ s : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  have hc := GlobalTheory.SplitUnif.card_residueField v (algebraMap F (v.adicCompletion F)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nat.card_congr e.toEquiv, hc]

end GlobalTheory.LocalResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletionStatement
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.LocalResidue.card_residue_of_ringEquiv | exact GlobalTheory.LocalResidue.card_residue_of_ringEquiv | (intros; apply GlobalTheory.LocalResidue.card_residue_of_ringEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

theorem dense_finite_vectors (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : K →* H →L[ℂ] H)
    (hiso : ∀ k x, ‖π k x‖ = ‖x‖) (hcont : ∀ x, Continuous fun k => π k x) :
    Dense {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
      ∀ k, ∀ x ∈ S, π k x ∈ S} := by
  let N : Submodule ℂ H :=
    { carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, π k x ∈ S}
      add_mem' := by
        rintro a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩
        refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
        intro k x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)
      zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
        intro k x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨S, hS, ha, hSs⟩
        exact ⟨S, hS, S.smul_mem c ha, hSs⟩ }
  have hNst : ∀ k, ∀ a ∈ N, π k a ∈ N := by
    rintro k a ⟨S, hS, ha, hSs⟩
    exact ⟨S, hS, hSs k a ha, hSs⟩
  have hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ := fun k a b =>
    (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b
  have hinv : ∀ k a, π k (π k⁻¹ a) = a := by
    intro k a
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ := by
    intro k w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro a ha
    rw [← hinv k a, hinner]
    exact hw _ (hNst _ a ha)
  have hbot : Nᗮ = ⊥ := by
    by_contra hne
    haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
    let ρ : K →* (Nᗮ →L[ℂ] Nᗮ) :=
      { toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro k l
          ext w
          show π (k * l) w = π k (π l w)
          rw [map_mul, ContinuousLinearMap.mul_apply] }
    have hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w := fun k w => rfl
    obtain ⟨S, hS0, hSf, hSs⟩ := exists_finiteDimensional_invariant K Nᗮ ρ
      (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)
    apply hS0
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwN : (w : H) ∈ N := by
      refine ⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩
      rintro k x ⟨y, hy, rfl⟩
      exact ⟨ρ k y, hSs k y hy, rfl⟩
    have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 w.2 _ hwN
    exact Subtype.ext (inner_self_eq_zero.1 h0)
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hbot)

theorem dense_isKFin (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hσ
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology
  have hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε := fun k => k.1.2
  let π : Formalism.REAL.KG ε →* (H →L[ℂ] H) :=
    { toFun := fun k => σ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ (hU k) _ (hU l) }
  have hd := dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x)
    (fun x => (hcont x).comp_continuous hemb.continuous hU)
  refine hd.mono ?_
  rintro v ⟨S, hS, hv, hSs⟩
  refine ⟨S, hS, hv, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k, rfl⟩ := hg
  exact hSs k x hx

end GlobalTheory.CompactRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRepStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  first | exact @GlobalTheory.CompactRep.dense_isKFin | exact GlobalTheory.CompactRep.dense_isKFin | (intros; apply GlobalTheory.CompactRep.dense_isKFin <;> assumption)
end
end
