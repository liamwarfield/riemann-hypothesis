module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex
noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic Finset

theorem gam_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (g x : GL (Fin k) F) :
    gam ψ₀ (g * x * g⁻¹) = gam ψ₀ x := by
  unfold gam
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun y => psiNat ψ₀ (y * x * y⁻¹))]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group

theorem representation_commutes_gamma : RepGamComm := by
  intro F _ _ k ψ₀ V _ _ π g
  apply LinearMap.ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [repGam, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have hm : ∀ a b : GL (Fin k) F, π a (π b v) = π (a * b) v := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  simp only [hm]

  rw [← Equiv.sum_comp (MulAut.conj g).toEquiv (fun x => gam ψ₀ x • π (x * g) v)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [gam_conj]
  congr 2
  group

theorem representation_conjugation_apply {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V) (y x : GL (Fin k) F) (v : V) :
    π y⁻¹ (π (y * x * y⁻¹) (π y v)) = π x v := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_conjugate_gamma : RepGamConj := by
  intro F _ _ k ψ₀ V _ _ π
  apply LinearMap.ext
  intro v
  have hR : ∀ y : GL (Fin k) F, ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) v =
      ∑ z, ((cardU F k : ℂ)⁻¹ * psiNat ψ₀ (y * z * y⁻¹)) • π z v := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [projQ, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    rw [← Equiv.sum_comp (MulAut.conj y).toEquiv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [representation_conjugation_apply, smul_smul]
  simp only [repGam, gam, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun y _ => hR y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]

theorem trace_representation_gamma : TraceRepGam := by
  intro F _ _ k ψ₀ V _ _ _ π
  set_option synthInstance.maxHeartbeats 100000 in
    rw [representation_conjugate_gamma F k ψ₀ V π, map_sum]

  have h : ∀ y : GL (Fin k) F,
      LinearMap.trace ℂ V ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) = LinearMap.trace ℂ V (projQ ψ₀ π) := by
    intro y
    show LinearMap.trace ℂ V (π y⁻¹ * (projQ ψ₀ π * π y)) = _
    rw [LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PI.GGConvScalarW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.RepresentationDimensionPos
noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  congr 1
  exact Subsingleton.elim a b

theorem representation_dimension_pos : DimPos := by
  intro F _ _ k V _ _ _ π hπ
  haveI := nontrivial_of_irreducible π hπ
  exact Module.finrank_pos

theorem schur_lemma_complex : SchurC := by
  intro F _ _ k V _ _ _ π hπ f hf
  haveI := nontrivial_of_irreducible π hπ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) →
      π g v ∈ LinearMap.ker (f - c • LinearMap.id) := by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
    have h1 := congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← map_smul, ← map_sub, hv, map_zero]
  let W : Subrepresentation π := ⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rcases hs.eq_bot_or_eq_top W with hW | hW
  · exfalso
    apply hv.2
    have hvW : v ∈ LinearMap.ker (f - c • LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul, sub_self]
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    rw [h2] at hvW
    have h3 : v ∈ (⊥ : Submodule ℂ V) := hvW
    simpa using h3
  · apply LinearMap.ext
    intro x
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    have hx : x ∈ LinearMap.ker (f - c • LinearMap.id) := by
      rw [h2]
      exact (show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa [sub_eq_zero] using hx

end PI.GGConvScalarW
end
end
