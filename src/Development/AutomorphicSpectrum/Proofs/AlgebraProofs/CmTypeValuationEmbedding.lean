module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsMonogenicSeparating
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSpanIntersectionBasis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationLatticeMatrixReduction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelf
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelf
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig

theorem sum_embeddings_eq_trace (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* C, s x = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  classical
  let Ω := AlgebraicClosure C
  let f : (E →+* C) → (E →ₐ[ℚ] Ω) := fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)
  have hf : ∀ s y, f s y = algebraMap C Ω (s y) := fun s y => rfl
  have hinj : Function.Injective f := by
    intro s t hst
    ext y
    have h := congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst
    simp only [hf] at h
    exact (algebraMap C Ω).injective h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hc, AlgHom.card]⟩
  have key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x :=
    trace_eq_sum_embeddings Ω (x := x)
  rw [← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)] at key
  simp only [hf] at key
  apply (algebraMap C Ω).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]

theorem sum_eigProj (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M) :
    ∑ s, HT.eigProj ρ s y = y := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    calc (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      _ = algebraMap (𝓞 E) E (∑ j, b.repr 1 j • b j) := by rw [b.sum_repr]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    calc Algebra.trace ℚ E (HT.dualInt E k) = Algebra.traceForm ℚ E (HT.dualInt E k) 1 := by
          rw [Algebra.traceForm_apply, mul_one]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by
          conv_lhs => rw [h1]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ((b.repr 1 k : ℤ) : ℚ) := by
          simp only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C) := by
    intro k
    rw [sum_embeddings_eq_trace E C hc, htr, map_intCast]
  calc ∑ s, HT.eigProj ρ s y = ∑ s : E →+* C, ∑ k, s (HT.dualInt E k) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [HT.eigProj]
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hb]
    _ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsum]
    _ = ρ (∑ k, b.repr 1 k • b k) y := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    _ = y := by
        rw [b.sum_repr, map_one, Module.End.one_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEigenProjectionsEqSelfStatement
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_eigen_projections_eq_self : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [Fintype (E →+* C)], Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M), ∑ s, HT.eigProj ρ s y = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenAction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenAction
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank

theorem comp_eigProj_eq {E : Type} [Field E] [NumberField E] {C : Type} [Field C]
    [Fintype (E →+* C)] {W : Type} [AddCommGroup W] [Module C W]
    {ρ : 𝓞 E →+* Module.End C W} {s' : E →+* C}
    (hsum : ∀ y, ∑ t, HT.eigProj ρ t y = y) {φ : Module.Dual C W}
    (hφ : ∀ a : 𝓞 E, φ ∘ₗ ρ a = s' (a : E) • φ) :
    φ ∘ₗ HT.eigProj ρ s' = φ := by
  classical
  ext y
  have key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0 := by
    intro t ht
    have hmem := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)
    have hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E) := by
      by_contra hc
      push_neg at hc
      exact ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
    obtain ⟨a, ha⟩ := hex
    have h1 := LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hmem a, map_smul, smul_eq_mul] at h1
    have h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
  have e : φ y = φ (HT.eigProj ρ s' y) := by
    conv_lhs => rw [← hsum y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]
  exact e.symm

theorem finrank_eigSp_inf_ker_fst :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  intro E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH
  set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU
  set T := HT.eigSp ρ s' with hT
  let F : U →ₗ[C] Module.Dual C T :=
    T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype
  have hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x := fun _ _ => rfl
  have hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0 := fun u => u.2.2
  have hact : ∀ u : U, ∀ a : 𝓞 E,
      (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2 := by
    intro u a
    have h1 := HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)
    have h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2) :=
      Prod.ext (hfst u) rfl
    rw [h2, hH, hbar] at h1
    have h3 := congrArg Prod.snd h1
    simpa [hs a] using h3
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := comp_eigProj_eq hsum (hact u)
    apply Subtype.ext
    refine Prod.ext (hfst u) ?_
    rw [← h0]
    ext y
    have := hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩
    rw [hu] at this
    simpa using this.symm
  have hsurj : Function.Surjective F := by
    intro ψ
    let e : W →ₗ[C] T := LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')
    have he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x := fun b x =>
      Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)
    have hmem : ((0 : W), ψ ∘ₗ e) ∈ U := by
      refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩
      rw [hH]
      refine Prod.ext (by simp) ?_
      ext x
      simp [he, hs, hbar]
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    rw [hFapply]
    have : e x = x := Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)
    simp [this]
  rw [(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenActionStatement
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_module_conjugate_eigen_action : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLatticeDualEigenDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLatticeDualEigenDecomposition
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil

section
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {W : Type} [AddCommGroup W]
  [Module C W]

theorem eigProj_comp_bar [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C)
    (ρ : 𝓞 E →+* Module.End C W) (hsum : ∀ y, ∑ s, HT.eigProj ρ s y = y)
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hbar : ∀ a, bar (bar a) = a) (x : W) :
    HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ x = HT.eigProj ρ σ' x := by
  classical
  conv_lhs => rw [← hsum x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single σ']
  · apply HT.LatBasic.eigProj_of_mem
    rw [HT.LatBasic.mem_eigSp]
    intro a
    have h := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ' x) (bar a)
    rw [hσ, hbar] at h
    exact h
  · intro s _ hs
    refine HT.LatBasic.eigProj_of_eigenSub_ne
      (χ := (s.comp (algebraMap (𝓞 E) E)).comp (bar : 𝓞 E →+* 𝓞 E)) ?_ ?_
    · intro e
      apply hs
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      refine RingHom.ext fun a => ?_
      have h := DFunLike.congr_fun e (bar a)
      have h2 : σ ((bar a : 𝓞 E) : E) = s (a : E) := by
        simpa [hbar] using h
      change s (a : E) = σ' (a : E)
      rw [hσ, h2]
    · rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ s x) (bar a)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eigProj_zero_form (bar : 𝓞 E ≃+* 𝓞 E) (σ : E →+* C) (ρ : 𝓞 E →+* Module.End C W)
    (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
    (hact : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) (φ : Module.Dual C W) :
    HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ) := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hact]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · ext x
    simp [Prod.snd_sum, LinearMap.sum_apply]

end

theorem span_iff_proj : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  intro E _ _ V C _ _ _ _ bar σ σ' W _ _ _ _ ρ ρH HV Lie n w ψ hsum hσ hbar _ hact hlat hspan hwL hψ hint y
  classical

  have hform : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj ρ σ') := by
    intro φ
    rw [eigProj_zero_form bar σ ρ ρH hact φ]
    refine Prod.ext rfl ?_
    ext x
    simp only [LinearMap.comp_apply]
    rw [eigProj_comp_bar bar σ σ' ρ hsum hσ hbar x]
  have hψe : ∀ j, ψ j = (0, (ψ j).2) := fun j => Prod.ext (hψ j).2.1 rfl

  have hχ : ∀ j x, (ψ j).2 x = (ψ j).2 (HT.eigProj ρ σ' x) := by
    intro j x
    have h := HT.LatBasic.eigProj_of_mem (hψ j).1
    rw [hψe j, hform] at h
    have h2 := congrArg (fun z : W × Module.Dual C W => z.2 x) h
    exact h2.symm

  have hexp : ∀ x, HT.eigProj ρ σ' x = ∑ j, (ψ j).2 x • w j := by
    intro x
    have hm : HT.eigProj ρ σ' x ∈ Submodule.span C (Set.range w) := by
      rw [hspan]; exact HT.LatBasic.eigProj_mem ρ σ' x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hm
    have hcj : ∀ j, (ψ j).2 x = c j := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hχ j x, ← hc, map_sum]
      simp [(hψ j).2.2]
    simp only [hcj]
    exact hc.symm

  have key : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = ∑ j, φ (w j) • ψ j := by
    intro φ
    rw [hform]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, (hψ _).2.1]
    · ext x
      simp only [LinearMap.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp x, map_sum, Prod.snd_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]

  have hsm : ∀ (v : V) (z : W × Module.Dual C W), v • z = algebraMap V C v • z := by
    intro v z
    refine Prod.ext ?_ ?_
    · simp
    · ext x
      simp [Algebra.smul_def]
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hy
    choose φ hφ1 hφ2 using hint
    refine ⟨∑ j, algebraMap V C (c j) • φ j, ?_, ?_⟩
    · rw [hlat]
      intro e he
      rw [LinearMap.sum_apply]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨c j, rfl⟩ (hφ1 j e he)
    · rw [key]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (∑ j, algebraMap V C (c j) • φ j) (w k) = algebraMap V C (c k) := by
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hφ2, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsm, hk]
  · rintro ⟨φ, h0, rfl⟩
    rw [key]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨v, hv⟩ := (hlat φ).1 h0 (w j) (hwL j)
    rw [← hv, ← hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLatticeDualEigenDecompositionStatement
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_dual_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEmbeddingsValuationRankBound
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEmbeddingsValuationRankBound
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red

section Xfer

variable {A B K M : Type} [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]

def xfer (h : (algebraMap A K).range = (algebraMap B K).range) (X : Submodule A M) : Submodule B M where
  carrier := X
  zero_mem' := X.zero_mem
  add_mem' := fun hx hy => X.add_mem hx hy
  smul_mem' := fun c x hx => by
    obtain ⟨a, ha⟩ : algebraMap B K c ∈ (algebraMap A K).range := h ▸ ⟨c, rfl⟩
    have e : c • x = a • x := by rw [← algebraMap_smul K c x, ← ha, algebraMap_smul]
    rw [e]
    exact X.smul_mem a hx

theorem mem_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {X : Submodule A M} {y : M} :
    y ∈ xfer h X ↔ y ∈ X := Iff.rfl

theorem xfer_span (h : (algebraMap A K).range = (algebraMap B K).range) (s : Set M) :
    xfer h (Submodule.span A s) = Submodule.span B s := by
  apply le_antisymm
  · intro y hy
    exact (Submodule.span_le (p := xfer h.symm (Submodule.span B s))).2
      (fun z hz => Submodule.subset_span hz) hy
  · exact Submodule.span_le.2 fun z hz => Submodule.subset_span hz

end Xfer

section XferEig

variable {A B K M : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]
  {E : Type} [Field E] [NumberField E]

theorem xfer_eigSub (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigSub ρ σ X) = HT.eigSub ρ σ (xfer h X) := by
  ext y
  exact Iff.rfl

theorem xfer_eigQuot (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigQuot ρ σ X) = HT.eigQuot ρ σ (xfer h X) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isFreeOn_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {ρ : 𝓞 E →+* Module.End K M}
    {X : Submodule A M} {N : ℕ} {t : Fin N → M} (hf : HT.IsFreeOn ρ X t) :
    HT.IsFreeOn ρ (xfer h X) t := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  rw [← xfer_span h, ← hf.2.2]

end XferEig

theorem targetV : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  intro hO E _ _ V C _ _ _ _ _ _ _ bar σ σ' rk p q ν hν hℓ hs hcard hσ' hbar
  have hr : (algebraMap V C).range = (algebraMap ν.valuationSubring C).range := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨_, (Valuation.mem_valuationSubring_iff _ _).2 (hν.map_le_one a)⟩, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨a, ha⟩ := hν.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 o.2)
      exact ⟨a, ha⟩
  obtain ⟨γ, hγ, H⟩ := hO E C ν bar σ σ' rk p q hℓ (fun s a => by
    obtain ⟨o, ho⟩ : s (a : E) ∈ (algebraMap ν.valuationSubring C).range := hr ▸ hs s a
    rw [← ho]
    exact o.2) hcard hσ' hbar
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  letI : Module ν.valuationSubring W := Module.compHom W (algebraMap ν.valuationSubring C)
  haveI : IsScalarTower ν.valuationSubring C W := ⟨fun o c y => by
    change ((o : C) * c) • y = (o : C) • (c • y)
    rw [mul_smul]⟩
  obtain ⟨ε, hε⟩ := H W ρ ρH (xfer hr HV) (xfer hr Lie) x v w u A h1 h2
    (by
      ext y
      rw [mem_xfer, ← h3]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩)
    (fun φ => by
      rw [mem_xfer, h4, ← hr]
      exact Iff.rfl)
    (isFreeOn_xfer hr h5) h6 h7
    (by rw [← xfer_span hr, h8, xfer_eigSub]) h9
    (by rw [← xfer_span hr, h10, xfer_eigSub]) h11 h12
    (by rw [← xfer_span hr, h13, xfer_eigQuot])
  obtain ⟨a, ha⟩ : algebraMap ν.valuationSubring C (ε : ν.valuationSubring) ∈ (algebraMap V C).range :=
    hr ▸ ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : algebraMap ν.valuationSubring C ((ε⁻¹ : (ν.valuationSubring)ˣ) : ν.valuationSubring) ∈
      (algebraMap V C).range := hr ▸ ⟨_, rfl⟩
  have hab : a * b = 1 := by
    apply hν.hom_inj
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  rw [hε]
  exact congrArg (· * γ) ha.symm

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEmbeddingsValuationRankBoundStatement
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_valuation_rank_bound : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOne
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOne
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem block_monogenic_of_residual_character : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  exact @PositivityTheory.Xgn.exists_monogenic_separating

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOneStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_unavailable_one : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | exact GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypeValuationEmbedding
open scoped NNReal
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem targetO : TargetO := by
  intro E _ _ C _ _ ν bar σ σ' rk p q hℓ hint hcard hσ' hbar
  classical
  obtain ⟨ℓ, h0, h1⟩ := hℓ
  haveI : Finite (E →+* C) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* C) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* C) = Module.finrank ℚ E := by rw [← Nat.card_eq_fintype_card, hcard]
  have hsumAll := GlobalTheory.T.sum_eigen_projections_eq_self E C hcard'
  let emb : (E →+* C) → (𝓞 E →+* ν.valuationSubring) := fun s =>
    (s.comp (algebraMap (𝓞 E) E)).codRestrict ν.valuationSubring (fun a => hint s a)
  have hemb : ∀ s (a : 𝓞 E), ((emb s a : ν.valuationSubring) : C) = s (a : E) := fun s a => rfl
  obtain ⟨π, hπ1, hπ2⟩ := GlobalTheory.T.statement_unavailable_one E ν.valuationSubring C emb (fun s a => hemb s a) hcard σ
  let D : (E →+* C) → Prop := fun s => ∀ a, ¬ IsUnit (emb s a - emb σ a)
  let S := {s // D s}
  have hDσ : D σ := fun a => by simp
  let τ : S := ⟨σ, hDσ⟩
  let a : S → ν.valuationSubring := fun s => emb s.1 π
  have ha : Function.Injective a := fun s s' e => Subtype.ext (hπ1 _ _ s.2 s'.2 e)
  have hmono : ∀ f : (E →+* C) → ν.valuationSubring, (∀ s, ¬ D s → f s = 0) →
      ((∃ g : Polynomial ν.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔
        f ∈ Submodule.span ν.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
    intro f hf
    refine hπ2 f (fun s hs => hf s ?_)
    intro hd
    obtain ⟨b, hb⟩ := hs
    exact hd b hb

  have hbarE : ∀ s : E →+* C, ∃ s' : E →+* C, ∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E) := by
    intro s
    have hinj : Function.Injective ((s.comp (algebraMap (𝓞 E) E)).comp bar.toRingHom) := by
      refine (s.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)).comp bar.injective
    exact ⟨IsFractionRing.lift hinj, fun a => IsFractionRing.lift_algebraMap hinj a⟩
  choose sbar hsbar using hbarE
  let r : S → ℕ := fun s => rk (sbar s.1)
  let P : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))
  have hne : ∀ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ≠ 0 := by
    intro s hs e
    have : a τ = a s := Subtype.ext (sub_eq_zero.1 e)
    exact (Finset.mem_erase.1 hs).1 (ha this).symm
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  let Q : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hne s hs)
  refine ⟨Q / P ^ (p + q), div_ne_zero hQ (pow_ne_zero _ hP), ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A hfst hinr hmap hfil hfree hrk hv hvs hw hws had hAl hAs
  have hIv : ν.Integers ν.valuationSubring :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => x.2
      exists_of_le_one := fun {r} h => ⟨⟨r, h⟩, rfl⟩ }
  have hsumW := hsumAll W ρ
  have hsumH := hsumAll _ ρH

  have fstE : ∀ (s : E →+* C) (y : W × Module.Dual C W), (HT.eigProj ρH s y).1 = HT.eigProj ρ s y.1 := by
    intro s y
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hfst]
  let T : S → (Fin (p + q) → C) →ₗ[C] (W × Module.Dual C W) := fun s => eigCoord ρH x s.1
  let g : S → (Fin (p + q) → C) →ₗ[C] W := fun s => (LinearMap.fst C W (Module.Dual C W)) ∘ₗ T s
  have hgT : ∀ s y, g s y = (T s y).1 := fun s y => rfl
  have Tmem : ∀ s y, T s y ∈ HT.eigSp ρH s.1 := by
    intro s y
    change eigCoord ρH x s.1 y ∈ _
    rw [eigCoord_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem _ _ _)
  have gmem : ∀ s y, g s y ∈ HT.eigSp ρ s.1 := by
    intro s y
    rw [HT.LatBasic.mem_eigSp]
    intro b
    rw [hgT, ← hfst, HT.LatBasic.mem_eigSp.1 (Tmem s y) b]
    rfl
  have Tinj : ∀ s, Function.Injective (T s) := by
    intro s
    have hli := HodgeDeterminantLattice.linearIndependent_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    change eigCoord ρH x s.1 y = 0 at hy
    rw [eigCoord_apply] at hy
    exact funext (Fintype.linearIndependent_iff.1 hli y hy)
  have Tsurj : ∀ s y, y ∈ HT.eigSp ρH s.1 → ∃ z, T s z = y := by
    intro s y hy
    have hsp := HodgeDeterminantLattice.span_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← hsp] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hy
    exact ⟨c, by change eigCoord ρH x s.1 c = y; rw [eigCoord_apply]; exact hc⟩

  have projSum : ∀ (f : S → Fin (p + q) → C) (t : S), HT.eigProj ρH t.1 (∑ s, T s (f s)) = T t (f t) := by
    intro f t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single t]
    · exact HT.LatBasic.eigProj_of_mem (Tmem _ _)
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (Tmem _ _)
    · simp
  have hind : ∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0 := by
    intro f hf t
    have h2 := congrArg (HT.eigProj ρ t.1) hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, Finset.sum_eq_single t] at h2
    · rwa [HT.LatBasic.eigProj_of_mem (gmem _ _)] at h2
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (gmem _ _)
    · simp
  have hblk := GlobalTheory.T.cm_type_polynomial_vanishing_criterion E C ν emb (fun s a => hemb s a) hcard' D π hmono _ ρH HV (p + q) x hfree
  obtain ⟨hb1, hb2⟩ := hblk
  have sumFst : ∀ f : S → Fin (p + q) → C, (∑ s, T s (f s)).1 = ∑ s, g s (f s) := by
    intro f
    exact map_sum (LinearMap.fst C W (Module.Dual C W)) _ _

  have hr : ∀ s, Module.finrank C (LinearMap.ker (g s)) = r s := by
    intro s
    have e1 : (LinearMap.ker (g s)).map (T s) =
        HT.eigSp ρH s.1 ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Tmem s z, hz⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨z, rfl⟩ := Tsurj s y h1
        exact ⟨z, h2, rfl⟩
    change _ = rk (sbar s.1)
    rw [← hrk, ← GlobalTheory.T.dual_module_conjugate_eigen_action E C bar s.1 (sbar s.1) W ρ ρH hsumW (hsbar s.1) hbar hinr, ← e1]
    exact (Submodule.equivMapOfInjective _ (Tinj s) _).finrank_eq
  have hspanLie : Submodule.span C (Lie : Set W) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have h3 : ((y, 0) : W × Module.Dual C W) ∈ Submodule.span C (HV : Set (W × Module.Dual C W)) := by
      rw [hfree.2.1]; trivial
    have h4 : ∀ z ∈ Submodule.span C (HV : Set (W × Module.Dual C W)), z.1 ∈ Submodule.span C (Lie : Set W) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (hmap ▸ ⟨z, hz, rfl⟩)
      | zero => exact zero_mem _
      | add z z' _ _ h h' => exact add_mem h h'
      | smul c z _ h => exact Submodule.smul_mem _ c h
    exact h4 _ h3
  have hLieFG : Lie.FG := by
    rw [← hmap, hfree.2.2]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  have hwLie : ∀ j, w j ∈ Lie ∧ w j ∈ HT.eigSp ρ σ' := by
    intro j
    have : w j ∈ HT.eigSub ρ σ' Lie := hws ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hwsp : Submodule.span C (Set.range w) = HT.eigSp ρ σ' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hwLie j).2
    · intro y hy
      obtain ⟨c, hc, hcy⟩ := HT.LatBasic.exists_smul_mem ν hIv (L := Lie) (x := y) (by rw [hspanLie]; trivial)
      have h3 : c • y ∈ HT.eigSub ρ σ' Lie := ⟨hcy, Submodule.smul_mem _ c hy⟩
      rw [← hws] at h3
      have h4 : c • y ∈ Submodule.span C (Set.range w) :=
        Submodule.span_le_restrictScalars ν.valuationSubring C _ h3
      have := Submodule.smul_mem _ c⁻¹ h4
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hsat : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w) := by
    intro y
    rw [hws, hwsp]
    exact Iff.rfl
  have hφ := GlobalTheory.T.lattice_span_intersection_basis ν.valuationSubring C W Lie q w hLieFG hspanLie hw hsat
  have hσbar : sbar σ = σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    (RingHom.ext fun b => (hsbar σ b).trans (hσ' b).symm)
  have hrτ : r τ = q := by
    change rk (sbar σ) = q
    rw [hσbar, ← hrk, ← hwsp, finrank_span_eq_card hw, Fintype.card_fin]

  have hex : ∀ i, ∃ z, T τ z = u i := fun i => Tsurj τ _ (had.1 i)
  choose U hU using hex
  have hU1 : ∀ i, g τ (U (Fin.castAdd q i)) = v i := fun i => by
    rw [hgT, hU]; exact had.2.1 i
  have hU2 : ∀ j, g τ (U (Fin.natAdd p j)) = 0 := fun j => by
    rw [hgT, hU]; exact (had.2.2 j).1
  have hTmemSpan : ∀ (n : ℕ) (b : Fin n → Fin (p + q) → C) (z : Fin (p + q) → C),
      z ∈ Submodule.span ν.valuationSubring (Set.range b) ↔
        T τ z ∈ Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) := by
    intro n b z
    have e : Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) =
        (Submodule.span ν.valuationSubring (Set.range b)).map ((T τ).restrictScalars ν.valuationSubring) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e]
    constructor
    · exact fun h => ⟨z, h, rfl⟩
    · rintro ⟨z', h, e'⟩
      rwa [← Tinj τ e']
  have hLB2 : IsLatticeBasis ν (fun j => U (Fin.natAdd p j))
      (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) := by
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h2 := congrArg (fun y : W × Module.Dual C W => y.2 (w k)) hc
      simp only [Function.comp, hU, Prod.snd_sum, Prod.smul_snd, LinearMap.sum_apply, LinearMap.smul_apply,
        (had.2.2 _).2, Prod.snd_zero, LinearMap.zero_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h2
      simpa using h2
    · ext z
      rw [hTmemSpan]
      simp only [hU]
      rw [GlobalTheory.T.hodge_lattice_dual_eigen_decomposition E ν.valuationSubring C bar σ σ' W ρ ρH HV Lie q w (fun j => u (Fin.natAdd p j)) hsumW hσ' hbar hfst hinr
        hfil hwsp (fun j => (hwLie j).1) (fun j => ⟨had.1 _, (had.2.2 j).1, (had.2.2 j).2⟩) hφ]
      constructor
      · rintro ⟨φ, h1, h2⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ h1
        refine ⟨f, ⟨hf, fun s => ?_⟩, ?_⟩
        · rw [hgT]
          change (eigCoord ρH x s.1 (f s)).1 = 0
          rw [← hfs, fstE]
          simp
        · apply Tinj τ
          rw [← h2, hfs τ]
          rfl
      · rintro ⟨f, ⟨hf, hg0⟩, rfl⟩
        have h3 := (hb1 f).2 hf
        have h4 : (∑ s, T s (f s)).1 = 0 := by
          rw [sumFst]
          exact Finset.sum_eq_zero fun s _ => hg0 s
        refine ⟨(∑ s, T s (f s)).2, ?_, ?_⟩
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact h3
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact projSum f τ
  have hvs' : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range v) ↔
      y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y := by
    intro y
    rw [hvs]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy2' : y ∈ HT.eigSp ρ σ := hy2
      rw [← hmap] at hy1
      obtain ⟨η, hη, rfl⟩ := hy1
      change η.1 ∈ HT.eigSp ρ σ at hy2'
      obtain ⟨z, hz⟩ := Tsurj τ _ (HT.LatBasic.eigProj_mem ρH σ η)
      obtain ⟨f, hf, hfs⟩ := hb2 _ hη
      refine ⟨⟨z, ?_⟩, f, hf, ?_⟩
      · change (T τ z).1 = η.1
        rw [hz, fstE]
        exact HT.LatBasic.eigProj_of_mem hy2'
      · have h5 : ∀ s, g s (f s) = HT.eigProj ρ s.1 η.1 := fun s => by
          rw [hgT, ← fstE, hfs s]
        simp only [h5]
        rw [Finset.sum_eq_single τ]
        · exact HT.LatBasic.eigProj_of_mem hy2'
        · intro s _ hs
          exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e)) hy2'
        · simp
    · rintro ⟨⟨z, rfl⟩, f, hf, e⟩
      refine ⟨?_, gmem τ z⟩
      rw [← hmap]
      exact ⟨_, (hb1 f).2 hf, (sumFst f).trans e⟩
  have hLBA : IsLatticeBasis ν (fun i => ∑ j, A i j • U j)
      (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) := by
    have hTA : ∀ i, T τ (∑ j, A i j • U j) = ∑ j, A i j • u j := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hU]
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      have : (T τ) ∘ (fun i => ∑ j, A i j • U j) = fun i => ∑ j, A i j • u j := funext hTA
      rw [this]
      exact hAl
    · ext z
      rw [hTmemSpan]
      simp only [hTA]
      rw [hAs]
      constructor
      · rintro ⟨η, hη, e⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ hη
        refine ⟨f, hf, ?_⟩
        apply Tinj τ
        have e' : HT.eigProj ρH σ η = T τ z := e
        rw [← e', hfs τ]
        rfl
      · rintro ⟨f, hf, rfl⟩
        exact ⟨_, (hb1 f).2 hf, projSum f τ⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.T.valuation_lattice_matrix_reduction C ν ℓ h0 h1 S a p q τ r W g v U A ha hind hr hrτ hv hvs' hU1 hU2 hLB2 hLBA
  refine ⟨ε, ?_⟩
  change A.det * P ^ (p + q) = _ * Q at hε
  change A.det = ((ε : ν.valuationSubring) : C) * (Q / P ^ (p + q))
  rw [← mul_div_assoc, ← hε, mul_div_cancel_right₀ _ (pow_ne_zero _ hP)]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_adapted_eq_unit_mul_const : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ :=
  GlobalTheory.T.conjugate_embeddings_valuation_rank_bound ExG.targetO

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypeValuationEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_valuation_embedding : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const | exact GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const <;> assumption)
end
