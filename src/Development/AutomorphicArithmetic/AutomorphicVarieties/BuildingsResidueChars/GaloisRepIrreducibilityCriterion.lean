module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

theorem UpperTheory.galoisRep_irreducibility_criterion :
    UpperTheory.V.Af.Bc.IrrBasic := by
  refine ⟨fun Γ Γ' k _ _ _ n r => ⟨fun φ h => ?_, fun h => ?_, fun δ h => ?_⟩, fun Γ k _ _ _ _ _ n r δ hr hδ => ?_⟩
  · exact ⟨h.1, fun _ _ _ => Submodule.mem_top, fun W hW hinv => h.2.2 W hW fun g v hv => hinv (φ g) v hv⟩
  · intro W hW
    rcases h.2.2 W le_top hW with rfl | rfl
    · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : k)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    intro W hW
    obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
    exact ⟨W', (key W').2 hW', hc⟩
  · obtain ⟨hr1, hr2⟩ := Units.continuous_iff.1 hr
    obtain ⟨hd1, hd2⟩ := Units.continuous_iff.1 hδ
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine (hd1.smul hr1).congr fun g => ?_
      exact (tw_val r δ g).symm
    · refine (hd2.smul hr2).congr fun g => ?_
      have := tw_val r δ g⁻¹
      simp only [map_inv] at this
      exact this.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf13.pow_cong A ha hb h m

private theorem dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) : IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

private theorem key {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (f : ℕ)
    (hf : normV w = normV (w.under (𝓞 F)) ^ f) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 F)) ∧ (∀ s ∈ Ine (F := E) A, res F Ω E s ∈ Ine (F := F) A) ∧
      ∀ φ : G E Ω, IsFrob A (normV w) φ → ∃ σ : G F Ω, IsFrob A (normV (w.under (𝓞 F))) σ ∧
        ∀ (C : Type) [Group C] (r : G F Ω →* C), (∀ s ∈ Ine (F := F) A, r s = 1) → r (res F Ω E φ⁻¹) = r σ⁻¹ ^ f := by
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have hv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  refine ⟨hv, fun s hs => ⟨hs.1, hs.2⟩, fun φ hφ => ?_⟩
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hv
  refine ⟨σ, hσ, fun C _ r hr => ?_⟩
  have hφ' : IsFrob (F := F) A (normV w) (res F Ω E φ) := ⟨hφ.1, hφ.2⟩
  rw [hf] at hφ'
  have h := hr _ (inv_mul_mem_Ine_of_isFrob hφ' (isFrob_pow hσ f))
  rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h
  rw [map_inv, map_inv, map_inv, h, inv_pow]

theorem UpperTheory.frobenius_power_compatibility :
    UpperTheory.V.Af.Bc.FrobRes := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ ι w f hf
  refine ⟨fun n r B h A hA => ?_, fun δ z h A hA => ?_⟩
  · obtain ⟨hv, hI, hF⟩ := key w f hf A hA
    obtain ⟨h1, h2⟩ := h A hv
    refine ⟨fun s hs => h1 _ (hI s hs), fun φ hφ => ?_⟩
    obtain ⟨σ, hσ, e⟩ := hF φ hφ
    have e1 := h2 σ hσ
    rw [MonoidHom.comp_apply, e _ r h1, Units.val_pow_eq_pow_val, ← Matrix.charpoly_map, Matrix.map_pow]
    rw [← Matrix.charpoly_map] at e1
    generalize (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).map ι.toRingHom = M at e1 ⊢
    have e2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n f M
    rw [e1, roots_multiset_prod_X_sub_C] at e2
    rw [← e2]
    exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  · obtain ⟨hv, hI, hF⟩ := key w f hf A hA
    obtain ⟨h1, h2⟩ := h A hv
    refine ⟨fun s hs => h1 _ (hI s hs), fun φ hφ => ?_⟩
    obtain ⟨σ, hσ, e⟩ := hF φ hφ
    rw [MonoidHom.comp_apply, e _ δ h1, Units.val_pow_eq_pow_val, map_pow, h2 σ hσ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

private theorem charpoly_smul_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (hM : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  have hc : Multiset.card L = Fintype.card ι := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hM, natDegree_multiset_prod_X_sub_C_eq_card]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem UpperTheory.frobenius_eigenvalues_twist :
    UpperTheory.V.Af.Bc.FrobTw := by
  intro F Ω _ _ _ _ l _ ι n r δ w B z hr hδ A hA
  obtain ⟨h1, h2⟩ := hr A hA
  obtain ⟨h3, h4⟩ := hδ A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [tw_val, h1 s hs, h3 s hs]
    simp
  · have e1 := h2 σ hσ
    have e2 := h4 σ hσ
    rw [← Matrix.charpoly_map] at e1 ⊢
    rw [← charpoly_smul_prod _ z B e1, tw_val, ← e2]
    congr 1
    ext i j
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasFixedOfAlgNormFixedNeBot
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.hasFixed_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) {U : Subgroup G}
    (h : UpperTheory.V.Af.HasFixed τ U) : UpperTheory.V.Af.HasFixed ρ U := by
  obtain ⟨v, hv, hU⟩ := h
  refine ⟨e.symm.toLinearEquiv v, by simpa using hv, fun u hu => ?_⟩
  have h1 := LinearMap.congr_fun (e.symm.isIntertwining' u) v
  simp only [LinearMap.comp_apply, hU u hu] at h1
  exact h1.symm

private theorem UpperTheory.V.hasFixed_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (s : ℂ) (U : Subgroup (GL (Fin x.1) k))
    (hU : U ≤ GlobalTheory.SplitWeil.KO k (Fin x.1)) (h : UpperTheory.V.Af.HasFixed (x.nu s).rep U) :
    UpperTheory.V.Af.HasFixed x.rep U := by
  obtain ⟨v, hv, h1⟩ := UpperTheory.V.hasFixed_of_equiv (x.twEquiv _ _) h
  refine ⟨v, hv, fun u hu => ?_⟩
  have h2 := h1 u hu
  rwa [GlobalTheory.SmGL.twist_apply, detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) (hU hu), Units.val_one,
    one_smul] at h2

theorem UpperTheory.hasFixed_of_algNorm_fixed_ne_bot :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (w.adicCompletion F))), U ≤ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) →
    GlobalTheory.PRep.fixed (algNorm σ).rep U ≠ ⊥ → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ w n σ U hU h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine UpperTheory.V.hasFixed_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) ?_
  refine UpperTheory.V.hasFixed_of_nu (IrrGL.of σ.ρ σ.smooth σ.irred) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) U hU ⟨v, hv0, ?_⟩
  exact fun u hu => (hv ⟨u, hu⟩).trans (by simp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactAndCongruentOfMemPrincipalCongr
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ), ∀ g ∈ UpperTheory.V.Af.KLoc F w n M,
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) ∧
    ∀ i j, valuation (w.adicCompletion F) ((g.val - 1) i j) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) := by
  intro F _ _ w n M g hg
  obtain ⟨k, hk, hkg⟩ := hg
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hint : ∀ x : UpperTheory.V.Af.Ohat F,
      valuation (w.adicCompletion F) (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := fun x => by
    have h1 : Valued.v (GlobalTheory.CuspRep.pLoc F w x.1) ≤ 1 := Subring.mem_iInf.1 x.2 w
    rw [← map_one (valuation (w.adicCompletion F)), ← Valuation.Compatible.vle_iff_le,
      Valuation.Compatible.vle_iff_le
        (v := (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))), map_one]
    exact h1
  let φ : UpperTheory.V.Af.Ohat F →+* w.adicCompletion F := (GlobalTheory.CuspRep.pLoc F w).comp (UpperTheory.V.Af.Ohat F).subtype
  let ψ : UpperTheory.V.Af.Ohat F →+* 𝒪[w.adicCompletion F] := φ.codRestrict _ fun x => hint x
  have hent : ∀ i j, g.val i j = φ (k.val i j) := fun i j => by
    have h1 := GlobalTheory.CuspRep.pLoc_locGL w g
    rw [← hkg] at h1
    rw [← h1]
    rfl
  refine ⟨⟨Matrix.GeneralLinearGroup.map ψ k, ?_⟩, fun i j => ?_⟩
  · ext i j
    rw [hent]
    rfl
  · have h1 : Ideal.Quotient.mk (Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) (k.val i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j :=
      congrArg (fun u : GL (Fin n) (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {(M : UpperTheory.V.Af.Ohat F)}) => u.val i j)
        (MonoidHom.mem_ker.1 hk)
    have h2 : (k.val - 1) i j ∈ Ideal.span {(M : UpperTheory.V.Af.Ohat F)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    have h3 : (g.val - 1) i j = φ y * M := by
      rw [← map_natCast φ, ← map_mul, hy, Matrix.sub_apply, Matrix.sub_apply, map_sub, hent, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul]
    exact mul_le_of_le_one_left' (hint y)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_zpow_eq_ringEquiv_on_roots_of_unity {K : Type*} [Field K] (M : ℕ) (hM : 1 ≤ M) (σ : K ≃+* K) :
    ∃ m : ℤ, ∀ x : K, x ^ M = 1 → σ x = x ^ m := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((σ.toMulEquiv.restrictRootsOfUnity M).toMonoidHom)
  refine ⟨m, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : M ≠ 0)] at hx
  let g : rootsOfUnity M K := ⟨Units.mk0 x hx0, by rw [mem_rootsOfUnity]; ext; simp [hx]⟩
  have := congrArg (fun y : rootsOfUnity M K => ((y : Kˣ) : K)) (hm g)
  simpa [g] using this

private theorem commutator_fixes_root_of_unity {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) (hM : 1 ≤ M)
    (σ τ : Ω ≃ₐ[F] Ω) (ζ : Ω) (hζ : ζ ^ M = 1) : (σ * τ * σ⁻¹ * τ⁻¹) ζ = ζ := by
  obtain ⟨a, ha⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM σ.toRingEquiv
  obtain ⟨b, hb⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM τ.toRingEquiv
  have ha' : ∀ x : Ω, x ^ M = 1 → σ x = x ^ a := ha
  have hb' : ∀ x : Ω, x ^ M = 1 → τ x = x ^ b := hb
  have hμ : ∀ (ρ : Ω ≃ₐ[F] Ω) (x : Ω), x ^ M = 1 → (ρ x) ^ M = 1 := fun ρ x hx => by
    rw [← map_pow, hx, map_one]
  have hz : (σ⁻¹ (τ⁻¹ ζ)) ^ M = 1 := hμ _ _ (hμ _ _ hζ)
  have key : σ (τ (σ⁻¹ (τ⁻¹ ζ))) = τ (σ (σ⁻¹ (τ⁻¹ ζ))) := by
    rw [ha' _ (hμ τ _ hz), hb' _ hz, hb' _ (hμ σ _ hz), ha' _ hz, ← zpow_mul, ← zpow_mul, mul_comm]
  simp only [AlgEquiv.mul_apply]
  rw [key]
  simp

theorem UpperTheory.irreducible_weilDeligne_tame_level_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M : ℕ), 1 ≤ M →
    ∀ (m : ℕ) (b : WDRep h (Fin m → ℂ)), b.ρ.IsIrreducible →
    (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → b.ρ (ineIncl h s) = 1) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), WD.mk b = WD.lpOfChar h ξ hξ ∧ ∀ σ, b.ρ σ = 1 → ξ σ = 1 := by
  intro F Ω _ _ _ _ _ w A h M hM m b hirr hine
  haveI := hirr
  have hcomm : ∀ σ τ : Weil h, b.ρ σ * b.ρ τ = b.ρ τ * b.ρ σ := by
    intro σ τ
    have hdeg : deg (σ * τ * σ⁻¹ * τ⁻¹) = 0 := by
      simp only [deg_mul, deg_inv]
      ring
    have hc : ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ∈ Ine A := deg_eq_zero_iff.1 hdeg
    have hρc : b.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
      have e : ineIncl h ⟨_, hc⟩ = σ * τ * σ⁻¹ * τ⁻¹ := rfl
      rw [← e]
      apply hine
      intro ζ hζ
      show ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ζ = ζ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using commutator_fixes_root_of_unity M hM (σ : G F Ω) τ ζ hζ
    have hst : σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
    rw [← map_mul, hst, map_mul, hρc, one_mul, map_mul]
  have hnt : Nontrivial (Fin m → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation b.ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  have hscal : ∀ τ : Weil h, ∃ c : ℂ, ∀ v, b.ρ τ v = c • v := by
    intro τ
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.ρ τ)
    refine ⟨c, ?_⟩
    let S : Subrepresentation b.ρ := ⟨Module.End.eigenspace (b.ρ τ) c, fun g v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have := congrArg (fun f => f v) (hcomm τ g)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hvS : v ∈ S.toSubmodule := hv.1
      rw [hS] at hvS
      exact hv.2 ((Submodule.mem_bot ℂ).1 hvS)
    · intro v
      have hvS : v ∈ S.toSubmodule := by
        rw [hS]
        exact Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 hvS
  obtain ⟨v0, hv0⟩ := exists_ne (0 : Fin m → ℂ)
  have hspan : Submodule.span ℂ {v0} = ⊤ := by
    let S : Subrepresentation b.ρ := ⟨Submodule.span ℂ {v0}, fun g v hv => by
      obtain ⟨c, hc⟩ := hscal g
      rw [hc]
      exact Submodule.smul_mem _ _ hv⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      have hvS : v0 ∈ S.toSubmodule := Submodule.subset_span rfl
      rw [hS] at hvS
      exact hv0 ((Submodule.mem_bot ℂ).1 hvS)
    · exact congrArg Subrepresentation.toSubmodule hS
  have hm1 : m = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  subst hm1
  let v1 : Fin 1 → ℂ := fun _ => 1
  have hEnd : ∀ (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ), f v = f v1 0 • v := by
    intro f v
    have hv : v = v 0 • v1 := by
      funext i
      fin_cases i
      simp [v1]
    rw [hv, map_smul]
    funext i
    fin_cases i
    simp [v1, mul_comm]
  have hne : ∀ σ : Weil h, b.ρ σ v1 0 ≠ 0 := by
    intro σ h0
    have hinv : b.ρ σ⁻¹ (b.ρ σ v1) = v1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hEnd (b.ρ σ) v1, h0, zero_smul, map_zero] at hinv
    have := congrFun hinv 0
    simp [v1] at this
  let ξ : Weil h →* ℂˣ :=
    { toFun := fun σ => Units.mk0 _ (hne σ)
      map_one' := by
        ext
        simp [v1]
      map_mul' := by
        intro σ τ
        ext
        simp only [Units.val_mk0, Units.val_mul, map_mul, Module.End.mul_apply]
        rw [hEnd (b.ρ σ) (b.ρ τ v1)]
        simp }
  have hξ1 : ∀ σ, ξ σ = 1 ↔ b.ρ σ = 1 := by
    intro σ
    constructor
    · intro hσ
      have h1 : b.ρ σ v1 0 = 1 := by simpa [ξ] using congrArg Units.val hσ
      apply LinearMap.ext
      intro v
      rw [hEnd, h1, one_smul]
      rfl
    · intro hσ
      ext
      simp [ξ, hσ, v1]
  have hsm : IsSmooth ξ := by
    simpa only [IsSmooth, hξ1] using b.smooth
  have hN : b.N = 0 := by
    obtain ⟨k, hk⟩ := b.nilpotent
    set c := b.N v1 0 with hc
    have hNv : b.N v1 = c • v1 := hEnd b.N v1
    have hp : ∀ n : ℕ, (b.N ^ n) v1 = c ^ n • v1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, pow_succ]
    have hck : c ^ k = 0 := by
      have := congrFun (hp k) 0
      rw [hk] at this
      simpa [v1] using this.symm
    have hc0 : c = 0 := pow_eq_zero_iff'.1 hck |>.1
    apply LinearMap.ext
    intro v
    rw [hEnd, ← hc, hc0, zero_smul]
    rfl
  refine ⟨ξ, hsm, ?_, fun σ hσ => (hξ1 σ).2 hσ⟩
  unfold WD.lpOfChar
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    fin_cases i
    rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, hEnd (b.ρ σ) v]
    simp [WDRep.ofChars, diagEnd, ξ]
  · simp [hN, WDRep.ofChars]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ (d : 𝓞 F) (t : E), d ≠ 0 ∧ t * t = algebraMap F E d ∧ (∀ c : F, algebraMap F E c ≠ t) ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h⟩
  obtain ⟨δ, e, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F E
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) δ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
  have hb2 : algebraMap F E (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hδ (by simp)
  refine ⟨a * b, algebraMap F E (algebraMap (𝓞 F) F b) * e 1, mul_ne_zero ha0 hb0, ?_, fun c hc => ?_, fun x => ?_⟩
  · rw [mul_mul_mul_comm, h1, ← map_mul, ← map_mul]
    congr 1
    show _ = algebraMap (𝓞 F) F (a * b)
    rw [map_mul]
    field_simp
  · apply hδ
    refine ⟨c / algebraMap (𝓞 F) F b, (algebraMap F E).injective ?_⟩
    rw [← h1, map_mul, map_div₀, hc]
    field_simp
  · refine ⟨e.repr x 0, e.repr x 1 / algebraMap (𝓞 F) F b, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, map_div₀, Algebra.smul_def, Algebra.smul_def]
    field_simp

theorem UpperTheory.exists_quadratic_sign_character :
    UpperTheory.V.Af.Bc.SignEx := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ h
  classical
  obtain ⟨d, t, hd, ht, hn, hx⟩ := exists_gen F E h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F E Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  set θ : Ω := algebraMap E Ω t with hθ
  have hθ2 : θ * θ = algebraMap F Ω d := by
    rw [hθ, ← map_mul, ht, ← IsScalarTower.algebraMap_apply]
  have hd' : algebraMap F Ω d ≠ 0 := by simpa using hd
  have hθ0 : θ ≠ 0 := fun h0 => hd' (by rw [← hθ2, h0, zero_mul])
  have hne : -θ ≠ θ := fun h0 => hθ0 (by linear_combination (-1 / 2 : Ω) * h0)
  have hpm : ∀ s : G F Ω, s θ = θ ∨ s θ = -θ := fun s => by
    apply mul_self_eq_mul_self_iff.1
    rw [← map_mul, hθ2, AlgEquiv.commutes]
  have hm1 : (-1 : (Qbar l)ˣ) ≠ 1 := fun h0 => by
    have := congrArg Units.val h0
    simp only [Units.val_neg, Units.val_one] at this
    exact absurd this (by norm_num)
  let δ : G F Ω →* (Qbar l)ˣ := MonoidHom.mk' (fun s => if s θ = θ then 1 else -1) fun a b => by
    rcases hpm a with ha | ha <;> rcases hpm b with hb | hb <;>
      simp [AlgEquiv.mul_apply, ha, hb, hne]
  have hδ : ∀ s, δ s = 1 ↔ s θ = θ := fun s => by
    show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ↔ _
    split_ifs with h0 <;> simp [h0, hm1]
  refine ⟨δ, continuous_of_isOpen_ker' δ ?_, fun h1 => ?_, ⟨fun s => ?_, fun s => ?_⟩, ?_⟩
  · have e : δ.ker = MulAction.stabilizer (G F Ω) θ := Subgroup.ext fun s => hδ s
    rw [e]
    exact stabilizer_isOpen_of_isIntegral θ
  · have hfix : θ ∈ (⊥ : IntermediateField F Ω) := by
      rw [← InfiniteGalois.fixedField_bot]
      intro s
      exact (hδ s.1).1 (by rw [h1]; rfl)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
    refine hn c ((algebraMap E Ω).injective ?_)
    rw [← IsScalarTower.algebraMap_apply, hc]
  · rw [hδ]
    constructor
    · intro hs
      refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => ?_, rfl⟩
      obtain ⟨a, b, rfl⟩ := hx x
      show s _ = _
      rw [map_add (f := _), map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul,
        AlgEquiv.commutes, AlgEquiv.commutes, ← hθ, hs]
    · rintro ⟨u, rfl⟩
      exact u.commutes t
  · show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ∨ (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = -1
    split_ifs <;> simp
  · have h4 : Ideal.span {(4 * d : 𝓞 F)} ≠ 0 := by simpa using hd
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h4).subset fun v hv => ?_)
    by_contra hv'
    apply hv
    intro A hA s hs
    rw [hδ]
    refine (hpm s).resolve_right fun h0 => hv' ?_
    have hle : A.valuation θ ≤ 1 := by
      have h1 : A.valuation (θ * θ) ≤ 1 := by
        rw [hθ2]
        exact int_le A (map_isIntegral_int (algebraMap F Ω) d.isIntegral_coe)
      rw [map_mul] at h1
      by_contra h2
      exact absurd h1 (not_le.2 (one_lt_mul'' (not_le.1 h2) (not_le.1 h2)))
    have hlt := hs.2 θ hle
    rw [h0] at hlt
    show v.asIdeal ∣ _
    rw [Ideal.dvd_span_singleton, ← hA]
    have e : algebraMap F Ω ((4 * d : 𝓞 F) : F) = (-θ - θ) * (-θ - θ) := by
      have : ((4 * d : 𝓞 F) : F) = 4 * (d : F) := by
        show algebraMap (𝓞 F) F (4 * d) = _
        rw [map_mul, map_ofNat]
      rw [this, map_mul, ← hθ2, map_ofNat]
      ring
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

private theorem hasSatGL_of_invT {E : Type} [Field E] [NumberField E] {a : ℕ} {w w' : HeightOneSpectrum (𝓞 E)}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

private theorem theta_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g))) := fun v =>
    GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.theta_satake_parameters_inverse :
    UpperTheory.V.Af.Bc.ThetaSat := by
  intro E _ _ _ n P w B h
  rw [CG.hasSat_mk] at h ⊢
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).toRingHom) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  let ρ' := (GlobalTheory.ThetaPull.thetaSub P).locRep w
  let T₀ : P.V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V := (GlobalTheory.ThetaPull.pull E n).submoduleMap P.V
  have h0 : ∀ g x, ρ' (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (P.locRep (cPl w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (GlobalTheory.ThetaPull.pull_act (.fin (locGL E n (cPl w) g)) x.1).symm
  let k := PhiU n (w.adicCompletion E)
  let S : (GlobalTheory.ThetaPull.thetaSub P).V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT c (conjLoc_spec _ w).2.2 hq (T₀.trans S) (fun g x => ?_) h
  have e : thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      k * GlobalTheory.LFun.ConjPlace.invT c n g * k⁻¹ := by
    have e1 : GlobalTheory.LFun.ConjPlace.invT c n g = GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
      Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
    rw [e1]
    rfl
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

theorem UpperTheory.polOfSat_of_thetaSat :
    UpperTheory.V.Af.Bc.ThetaSat → UpperTheory.V.Af.Bc.PolOfSat := by
  intro hθ hJ hG E _ _ _ n hn P ψ h
  refine GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E n P ψ (hG E n _) ?_
  have hiso : (GlobalTheory.ThetaPull.thetaSub P).Iso (P.twist ψ⁻¹) := by
    refine Quotient.exact (hJ.strong_multiplicity_one hn (CG.mk (GlobalTheory.ThetaPull.thetaSub P)) (CG.mk (P.twist ψ⁻¹)) ?_)
    refine h.mono fun w ⟨hu, B, B', h1, h2, e⟩ => ⟨B'.map (·⁻¹), hθ E n P w B' h2, ?_⟩
    have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
      have h3 : ψ.loc w x = 1 := hu x hx
      exact (congrArg Inv.inv h3).trans inv_one
    rw [e]
    exact GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' h1
  obtain ⟨T, hT⟩ := hiso
  refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm)).trans
    (hT o ((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V φ))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurTwistHolds
noncomputable def UpperTheory.Reformulated.B.H13.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.H13.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.H13.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.H13.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.H13.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.H13.aux5 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (1 : Γ)) *
          (r : Γ → GL (Fin n) k) (1 : Γ) =
        (1 : GL (Fin n) k) := by
  intro Γ k _ _ n r χ
  simp

theorem UpperTheory.Reformulated.B.H13.aux6 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s t : Γ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (s * t)) *
          (r : Γ → GL (Fin n) k) (s * t) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s *
          ((Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) t) * (r : Γ → GL (Fin n) k) t) := by
  intro Γ k _ _ n r χ s t
  have hc : ∀ (c : kˣ) (A : GL (Fin n) k),
      A * Matrix.GeneralLinearGroup.scalar (Fin n) c = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
    intro c A
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : k) (fun x => Commute.all _ _) (A : Matrix (Fin n) (Fin n) k)).eq.symm
  rw [map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (r s), hc, mul_assoc]

noncomputable def UpperTheory.Reformulated.B.H13.tw :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* kˣ) → Γ →* GL (Fin n) k :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) ↦
      {
        toFun := fun (s : Γ) ↦
          (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s,
        map_one' := UpperTheory.Reformulated.B.H13.aux5 r χ, map_mul' := UpperTheory.Reformulated.B.H13.aux6 r χ : Γ →* GL (Fin n) k }

noncomputable def UpperTheory.Reformulated.B.H13.SchurTw :
    Prop :=
    ∀ (Γ Γ' k : Type) [inst : Group Γ] [inst_1 : Group Γ'] [inst_2 : Field k] [IsAlgClosed k] (n : ℕ)
      (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
      UpperTheory.Reformulated.B.H13.IsIrr (r.comp φ) →
        δ.comp φ = (1 : Γ' →* kˣ) → UpperTheory.Reformulated.B.H13.RepIso r (UpperTheory.Reformulated.B.H13.tw r δ) → δ = (1 : Γ →* kˣ)

theorem UpperTheory.Reformulated.B.H13.schur_twist_holds :
    UpperTheory.Reformulated.B.H13.SchurTw := by
  intro Γ Γ' k _ _ _ _ n r φ δ hirr hδ hiso
  obtain ⟨hne, -, hmin⟩ := hirr
  obtain ⟨g, hg⟩ := hiso
  have hg' : ∀ s : Γ, Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s * g = g * r s := by
    intro s
    have h : Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s = g * r s * g⁻¹ := hg s
    rw [h, inv_mul_cancel_right]
  have hcomm : ∀ t : Γ', r (φ t) * g = g * r (φ t) := by
    intro t
    have h1 : δ (φ t) = 1 := DFunLike.congr_fun hδ t
    have h := hg' (φ t)
    rwa [h1, map_one, one_mul] at h
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v : Fin n → k,
      v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c ↔
        (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have htop : Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c = ⊤ := by
    refine (hmin _ le_top ?_).resolve_left hc
    intro t v hv
    rw [hmem] at hv ⊢
    have h : (r (φ t) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)
        = (g : Matrix (Fin n) (Fin n) k) * (r (φ t) : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    change (g : Matrix (Fin n) (Fin n) k).mulVec ((r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v)
      = c • (r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hgv : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [← hmem, htop]
    exact Submodule.mem_top
  have hcent : ∀ A : GL (Fin n) k, g * A = A * g := by
    intro A
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, hgv, Matrix.mulVec_smul]
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (Fin n → k) inferInstance
  obtain ⟨i⟩ := hn
  refine MonoidHom.ext fun s => ?_
  have h := hg' s
  rw [hcent, mul_left_inj, mul_eq_right] at h
  have h2 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) i i) h
  apply Units.ext
  simpa using h2
end

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

theorem UpperTheory.schur_twist_holds :
    UpperTheory.V.Af.Bc.SchurTw :=
  _root_.UpperTheory.Reformulated.B.H13.schur_twist_holds
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormValuationOfLocalCompatibility
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open Neutral.B1 hiding G IsPlaceOver Dec

theorem UpperTheory.ideleNorm_valuation_of_local_compatibility :
    UpperTheory.V.Af.Bc.NormLoc → UpperTheory.V.Af.Bc.NormVal := by
  intro hN
  unfold UpperTheory.V.Af.Bc.NormLoc at hN
  unfold UpperTheory.V.Af.Bc.NormVal
  intro E _ _ _ χ w f hf hχ
  set u := HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w with hu
  have hunr : ∀ x : (HeightOneSpectrum.adicCompletion _ u)ˣ, IsUnitAt u x → χ.loc u x = 1 := by
    unfold HChar.UnrAt at hχ
    exact hχ
  have hloc : ∀ x : (HeightOneSpectrum.adicCompletion E w)ˣ,
      ((compNorm E) χ).loc w x = (χ : Ideles _ →* ℂˣ) (ideleNorm E (localIdele E w x)) := fun x => rfl
  have hlocF : ∀ y : (HeightOneSpectrum.adicCompletion _ u)ˣ,
      χ.loc u y = (χ : Ideles _ →* ℂˣ) (localIdele _ u y) := fun y => rfl
  constructor
  · unfold HChar.UnrAt
    intro x hx
    obtain ⟨y, hy, hv⟩ := hN E w x
    rw [hloc, hy, ← hlocF]
    apply hunr
    unfold IsUnitAt at hx ⊢
    rw [hv f hf, hx, one_pow]
  · have hvw : ((compNorm E) χ).val w = ((compNorm E) χ).loc w (atFin w (unif w)) := rfl
    have hvu : χ.val u = χ.loc u (atFin u (unif u)) := rfl
    have hpw : IsUnifAt w (atFin w (unif w)) := Classical.choose_spec (exists_unif w)
    have hpu : IsUnifAt u (atFin u (unif u)) := Classical.choose_spec (exists_unif u)
    unfold IsUnifAt at hpw hpu
    obtain ⟨y, hy, hv⟩ := hN E w (atFin w (unif w))
    rw [hvw, hvu, hloc, hy, ← hlocF, ← map_pow]
    have hone : χ.loc u (y * ((atFin u (unif u)) ^ f)⁻¹) = 1 := by
      apply hunr
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
        hv f hf, hpw, hpu, mul_inv_cancel₀]
      exact pow_ne_zero _ (by simp)
    rw [map_mul, map_inv, mul_inv_eq_one] at hone
    exact hone
end
