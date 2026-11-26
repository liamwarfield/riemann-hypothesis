module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsPrimeIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNewformAut
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Af.NewformAutomorphy
private theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩
private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
private theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring
end UpperTheory.V.Af.NewformAutomorphy
open UpperTheory.V.Af.NewformAutomorphy in
theorem UpperTheory.V.Af.newformAutR_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.NewformAutR := by
  intro P k hk f l hl Ω _ _ _ ι W j hf
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ss_of_tw _ _ hf.1, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ f.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq]
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Af.NewformAutomorphy
end UpperTheory.V.Af.NewformAutomorphy
theorem UpperTheory.GalN.V.newformAut0_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → NewformAut0 := by
  intro P k hk f l hl Ω _ _ _ ι W j hf hW K _ _ _ _ _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact _root_.UpperTheory.V.Sd.up_quad_of_printed_results P ℚ K Ω l ι hK 2 one_le_two W hW (_root_.UpperTheory.V.Af.newformAutR_alt P k hk f l Ω ι W j hf) hirr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpSol
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (ha : IsAutC ι r) (hi : IsIrr (r.comp (galEmb F E Ω))) :
    IsAutC ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, -, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
theorem UpperTheory.V.Z.Bc.upSol_of_alt (hA : _root_.UpperTheory.V.Af.Hypotheses') (cyc : UpperTheory.V.Z.Bc.CycC) : UpperTheory.V.Sd.UpSol := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r hc ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι n r ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  refine ih _ hlt K rfl _ (hc.comp (resFacts F K Ω l n r).1) ?_ hi
  exact _root_.UpperTheory.V.Z.Bc.upCyc_of_alt hA cyc F K Ω l ι (hdeg ▸ hp) n hn r hc ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ hi)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSphOfUnrW
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Birth
private theorem exists_polarized {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (H : _root_.UpperTheory.V.Af.HypothesesH') {ι : Qbar l ≃+* ℂ} (hn : 1 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hp : Sol.Pol ι r) (ha : AttC ι r π) : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := UpperTheory.cyclotomicCharacter_plusPart (_root_.UpperTheory.V.Af.algOfCyc_s H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp
  have hdual := _root_.UpperTheory.V.Af.self_dual_complex_of_printed_hida H K Ω l ι n hn r π ha χ μ hμ c P hc hP
  have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
  have hnorm : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  refine ⟨χ * quadChar K ^ (m + n), fun v => ?_, hnorm ▸ hdual⟩
  change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
  rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
  simp
private theorem unram_of_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {n : ℕ} (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (H : ∀ g : Weil h, deg g = 0 → ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n) (j : Fin n)
    (x : (w.adicCompletion E)ˣ) (hx : ord (w.adicCompletion E) x = 0) : ξ j x = 1 := by
  obtain ⟨g, rfl⟩ := ha.surj x
  have h0 : deg g = 0 := by
    have := ha.ord_eq g
    rw [hx] at this
    omega
  have e := congrArg (Polynomial.eval ((ξ j (a g) : ℂˣ) : ℂ)) (H g h0)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp)] at e
  have e2 : ((ξ j (a g) : ℂˣ) : ℂ) - 1 = 0 := by
    have := e.symm
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at this
    exact (pow_eq_zero_iff j.pos.ne').1 this
  exact Units.ext (by simpa [sub_eq_zero] using e2)
end UpperTheory.V.Z.Win.Birth
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Birth in
theorem UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Win.Birth.SphOfUnrW := by
  intro H M Ω _ _ _ _ _ _ l _ ι n hn r π hr hpol hreg hatt hW w hw A hA hu
  have hRow : RowT := _root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal
  have hpp := exists_polarized H hn hpol hatt
  obtain ⟨HT, -, hC⟩ := compatTOf hRow plainRec M Ω l ι n hn r π hr hreg hpp hatt
  obtain ⟨t, ht⟩ := hW π hreg hatt
  refine winSph M n hn π t w (ht w) ?_
  rintro s ⟨σ, hσ, hsup⟩ ζ ⟨hζ, hmem⟩
  haveI : CharZero (w.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists M Ω A w hA
  obtain ⟨hPT, hTor, hMono⟩ := plainRec M Ω A w hA rc hrc n π t (ht w) σ hσ
  have hwd : IsWDOf ι r (rc (algNorm σ)) := (((hC w σ hσ).1 A hA rc hrc).1 hw).isWDOf ⟨hTor, hMono⟩
  have hpolW : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).map ι.toRingHom := fun g => by
    rw [← hwd.wdOf_eq hw]
    exact charPol_wdOf hw ι (Units.continuous_val.comp hr) g
  obtain ⟨a, ha, hLaws⟩ := hrc
  obtain ⟨ξ, hξ, hsupx, -⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion M) (IrrGL.of σ.ρ σ.smooth σ.irred) hPT
  let c : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  let ξ' : Fin n → ((w.adicCompletion M)ˣ →* ℂˣ) := fun j => ξ j * absPow _ c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsup' : HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ' hξ') :=
    (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion M) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' c fun _ => rfl).1.1 hsupx
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  have hse : s = GlobalTheory.RoadU.chars ξ hξ := GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _
    (IrrGL.of σ.ρ σ.smooth σ.irred) _ _ (hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)) hsupx
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 (hse ▸ hmem)
  have hζj : ξ j = ζ := IrrGL.ofChar_inj.1 hj
  have hIne : ∀ g : Weil hA, deg g = 0 → ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n := fun g hg => by
    have hI : (g : G M Ω) ∈ Ine (F := M) A := deg_eq_zero_iff.1 hg
    rw [← charPol_of_chars hLaws _ ξ' hξ' hsup' g, hpolW, hu _ hI]
    simp [Matrix.charpoly_one]
  intro x hx
  have e := unram_of_charPol ha ξ' hIne j x (ord_eq_zero_iff.2 hx)
  have e' : ξ' j x = ξ j x := by
    simp only [ξ', MonoidHom.mul_apply, isUnram_absPow _ c x hx, mul_one]
  rw [← hζj, ← e', e]
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NmRegArith
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
private theorem norm_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  have key : ∀ t, ‖(ψ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h2
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem emb_ne (H : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion L)ˣ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) :
    Nonempty (Emb l w) := by
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * Hi.algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  by_contra hE
  haveI : IsEmpty (Emb l w) := not_nonempty_iff.1 hE
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
  rw [hε, deg_frob, zpow_one, Hi.algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
  have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
    exact lt_irrefl _ this)).1 h1
  exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {w : Plc F} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {a : Weil h →* (w.adicCompletion F)ˣ} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {n : ℕ}
    (wt : Fin n → Emb l w → ℤ) (hm : ∀ τ, StrictMono fun j => wt j τ) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ)
    (hψ : ∀ j, IsLocAlg h (ψ j) (wt j)) : ∃ g, Function.Injective fun i => ψ i g := by
  haveI := emb_ne H hw ha
  haveI : Finite (Emb l w) := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (Emb l w)
  haveI : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  choose ph hph using hψ
  let U : Subgroup (Ine (F := F) A) := ⨅ j, (ph j).ker
  have hU : IsOpen (U : Set (Ine (F := F) A)) := by
    simp only [U, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => (hph j).1
  haveI : Finite (Ine (F := F) A ⧸ U) := U.quotient_finite_of_isOpen hU
  have hN : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hl : ValuativeRel.valuation (w.adicCompletion F) (l : w.adicCompletion F) < 1 := by
    have e : (ValuativeRel.valuation (w.adicCompletion F)).IsEquiv (Valued.v : Valuation (w.adicCompletion F) _) := by
      haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion F) _)
      exact ValuativeRel.isEquiv _ _
    rw [e.lt_one_iff_lt_one, ← map_natCast (algebraMap (𝓞 F) (w.adicCompletion F)),
      IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
    erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem _).2 hw
  have hu : ValuativeRel.valuation (w.adicCompletion F) (1 + l : w.adicCompletion F) = 1 :=
    (ValuativeRel.valuation (w.adicCompletion F)).map_one_add_of_lt hl
  have hu0 : (1 + l : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at hu
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 _ hu0)
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at h2
    omega
  have hI : (s : G F Ω) ∈ Ine (F := F) A := actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))
  let σ : Ine (F := F) A := ⟨s, hI⟩
  haveI : U.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hmem : σ ^ U.index ∈ U := U.pow_index_mem σ
  have e : ((a (ineIncl h (σ ^ U.index)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = (1 + l) ^ U.index := by
    rw [map_pow, map_pow, show ineIncl h σ = s from rfl, hs]
    simp
  let q : ℕ := (1 + l) ^ U.index
  have hq : 1 < q := Nat.one_lt_pow hN (by have := (Fact.out : l.Prime).pos; omega)
  have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp : ∀ (T : Finset (Emb l w)) (c : Emb l w → ℤ), ∏ j ∈ T, (q : Qbar l) ^ c j = (q : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hq0]
  have key : ∀ j, ((ψ j (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index))) : (Qbar l)ˣ) : Qbar l) =
      (q : Qbar l) ^ ∑ τ, -wt j τ := fun j => by
    have h3 := (hph j).2 a ha (σ ^ U.index)
    rw [show ph j (σ ^ U.index) = 1 from Subgroup.mem_iInf.1 hmem j, finprod_eq_prod_of_fintype, e, mul_one] at h3
    rw [h3, ← hp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [q]
  refine ⟨Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index)), fun i j hij => ?_⟩
  have h4 : (q : Qbar l) ^ ∑ τ, -wt i τ = (q : Qbar l) ^ ∑ τ, -wt j τ := by
    rw [← key, ← key]
    exact congrArg Units.val hij
  have h5 : (q : ℚ) ^ ∑ τ, -wt i τ = (q : ℚ) ^ ∑ τ, -wt j τ := by
    apply Rat.cast_injective (α := Qbar l)
    simpa using h4
  have h6 := zpow_right_injective₀ (a := (q : ℚ)) (by positivity) (by exact_mod_cast hq.ne') h5
  have hs : StrictAnti fun j => ∑ τ, -wt j τ := fun i j hij =>
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ _ => neg_lt_neg (hm τ hij)
  exact hs.injective h6
theorem UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (h : s.Wt n) (v : Vl l L) (ψ : Fin n → Dec (F := L) (s.A v) →* (Qbar l)ˣ), h.Incr → (∀ j, IsLocAlg (s.hw v) (ψ j) (h v j)) → ∃ g, Function.Injective fun i => ψ i g := by
  intro H l _ L Ω _ _ _ _ _ _ s n h v ψ hI hψ
  obtain ⟨a, ha⟩ := _root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v)
  have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
  exact main H.aut.art (s.hw v) ((s.hw v.1 _).1 (by simpa using h1)) ha (h v) (hI v) ψ hψ
end
end
