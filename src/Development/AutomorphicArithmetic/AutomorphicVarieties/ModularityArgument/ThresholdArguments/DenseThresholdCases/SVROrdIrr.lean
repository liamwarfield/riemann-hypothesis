module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewform2A
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkedRig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AutomorphyRankFour
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SharedDedup_Chars_of_red

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVConv
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
theorem ratioW_of_hasSat_alt [IsTotallyReal F] (_P : _root_.UpperTheory.V.Af.Hypotheses') {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    UpperTheory.GalN.V.RatioW (wdOf h hl ι r) := H.ratio w hl A h (H.plain w B hB)
end UpperTheory.Gal.SV
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Sd
private theorem inf_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
private theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) : (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨s, hs, e1⟩, t, ht, e2⟩ := hc
  have a := (H s hs).resolve_left e1
  have b := (H t ht).resolve_right e2
  rcases H _ (I.mul_mem hs ht) with e | e <;> simp only [map_mul] at e
  · exact e1 (mul_right_cancel (b ▸ e))
  · exact e2 (mul_left_cancel (a ▸ e))
private theorem chars_of_red {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [NormedField k] (r : Γ →* GL (Fin 2) k)
    (hc : Continuous r) (h : ¬ IsIrr r) : ∃ c d : Γ →* kˣ, Continuous c ∧ Continuous d ∧
      ∀ s, (r s : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (c s : k)) * (X - C (d s : k)) := _root_.DedupShared.dedup_chars_of_red_1 (Γ := Γ) (k := k) r hc h
private theorem charpoly_tri {K : Type} [Field K] (g r : GL (Fin 2) K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly =
      (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 0 0)) * (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 1 1)) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
private theorem cyc_ine {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine ⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ordinary_irreducible_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdIrr := by
  intro P F Ω _ _ _ _ _ _ l _ hl2 hs ι ξ s c m a π r hr
  by_contra hirr
  obtain ⟨c₁, c₂, hc₁, hc₂, hch⟩ := chars_of_red r hr.cont hirr
  have hI : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      ∃ d : ℤ, d ≠ 0 ∧ ∀ g ∈ Ine (F := F) A, (c₁ / c₂) g = cycBar F Ω l g ^ d := by
    intro w hw A hA
    obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_printsH P F Ω l hl2 hs ι ξ s c m a π r hr w hw A hA
    have hm := (hr.above w hw).2.1
    have key : ∀ t ∈ Ine (F := F) A, (X - C (c₁ t : Qbar l)) * (X - C (c₂ t : Qbar l)) =
        (X - C ((cycBar F Ω l t ^ m w 0 : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l t ^ m w 1 : (Qbar l)ˣ) : Qbar l)) := by
      intro t ht
      let t' : ↥(Dec (F := F) A) := ⟨t, Ine_le_Dec A ht⟩
      rw [← hch, charpoly_tri g _ (hg t').1, (hg t').2 0, (hg t').2 1, hκ 0 t' ht, hκ 1 t' ht]
    have hp : ∀ t ∈ Ine (F := F) A, c₁ t * c₂ t = cycBar F Ω l t ^ m w 0 * cycBar F Ω l t ^ m w 1 := fun t ht => by
      have := congrArg (eval 0) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub, neg_mul_neg] at this
      exact Units.ext this
    rcases hom_or (Ine (F := F) A) c₁ (cycBar F Ω l ^ m w 0) (cycBar F Ω l ^ m w 1) (fun t ht => by
      have := congrArg (eval (c₁ t : Qbar l)) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
      exact (mul_eq_zero.1 this.symm).imp (fun e => Units.ext (sub_eq_zero.1 e)) fun e => Units.ext (sub_eq_zero.1 e)) with h | h
    · refine ⟨m w 0 - m w 1, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
    · refine ⟨m w 1 - m w 0, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_comm (_ ^ m w 0), mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
  obtain ⟨χ, -, art, n, hart, hn, hL⟩ := (_root_.UpperTheory.V.Af.algOfCyc_s P F Ω l ι).1 (c₁ / c₂) (hc₁.div' hc₂) fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨d, -, hd⟩ := hI w hw A hA
    exact ⟨A, hA, d, 1, one_pos, fun t ht => by rw [hd t ht, zpow_neg, mul_inv_cancel, one_pow]⟩
  obtain ⟨χ₀, hχ₀⟩ := hr.pol
  obtain ⟨-, wt, HT, -, -, hG⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems F Ω l ι 2 one_le_two π χ₀ hr.reg hχ₀
  have hG := hG r hr.cont hr.att
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  obtain rfl : n = 0 := by
    have hinf : Infinite (HeightOneSpectrum (𝓞 F)) := inf_places F
    obtain ⟨w, hw, ⟨B, hB, hF⟩, hu⟩ := (hl.and (hr.att.2.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1)).exists
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hR := _root_.UpperTheory.Gal.SV.ratioW_of_hasSat_alt P.toClassicalTheorems hG hw hA hB
    have r1 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₁ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have r2 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have e1 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r1 r2
    have e2 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r2 r1
    have e3 := hL.frob_unr hart (Or.inl hw) hu hA (isFrob_frob (h := hA))
    have e4 : ((χ.val w : ℂˣ) : ℂ) = ι (c₁ (frob hA : G F Ω)⁻¹) / ι (c₂ (frob hA : G F Ω)⁻¹) := by
      rw [← map_div₀, ← Units.val_div_eq_div_val, ← MonoidHom.div_apply, map_inv, Units.val_inv_eq_inv_val, e3, inv_inv,
        RingEquiv.apply_symm_apply]
    have p2 : 0 < ‖ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 (Units.ne_zero _))
    refine UpperTheory.GalN.V.type_zero_window χ n hn w ?_ ?_
    · rw [e4, norm_div, div_lt_iff₀ p2]; exact e1
    · rw [e4, norm_div, ← mul_div_assoc, lt_div_iff₀ p2, one_mul]; exact e2
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have hne : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊤ := fun e => by
      have := congrArg Ideal.absNorm e
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, pow_eq_one_iff] at this
      rcases this with h | h
      · exact (Fact.out : l.Prime).ne_one h
      · exact Module.finrank_pos.ne' h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨⟨M, hM.isPrime, fun e => h0 (le_bot_iff.1 (e ▸ hle))⟩, hle (Ideal.mem_span_singleton_self _)⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨d, hd0, hd⟩ := hI w hw A hA
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  obtain ⟨g, hg, hne⟩ := cyc_ine hw hA (n := d * N) (mul_ne_zero hd0 (by exact_mod_cast hN.ne'))
  obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inr rfl) hA _).1 ⟨g, hg, rfl⟩
  have e2 : χ.loc w x ^ N = 1 := hu w x hx
  refine hne (Units.ext ?_)
  rw [zpow_mul, zpow_natCast, ← hd g hg, Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, e2]
  simp
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckePolyCoeffZero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTwA
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.twisted_point_property_of_isJ_arith_rep_autCsd :
    _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x :=
  fun PH => _root_.UpperTheory.V.Z.Desc.W.point_property_of_isJ_arith_rep_autCsd (_root_.UpperTheory.Gal.SV.rowOf' PH.litN.aut.gal) PH
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.hecke_ideal_point_properties :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.PointTheoremBaseObject ι J :=
  fun PH => _root_.UpperTheory.V.Z.Desc.W.twisted_point_property_of_isJ_arith_rep_autCsd PH PH.descU
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3Alt
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V UpperTheory.V.Z.Win
theorem UpperTheory.V.Z.Win.Dn.autEnd3_alt :
    _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → Sd.IsCC σ → ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], (∀ [Algebra K Ω], Base.galOf ℚ K Ω = η.ker) →
    (∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A)), OrdPt l η Ψ σ g₁ B r →
      (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
      ∀ [Algebra K Ω] [Algebra K L] [IsScalarTower K L Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)),
        (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)).mat) → IneAb ρ ∧ Flagged ρ ∧ Keeps ρ L) → _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι (cycBar L Ω l)⁻¹ → _root_.UpperTheory.V.Pr.AutEnd3Alt c η Ψ σ g₁ B K ι := by
  intro hD Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ Φ k _ C₀ hok hl hcc ι K _ _ _ hK hS hA A dvrA _ r hr hirr _ ρ hρ
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI : IsGalois L Ω := {}
  have hσ : σ * σ = 1 := by
    obtain ⟨j, hj⟩ := hcc
    exact AlgEquiv.ext fun x => j.injective (by simp [AlgEquiv.mul_apply, hj])
  have hησ : η σ = -1 := by
    obtain ⟨hc, ec⟩ := k.c
    have h := k.del ⟨σ, hc⟩
    rw [ec, hok.del_c] at h
    exact h.symm
  have hLη : Base.galOf ℚ L Ω ≤ η.ker := k.gal ▸ inf_le_right
  have hKL : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun f =>
      (hK.ge (hLη (Base.galEmb_mem ℚ L Ω f))) x
  choose f hf using hKL
  have hinj := (algebraMap L Ω).injective
  let φ : K →+* L :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  letI : Algebra K L := φ.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  haveI := k.ab
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have : IsLocalRing A := dvrA.toIsLocalRing
  obtain ⟨_, hloc, hcont⟩ := UpperTheory.V.Th.End3.sub_facts c A
  have : IsLocalHom (algebraMap c.O A) := hloc
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  obtain ⟨ρ', h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hU := hirr (Base.galOf ℚ L Ω) (Base.galEmbTop ℚ L Ω).2.1 hLη
  have hcomp : ∀ s : G L Ω, Base.galEmb ℚ K Ω (Base.galEmb K L Ω s) = Base.galEmb ℚ L Ω s := fun s => rfl
  have hρL (s : G L Ω) : (ρ (Base.galEmb K L Ω s)).val =
      (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ L Ω s)).mat := by
    rw [hρ, hcomp]
  have irreducible {Γ : Type} [Group Γ] (τ : Γ →* GL (Fin 3) (Qbar l))
      (hτ : ∀ g ∈ Base.galOf ℚ L Ω, ∃ s, ∃ t : Qbar l,
        (UnitaryThreeInertia.push A.val r g).mat = t • (τ s).val) : Af.IsIrr τ := by
    refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => hU W fun g hg v hv => ?_⟩
    obtain ⟨s, t, e⟩ := hτ g hg
    change (UnitaryThreeInertia.push A.val r g).mat.mulVec v ∈ W
    rw [e, Matrix.smul_mulVec]
    exact W.smul_mem t (hi s v hv)
  have haut := hA A ρ' h1 (by
    intro v i g hg
    rw [h3 v i g hg, UnitaryThreeInertia.psi]
    have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
    rw [h6]) (ρ.comp (Base.galEmb K L Ω)) (by
    intro s
    rw [h2]
    exact hρL s) (irreducible _ (by
    intro g hg
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    refine ⟨s, 1, ?_⟩
    change _ = (1 : Qbar l) • (ρ (Base.galEmb K L Ω s)).val
    rw [one_smul]
    exact (hρL s).symm))
  have hEntry : Continuous fun g : G ℚ Ω => (r g).mat.map (A.val : A →+* PadicAlgCl l) := by
    refine continuous_matrix fun a b => hcont _ (fun g => (r g).mat a b) fun n => ?_
    exact (hr.cont n).comp fun X => X a b
  have hχ : Continuous fun s : G K Ω => (cycBar K Ω l s)⁻¹ :=
    (UpperTheory.V.Th.End3.cyc_cont K Ω l).inv
  obtain ⟨s1, s2, s3⟩ := hS A r hr hirr ρ hρ
  have f1 := (flagLaws K Ω l 3 ρ).2.1 (cycBar K Ω l)⁻¹
  have f2 := (flagLaws L Ω l 3 (ρ.comp (Base.galEmb K L Ω))).2.1 (cycBar L Ω l)⁻¹
  refine hD K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hcc ?_
    ⟨Jgl (R := Qbar l) 3, fun s s' hs => ?_⟩ ?_ (f1.1 hχ s1) (f1.2.1 s2)
    (fun w hw hu => (f2.2.2 w).1.1 (s3 w hw ((f1.2.2 _).1.2 hu))) haut
  · refine _root_.UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom _ ?_
    simp only [Af.tw_val, hρ]
    exact (Units.continuous_val.comp hχ).smul
      (hEntry.comp (Base.galEmbTop ℚ K Ω).1.continuous)
  · have pairing {x y j : GG (m := 3) (R := PadicAlgCl l)} (hj : j.mat = 1) (hj' : j.right = -1)
        (h : y * j = j * x) : x.mat.transpose * Jmat _ 3 * y.mat = Jmat _ 3 := by
      have h1 : j.left = 1 := Units.ext hj
      have h2 := congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2
      rw [GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ (Jmat _ 3) (Jmat _ 3), Jmat_mul_Jmat, Matrix.mul_one,
        ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
      simp
    have hp := pairing (x := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)) (y := UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s'))
      (j := UnitaryThreeInertia.push A.val r σ)
      (by
        show (r σ).mat.map _ = 1
        rw [hr.norm.atc]; simp)
      ((hr.red.mult σ).trans hησ)
      (by rw [← map_mul, ← map_mul, hs, inv_mul_cancel_right])
    have he : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (Base.galEmb ℚ K Ω s') = cycBar ℚ Ω l (Base.galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [Af.tw_val, Af.tw_val, hρ, hρ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    show _ • (_ * Jmat _ 3 * _) = _ • Jmat _ 3
    rw [hp, MonoidHom.inv_apply, MonoidHom.inv_apply, he, MonoidHom.zpow_apply, ← Units.val_mul]
    congr 2
    rw [show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]
  · refine irreducible _ fun g hg => ?_
    obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
    refine ⟨s, (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l), ?_⟩
    change _ = (cycBar K Ω l (Base.galEmb K L Ω s) : Qbar l) •
      (Af.tw ρ (cycBar K Ω l)⁻¹ (Base.galEmb K L Ω s)).val
    rw [Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.mul_inv, one_smul]
    exact (hρL s).symm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutUpA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UpCsd0
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
namespace UpperTheory.V.Th.End3
open UpperTheory.V.U3 UpperTheory.V.Base
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
theorem autCsd0_comp_galEmb_of_isPair_of_isIrr_of_isAut (hP : _root_.UpperTheory.V.Af.HypothesesH') (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [hsol : Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω) (hσ : Sd.IsCC σ) (hr : Continuous r) (P : GL (Fin n) (Qbar l))
    (hPr : Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) (hirr : Af.IsIrr (r.comp (galEmb K L Ω)))
    (haut : Af.IsAut ι r) : AutCsd0 ι (r.comp (galEmb K L Ω)) := by
  obtain ⟨j, hj⟩ := hσ
  haveI : IsAlgClosure K Ω := algClo K Ω
  haveI : IsAlgClosure L Ω := algClo L Ω
  haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : Af.IsConjEl c := ⟨j, hj⟩
  have hpc : Af.IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : Af.IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP ℚ L Ω inferInstance l ι n hn _ σ P ⟨j, hj⟩ ?_
    fun s s' hs => hPr (galEmb K L Ω s) (galEmb K L Ω s') hs
  refine (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP) (maximalRealSubfield K) K L Ω hsol
    ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ inferInstance inferInstance
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).1 haut
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · have ha' : cycZ (maximalRealSubfield K) Ω l a = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := a.toRingEquiv) ha
    have hb' : cycZ (maximalRealSubfield K) Ω l b = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := b.toRingEquiv) hb
    simp only [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, ha', hb']
  · exact hpc
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}
end UpperTheory.V.Th.End3
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
namespace UpperTheory.V.Th.End3
open UpperTheory.V.U3 UpperTheory.V.Base
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
open UpperTheory.V.Z.Win
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}
theorem isAutCsdA_twist_comp_galEmb_of_repIso_of_flagged (hH : _root_.UpperTheory.V.Af.HypothesesH') (hab : IsAbelianGalois ℚ L) (ι : Qbar l ≃+* ℂ) (hσ : Sd.IsCC σ)
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hc : (R σ).right = -1) (hatc : (R σ).mat = 1) (hρc : Continuous ρ)
    (hiL : MatIrr ⊤ fun g => (ρ.comp (galEmb K L Ω) g).val) {ρ₀ : G K Ω →* GL (Fin 3) (Qbar l)} (hiso : Af.RepIso ρ₀ ρ) (hFl : Flagged ρ)
    (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw ρ₀ (cycBar K Ω l)⁻¹)) :
    _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹) := by
  obtain ⟨_, hsol⟩ := Db.galKL K L hab
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := hsol
  obtain ⟨h', hiso⟩ := hiso
  have et : Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹ = (Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω) :=
    MonoidHom.ext fun s => Units.ext <| by
      rw [Af.tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Af.tw_val]
      rfl
  have htw : MatIrr ⊤ fun g => (Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹ g).val := fun W hW =>
    hiL W fun g hg v hv => by
      have h := hW g hg v hv
      beta_reduce at h
      rwa [Af.tw_val, Matrix.smul_mulVec, W.smul_mem_iff ((cycBar L Ω l)⁻¹ g).ne_zero] at h
  have hiT := Db.irr_of_matIrr (show 1 ≤ 3 by decide) ⊤ _ htw (MonoidHom.id _) (fun g _ => ⟨g, rfl⟩) _ fun _ => rfl
  rw [et] at hiT ⊢
  haveI := algClo K Ω
  have hcT : Continuous (Af.tw ρ (cycBar K Ω l)⁻¹) := Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv
  have hisoT : Af.RepIso (Af.tw ρ₀ (cycBar K Ω l)⁻¹) (Af.tw ρ (cycBar K Ω l)⁻¹) := ⟨h', fun s => Units.ext (by
    rw [Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul,
      Matrix.smul_mul])⟩
  have hN := _root_.UpperTheory.GalN.V.autCsd_iso_alt hisoT (_root_.UpperTheory.GalN.V.csdN'_alt hH.toClassicalTheorems (by norm_num) haut)
  have hpr : Sd.IsPair σ (Af.tw ρ (cycBar K Ω l)⁻¹) (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) (Jgl (R := Qbar l) 3) := fun s s' hs => by
    have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [Af.tw_val, Af.tw_val, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, h3]
    apply congrArg _
    have hl : (R σ).left = 1 := Units.ext hatc
    have hconj : (R σ * R (galEmb ℚ K Ω s) * (R σ)⁻¹).left = theta (R (galEmb ℚ K Ω s)).left := by
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        hl, hc, hK s, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]
    rw [hρ s', hs, map_mul, map_mul, map_inv, hconj, ← hρ]
    change (ρ s).val.transpose * Jmat _ 3 * (theta (ρ s)).val = Jmat _ 3
    rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat _ 3) (Jmat _ 3), Jmat_mul_Jmat,
      Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mul]
  have halg : Af.IsAlgChar ι (cycBar ℚ Ω l ^ (1 - ((3 : ℕ) : ℤ))) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - ((3 : ℕ) : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, _root_.zpow_neg, mul_inv_cancel]
  suffices h0 : AutCsd0 ι ((Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω)) from
    _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change L hH hsol (by norm_num) hcT hiT
      ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, σ, Jgl (R := Qbar l) 3, halg,
        Ws.auSign _, hσ, hpr⟩ hN.1.c0 (((flagLaws K Ω l 3 ρ).2.1 _).2.1 hFl) (hN.2 hcT)
  refine _root_.UpperTheory.V.Th.End3.autCsd0_comp_galEmb_of_isPair_of_isIrr_of_isAut hH K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hσ
    (Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv) (Jgl (R := Qbar l) 3) hpr hiT
    (isAut_iso ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 3 _).2.2 haut) ⟨h', fun s => Units.ext ?_⟩
      ((Af.Bc.irrBasic.1 _ _ _ 3 _).1 _ hiT))
  rw [Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul,
      Matrix.smul_mul]
end UpperTheory.V.Th.End3
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
open UpperTheory.V.Z.Win
set_option maxHeartbeats 400000 in
open UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Th.End3 in
theorem UpperTheory.V.Z.Win.Dn.rigEnd3_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Th.RigEnd3Alt := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨ hF A _ _ r hr hirr K _ _ _ _ hK2 hker ρ hρ haut hfree
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := algClo K Ω
  haveI := algClo L Ω
  obtain ⟨hcpl, hloc, hcont⟩ := sub_facts c A
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hM := Pr.marks_of_link k hok hl hσ hΨ
  have h2 : IsUnit (2 : c.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h0
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))
  obtain ⟨h, -, hr'⟩ := _root_.UpperTheory.V.Th.End3.ordPt_renorm hr
    (_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM
  let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h
  have eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r) := map_conjBy _ h r
  refine h1fZero_conjBy _ h' ?_
  rw [← eR]
  have hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹ := fun g hg => by
    rw [eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]
  have hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => hker ▸ galEmb_mem ℚ K Ω s
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) := (MulAut.conj h').toMonoidHom.comp ρ
  have hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹ := fun _ => rfl
  have hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left := fun s => by
    rw [hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]
  have hLη : galOf ℚ L Ω ≤ η.ker := Db.galL_le k
  have hirr' : MatIrr (galOf ℚ L Ω) (mats (UnitaryThreeInertia.push A.val (conjBy h r))) :=
    matIrr_conj (hirr _ (galEmbTop ℚ L Ω).2.1 hLη) h' fun g hg => congrArg Units.val (hmat g (hLη hg))
  generalize conjBy h r = r' at hr' hρ' hirr'
  have hFl : Flagged ρ' := (Dn.localConditionRankThreeLink_of_inertia_ordinary Dn.ineOfKer_of Dn.flagAll_of Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r' hr' K hker ρ'
    fun s => congrArg Units.val (hρ' s)).2
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g := hr'.red.mult
  have hatc : (UnitaryThreeInertia.push A.val r' σ).mat = 1 := by
    rw [MonoidHom.comp_apply, GG.map_mat, hr'.norm.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : (UnitaryThreeInertia.push A.val r' σ).right = -1 := (hright σ).trans hM.ηc
  have hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1 := fun s => (hright _).trans (hmem s)
  have hρc : Continuous ρ' := by
    refine _root_.UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom _ (continuous_matrix fun a b => ?_)
    simp only [hρ']
    exact (hcont _ (fun g => (r' g).mat a b) fun n => (hr'.cont n).comp fun X => X a b).comp (galEmbTop ℚ K Ω).1.continuous
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hLη.trans hker.le)
  have hiL : MatIrr ⊤ fun g => (ρ'.comp (galEmb K L Ω) g).val := fun W hW => hirr' W fun g hg => by
    rw [← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    have := hW s trivial
    beta_reduce at this
    rwa [MonoidHom.comp_apply, hρ'] at this
  have hautL := _root_.UpperTheory.V.Th.End3.isAutCsdA_twist_comp_galEmb_of_repIso_of_flagged hH k.ab ι H.cc hρ' hK hc hatc hρc hiL ⟨h', hiso⟩ hFl haut
  obtain ⟨ν, n1, n2, n3⟩ := Pr.exists_nrep3 k hok hl hσ r' hr'
  have key := (_root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed).1
  have n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val := fun s => by
    rw [n2, MonoidHom.comp_apply, hρ']
    rfl
  have n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val =
      algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val := fun v i g hg => by
    rw [n3 v i g hg, Fr.w, if_pos rfl]
    rfl
  have hi : Af.IsIrr (ρ'.comp (galEmb K L Ω)) :=
    Db.irr_of_matIrr (show 1 ≤ 3 by decide) ⊤ _ hiL (MonoidHom.id _) (fun g _ => ⟨g, rfl⟩) _ fun _ => rfl
  have hrig := key A ν n1 n5 _ n4 hi hautL (freeAt_res (freeAt_iso hfree ⟨h', hiso⟩))
  obtain ⟨s, V, τ, t1, t2, t3⟩ := hrig
  refine adDown Ω l K L hK2 (galOf_le ℚ K Ω L) s V 3 ρ' 1 _ hρc
    ⟨σ, Jgl (R := Qbar l) 3, H.cc, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩ τ (cycBar L Ω l)⁻¹
    (fun g t ht => ?_) (fun g g' t hg _ => ?_) t3
  · rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have hl : ((UnitaryThreeInertia.push A.val r') σ).left = 1 := Units.ext hatc
    have hconj : ((UnitaryThreeInertia.push A.val r') σ * (UnitaryThreeInertia.push A.val r') (galEmb ℚ K Ω s) * ((UnitaryThreeInertia.push A.val r') σ)⁻¹).left = theta ((UnitaryThreeInertia.push A.val r') (galEmb ℚ K Ω s)).left := by
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
        hl, hc, hK s, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]
    change galEmb ℚ K Ω s' = σ * galEmb ℚ K Ω s * σ⁻¹ at hs
    rw [hρ' s', hs, map_mul, map_mul, map_inv, hconj, ← hρ']
    change (ρ' s).val.transpose * Jmat _ 3 * (theta (ρ' s)).val = Jmat _ 3
    rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat _ 3) (Jmat _ 3), Jmat_mul_Jmat,
      Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mul]
  · show (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).adFun X = _
    rw [GG.adFun, if_pos (hK s), hρ']
    rfl
  · have hl1 : (UnitaryThreeInertia.push A.val r' σ).left = 1 := Units.ext hatc
    show (UnitaryThreeInertia.push A.val r' σ).adFun X = _
    rw [GG.adFun, hc, if_neg (by decide), hatc, hl1, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · obtain rfl : galEmb K L Ω g = t := AlgEquiv.ext fun x => DFunLike.congr_fun ht x
    exact t1 g
  · rw [MonoidHom.one_apply, mul_one]
    exact t2 g g' hg
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicLiftGsp4OfInputs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Cu
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem as_infOf (M : Multiset ℂ) (h2 : M.card = 2) (hz : ∀ z ∈ M, ∃ k : ℤ, z = (k : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2) :
    ∃ a b : ℤ, M = infOf ![a, b] ∧ M = {(a : ℂ) + 1 / 2, (b : ℂ) + 1 / 2} := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h2
  obtain ⟨a, rfl⟩ := hz x (by simp)
  obtain ⟨b, rfl⟩ := hz y (by simp)
  have e : ∀ a : ℤ, (a : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 = ((a + 1 : ℤ) : ℂ) + 1 / 2 := fun a => by push_cast; ring
  refine ⟨a + 1, b + 1, ?_, by rw [e, e]⟩
  have : (Finset.univ : Finset (Fin 2)).val = {0, 1} := rfl
  rw [infOf, this, e, e]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1 <;> [skip; congr 1] <;> push_cast <;> ring
private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (h : IsIrr r) : IsIrr (tw r κ) := by
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hi => h.2.2 W hW fun s v hv => ?_⟩
  have := W.smul_mem (((κ s)⁻¹ : kˣ) : k) (hi s v hv)
  rw [tw_val, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at this
  exact this
private theorem irr_tw_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (φ : Γ' →* Γ)
    (h : IsIrr (r.comp φ)) : IsIrr ((tw r κ).comp φ) :=
  irr_tw (r.comp φ) (κ.comp φ) h
private theorem tw_one {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (s : Γ) (h : r s = 1) (h' : κ s = 1) :
    tw r κ s = 1 := Units.ext (by rw [tw_val, h, h']; simp)
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Cu.rank_four_automorphy_of_tensor_of_base_change_of_induction (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : Z.InvariantSubmoduleMonicPolynomial.E.IndAutCs) (hP : PolOf4) (hB : BadOfW) : RankFourAutomorphyOfTensor := by
  intro Ω _ _ _ l _ ι K' _ h2 hc ρ hρ ⟨π, hreg, hatt⟩ hio hrw g0 m c₁ κ hg0 ⟨τ₀, s₀, h₀⟩
  haveI : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have RK := resFacts ℚ K' Ω l 2 ρ
  obtain ⟨P₀, reg₀, att₀, -⟩ := hQ ℚ K' Ω l ι h2 ρ π hρ hreg hatt (RK.2.2.2.1.1 (hio _ RK.2.1))
  obtain ⟨j, j1, j9, hj⟩ := Cu2.goodJ K' h2 P₀ reg₀ m (by simpa using h₀.pos)
  refine ⟨j, j1, j9, fun ρ₁ τ s hiso hτ => ?_⟩
  suffices key : ∀ (L : IntermediateField ℚ Ω) [NumberField L] [_root_.NumberField.IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
      IsIrr ((tenB ρ₁ τ).comp (resQ L)) → IsAutC ι ((tenB ρ₁ τ).comp (resQ L)) ∧ AllW ι ((tenB ρ₁ τ).comp (resQ L)) from
    ⟨fun L _ _ a b c d => (key L a b c d).1, fun L _ _ a b c d => (key L a b c d).2⟩
  intro L _ _ hLa hkL hgood hL
  obtain ⟨art, Y, a, e, hart, hpos, hlad, ha, ha'⟩ := hτ.alg
  obtain ⟨N, N', hN, hN', -, hnd, hint⟩ := hj Y a e hpos ha ha'
  have att₁ := Cq.attTwist K' Ω l ι 2 _ P₀ att₀ art Y a (κ ^ j) hart hlad
  have hind := Cu2.tenInd Ω l ι K' h2 ρ g0 (m * j) c₁ (κ ^ j) ρ₁ τ s hiso hτ
  obtain ⟨a₁, a₂, e₁, f₁⟩ := as_infOf N (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN, CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inl hz))
  obtain ⟨b₁, b₂, e₂, f₂⟩ := as_infOf N' (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN', CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inr hz))
  have hinj : Function.Injective ![![a₁, a₂] 0, ![a₁, a₂] 1, ![b₁, b₂] 0, ![b₁, b₂] 1] := by
    rw [f₁, f₂] at hnd
    simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, add_left_inj, Int.cast_inj, not_or] at hnd
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; omega)
  have hemb : ∀ φ : K' →+* ℂ, φ = e ∨ φ = ComplexEmbedding.conjugate e := fun φ => by
    classical
    by_contra hw
    push Not at hw
    have hne : e ≠ ComplexEmbedding.conjugate e := fun h => IsTotallyComplex.complexEmbedding_not_isReal e (ComplexEmbedding.isReal_iff.2 h.symm)
    have h3 : ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ)).card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hw.1, hw.2, hne, rfl⟩
    have h4 := Finset.card_le_univ ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ))
    rw [NumberField.Embeddings.card K' ℂ, h2] at h4
    omega
  have reg₁ : (CG.mk (P₀.twist Y)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => by
    have key : ∀ (M : Multiset ℂ), (P₀.twist Y).HasInfChar φ M → M ≤ N + N' →
        ((CG.mk (P₀.twist Y)).infChar φ).Nodup ∧ ∀ z ∈ (CG.mk (P₀.twist Y)).infChar φ, ∃ k : ℤ, z = (k : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
      intro M hM hle
      rw [CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hM]
      refine ⟨Multiset.nodup_of_le hle hnd, fun z hz => ?_⟩
      obtain ⟨k, rfl⟩ := hint z (Multiset.mem_of_le hle hz)
      exact ⟨k + 1, by push_cast; ring⟩
    rcases hemb φ with rfl | rfl
    · exact key N hN (Multiset.le_add_right _ _)
    · exact key N' hN' (Multiset.le_add_left _ _)
  haveI : FiniteDimensional ℚ K' := NumberField.to_finiteDimensional
  haveI : FiniteDimensional ℚ L := NumberField.to_finiteDimensional
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = K' ⊔ L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup K' L
  haveI : NumberField M := {}
  have hEM : K' ≤ M := hM ▸ le_sup_left
  have hLM : L ≤ M := hM ▸ le_sup_right
  letI : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra K' M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ K' M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra L _
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ K' := { finrank_eq_two' := h2 }
  haveI hK : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ K' L ‹_› ‹_› hK hLa
  haveI : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[K'] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dM : Module.finrank L M = 2 := deg_two K' L _ hM h2 hkL
  have RM := resFacts K' M Ω l 2 (ρ.comp (galEmb ℚ K' Ω))
  have hirrM : IsIrr ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    irr_tw_comp _ _ _ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  obtain ⟨P, regP, att, inf⟩ := hS K' M Ω l ι _ (P₀.twist Y) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont) reg₁ att₁ hirrM
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois L M := IsAbelianGalois.tower_top ℚ _ _
  have hc0 : Continuous (tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont
  have hcont : Continuous ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) := hc0.comp RM.1
  haveI : IsCMField K' := IsCMField.of_isAbelianGalois K'
  have hW : AllW ι ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H ℚ K' M Ω h2 l ι ρ (κ ^ j) hρ hrw ⟨hτ.kcont, art, Y, a, hart, hpos, hlad⟩ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  have hbad : Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L P := by
    refine hB Ω l ι K' L M hM ρ _ P hgood hcont
      (UpperTheory.solvable_polarized_restriction K' M Ω l ι 2 _ (hP Ω l ι K' h2 hc ρ hρ ⟨π, hreg, hatt⟩ g0 _ c₁ _ τ s hτ)) regP att
      hW fun A hA u hu h1 => ?_
    have h3 : τ (resQ K' (galEmb K' M Ω u)) = 1 :=
      hτ.unr A hA _ ⟨hu.1, hu.2⟩ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => (galEmb K' M Ω u).commutes ⟨y, hy⟩)
    have h4 : (κ ^ j) (galEmb K' M Ω u) = 1 := Units.ext (by rw [hτ.val, h3]; simp)
    have h6 : galEmb ℚ K' Ω (galEmb K' M Ω u) = resQ M u := AlgEquiv.ext fun _ => rfl
    have h5 : (ρ.comp (galEmb ℚ K' Ω)) (galEmb K' M Ω u) = 1 := by rw [MonoidHom.comp_apply, h6, h1]
    rw [MonoidHom.comp_apply]
    exact tw_one (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j) (galEmb K' M Ω u) h5 h4
  refine (fun h1 h2 => And.intro (hI L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd L M Ω dM l ι P _ att (hW P regP att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨t, t', hne, q, q'⟩ := two_emb dM ψ
    have hd : t.comp (algebraMap K' M) ≠ t'.comp (algebraMap K' M) := fun hp =>
      hne (hom_ext_sup K' L M hEM hLM hM.le t t' (fun x => DFunLike.congr_fun hp x) fun x => DFunLike.congr_fun (q.trans q'.symm) x)
    rcases hemb (t.comp (algebraMap K' M)) with p | p <;> rcases hemb (t'.comp (algebraMap K' M)) with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, t, t', hne, q, q', inf _ _ (p ▸ e₁ ▸ hN), inf _ _ (p' ▸ e₂ ▸ hN'), hinj⟩
    · exact ⟨_, _, t', t, hne.symm, q', q, inf _ _ (p' ▸ e₁ ▸ hN), inf _ _ (p ▸ e₂ ▸ hN'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ L s ∉ K'.fixingSubgroup := fun hu => by
      apply hs
      rw [range_galEmb]
      have : resQ L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨hu, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    refine ⟨fun g g' e => hind.on _ hs' (galEmb K' M Ω g) (galEmb K' M Ω g') ?_, fun g e => hind.off _ hs' (galEmb K' M Ω g) ?_⟩
    · have := congrArg (resQ L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ L) e
      rw [map_mul] at this
      exact this
end
end
