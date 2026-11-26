module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ModU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SymmetricCubeTheoremOfEndomorphisms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HostEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GdEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DownCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.GapTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IrrDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Seed3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.IndAutCs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.EqOneOfUnr

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af
theorem UpperTheory.GalN.V.automorphy_bridge_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Af.AutBridgeAlt := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hNotBoth (hR : IsTotallyReal F) (hC : _root_.NumberField.IsTotallyComplex F) : False := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex v)) (hR.isReal v)
  have hC : ∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    have hRegInf (π : CuspSub F n) : RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
      refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩)
        (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
      rintro ⟨m, hm, h⟩
      rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
      exact h
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
      · exact (hNotBoth h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    have hRegInf (π : TR.CuspSub F n) :
        RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
      refine ⟨fun h v => ?_, fun h τ => h _⟩
      simpa only [InfinitePlace.mk_embedding] using h v.embedding
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (hNotBoth hF h).elim
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  · intro _ h0
    obtain ⟨π, hr, -, ha⟩ := _root_.UpperTheory.GalN.V.autCsd0_of_isAutCsdA h0
    exact hC.2 ⟨π, hr, ha⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
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
theorem exRS_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ExRS := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := _root_.UpperTheory.Gal.SV.gr2S' P.galR F Ω l ι n hn π χ hreg hpol
  have key := H.frob
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRS_iso H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩
end UpperTheory.Gal.SV
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
section Real
variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]
private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))
private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp
private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩
private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
    simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]
private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm
private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]
end Real
private theorem expo_intC {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (τ : E →+* ℂ) : expo χ τ = n τ := by
  refine (GlobalTheory.CuspRep.InfType.expo_of_infType E χ).1 n (fun k => h k fun φ => ?_) τ
  exact absurd (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
private theorem reg_shift {n : ℕ} {m : Multiset ℂ} (h2 : m.Nodup) (h3 : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2)
    {s : ℂ} (hs : ∃ k : ℤ, s = k) :
    (m.map (· + s)).Nodup ∧ ∀ z ∈ m.map (· + s), ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  obtain ⟨j, rfl⟩ := hs
  refine ⟨h2.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h3 y hy
  exact ⟨k + j, by push_cast; ring⟩
theorem UpperTheory.V.Af.twist_invariance_automorphic :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.Twi := by
  rintro - F Ω _ _ _ _ _ l _ ι n r κ ⟨sat, inf, hc, hr, hA⟩ ⟨χ, -, art, a, ha, hχ, hL⟩
  rcases hc with ⟨_, π, rfl, rfl⟩ | ⟨_, π, rfl, rfl⟩
  · refine ⟨_, _, Or.inl ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hA art χ a κ ha hL⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 ⟨_, expo_intC hχ τ⟩⟩
  · refine ⟨_, _, Or.inr ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 (expo_intR hχ _)⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
namespace Link
variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h))
end Link
structure UnramifiedInputs : Prop where
  coh : CohomologyHyp
  pr : _root_.UpperTheory.V.Af.HypothesesH'
  modU : _root_.UpperTheory.V.W.ModUAlt
  lev : W.LevEx
  lam : W.LamEx
  b0 : W.ProModularRingExists
end UpperTheory.V.Ws
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AIsoTwAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), WitA ι r →
    (∀ r', RepIso r r' → WitA ι r') ∧ ∀ μ : G F Ω →* (Qbar l)ˣ, IsAlgChar ι μ → WitA ι (tw r μ)
def AUpDownAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → RowT → ∀ (F K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
    [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsGalois F K], Group.IsSolvable (K ≃ₐ[F] K) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → Sol.Pol ι r → IsRegAlgAutomorphicAttached ι r → Flagged r →
      (WitA ι r → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) ∧
      (IneAb r → Keeps r K → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → WitA ι r)
end UpperTheory.V.Z.Win
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CoefIsCoef
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
theorem UpperTheory.V.W.modU_of_printsH :
    Pa.CohP → LocCFTAll → Pa.PfromAut → _root_.UpperTheory.V.W.HidaUAlt → _root_.UpperTheory.V.W.ModUAlt := by
  intro hcoh hloc hP hH l _ L Ω _ _ _ _ _ _ s V hS hμ c hc n hn r B Λ ι
  obtain ⟨J, hJ, hA⟩ := hH l L Ω s V hS hμ c hc n hn r B Λ ι
  haveI := coef_isCoef l c
  obtain ⟨h1, h3⟩ := hP hcoh l L Ω s V c.O n r B J hn hS (hloc l L Ω s) ((muL l L Ω s V).1 hμ) hA
  exact ⟨J, hJ, h1, h3⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.W
theorem cohP_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
theorem global_compat_printed_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GC.Hypotheses₂ :=
  ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
theorem local_class_field_theory_all_of_literal_automorphy (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : LocCFTAll := locCFT hN.aut.art (_root_.UpperTheory.V.W.cohP_alt hN)
theorem modularity_unitary_of_automorphy_hida_unitary (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hP : Pa.PfromAut) (hH : _root_.UpperTheory.V.W.HidaUAlt) : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modU_of_printsH (_root_.UpperTheory.V.W.cohP_alt hN) (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) hP hH
end UpperTheory.V.W
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
namespace UpperTheory.V.Af
section admitted
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
structure AdmRAlt [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : _root_.UpperTheory.V.Z.Win.IsAutQA ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : _root_.UpperTheory.V.Z.Win.A4.SafeRA l M m r
end admitted
section U3
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime]
structure Adm3Alt [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
end U3
def NumberSp4Alt : Prop :=
  ∃ c A : ℕ, ∀ e : ℕ, 2 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal →
    5 ≤ p → ¬ p ∣ M → ∀ k : ℕ, 0 < k → ∀ z₁ z₂ z₃ : ℂ, z₁ ^ k = 1 → z₂ ^ k = 1 → z₃ ^ k = 1 →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Nat.totient k * ((M : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
        (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G ℚ Ω, IsFrob B p σ →
        ∀ X : Finset (G ℚ Ω →* GL (Fin 4) (Qbar l)),
          (∀ r ∈ X, _root_.UpperTheory.V.Af.AdmRAlt ι M ![(e : ℤ) + 1, e, 1, 0] (e + 1) r) → (∀ r ∈ X, ∀ r' ∈ X, RepIso r r' → r = r') →
          (∀ r ∈ X, (r σ).val.trace ≠ ι.symm (eis4 p e z₁ z₂ z₃)) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ r ∈ X, ‖(r σ).val.trace - ι.symm (eis4 p e z₁ z₂ z₃)‖
section Ad
variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}
end Ad
end UpperTheory.V.Af
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfTwGal
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]
theorem UpperTheory.V.Sd.self_twist_galois_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.SelfTwGal := by
  intro P F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := P.litN.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (tendsto_under' (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normV_under (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfDualC
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix
private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm
private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))
private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm
private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))
private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)
private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    {c : G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
theorem UpperTheory.V.Af.self_dual_complex_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SelfDualC := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ χ μ hμ c P hc hP
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk F n hn π _ ?_
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have h2 := (conjSrc_injective (IsCMField.complexConj F).toRingEquiv).tendsto_cofinite.eventually hπ.2
  filter_upwards [Bc.normGal F Ω l ι χ μ hμ, hπ.2, h2, hl] with w ⟨hu, he⟩ ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩ hw
  exact ⟨hu, B, B', hB, hB', frob_dual hc hP hw hF hF' he⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBcPolar
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
theorem UpperTheory.V.Af.Bc.noTwist_of_prints (hP : _root_.UpperTheory.V.Af.Hypotheses') : NoTwist :=
  UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Hypotheses4Z
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Bc
structure Hypotheses4Z' : Prop where
  h : _root_.UpperTheory.V.Af.HypothesesH'
  eis : Published.HilbertEisOne
  one : Lit.OneUse
end UpperTheory.V.Z.Bc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
theorem UpperTheory.satake_galois_link_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ π.finPart ((_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w
    ⟨σ, hi σ hσ⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWAutKQ
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.GalN.V.autKQ0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ), Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → AutP ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) := by
  intro hP K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r wt hc hr ⟨θ, hθ, hd⟩ hirr
  obtain ⟨P, hreg, hA⟩ := hr hc K hK hirr
  obtain ⟨χ, -, hpol, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP.toClassicalTheorems K hK n hn l Ω ι r wt θ P hθ hd hA
  exact ⟨P, hreg, ⟨χ, hpol⟩, hA⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
  (lam : Wt L l n) (K : H.Lev) (P : (H.Gq →* GL (Fin n) (Qbar l)) → Prop)
end
def NumJAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), r.V0ok → IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    UpperTheory.V.J.Num B Λ J
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGIndAutCs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl
private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩
private theorem tw_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (R : G F Ω →* GL (Fin 4) (Qbar l)) : R = tw (tw R (cycBar F Ω l)⁻¹) (cycBar F Ω l ^ (1 : ℤ) * 1) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : IndCs) : IndAutCs := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ h2 l _ ι π r hatt hm hb R hR H
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨P, hfin, hinf⟩ := h K M h2 π hm hb
  have key : IsAutC ι (tw R (cycBar K Ω l)⁻¹) := by
    refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => ?_, attInd K M Ω h2 l ι r R (CG.mk π).HasSat (CG.mk P).HasSat (fun _ _ _ h h' => h.unique h') (fun _ _ _ h h' => h.unique h') hatt hfin hR H⟩
    obtain ⟨m, m', τ, τ', hne, rfl, e, hv, hv', hinj⟩ := hm φ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ τ' _ _ hne e.symm hv hv')]
    exact infOf_add hinj
  rw [tw_back R]
  exact _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hP K Ω l ι 4 _ _ ((_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP K Ω l ι).1 1 1 (by simp)) key
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfUnr
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = GlobalTheory.SmGL.unrChar k a := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
  have h0 : x ≠ 0 := fun e => ValuativeRel.uniformizer_ne_zero (R := k) (by rw [← hx, e, map_zero])
  exact ⟨_, eq_unrChar h (ϖ := Units.mk0 x h0) hx⟩
private theorem full_chars [CharZero k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i)) (hs : HasSupport ρ (GlobalTheory.RoadU.chars ξ hξ))
    (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) : Nonempty (ρ.Equiv (prinSeries ξ)) ∧
    IsL ((List.ofFn fun i => Segment.single (IrrGL.ofChar (ξ i) (hξ i)) (IrrGL.isCusp_ofChar _ _) : List (Segment k)) :
      Multiset (Segment k)) ρ := by
  obtain ⟨hρ, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V ρ ξ hξ).1 hs
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
    GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
  have hP : (prodIrr y hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
      (fun i => (single_spec (hy i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
  let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI : Nontrivial (IndSp _ _) := by
    obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  have equiv_of_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
      (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨e1⟩ := equiv_of_sub (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
  obtain ⟨e⟩ := hq.nonempty_equiv hρ (GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hM)
  have φ : ρ.Equiv (prodIrr y hd) := (e.symm.trans e1.symm).trans (p.trans q)
  exact ⟨⟨e.symm⟩, n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
    fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self hρ).of_equiv (.refl _) φ⟩
end Loc
section WD
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem eq_one_of_unr {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i))
    (hu : (sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).unr) (i : Fin n) (t : Ine (F := E) A) :
    c i (ineIncl h t) = 1 := by
  have h1 : ∀ i g, (WD.lpOfChar h (c i) (hc i)).charPol g = X - C (c i g : ℂ) := fun i g => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 : ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).charPol (ineIncl h t)).IsRoot (c i (ineIncl h t) : ℂ) := by
    rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn, List.prod_ofFn]
    refine IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    simp [h1]
  generalize sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i)) = x at hu h2
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h2
  obtain ⟨v, hv⟩ := h2.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  refine Units.ext (smul_left_injective ℂ hv.2 ?_)
  simpa using h3.symm
end WD
theorem sphT_alt : _root_.UpperTheory.V.Z.Desc.W.SphTAlt := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl A h hI rc ⟨a, ha, L⟩ σ hP hx
  haveI : CharZero (w.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have e0 := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -, -⟩ := id hx
  have hxu : (rc (algNorm σ)).unr := e0 ▸ (hN.unr_wdOf_iff hl ht ι).2 hI
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨⟨e⟩, hL0⟩ := full_chars (n := n) σ.ρ ξ hξ hs' hu
  have hL := hL0.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr, WD.unr_tw] at hxu
  have hun : ∀ i, IsUnram (ξ i) := fun i u hu1 => by
    obtain ⟨g, rfl⟩ := ha.surj u
    have h0 : deg g = 0 := by
      have h1 := ha.ord_eq g
      rw [ord_eq_zero_iff.2 hu1] at h1
      omega
    exact eq_one_of_unr _ _ hxu i ⟨g, deg_eq_zero_iff.1 h0⟩
  choose α hα using fun i => exists_unr (hun i)
  obtain rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i) := funext hα
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1
    (GlobalTheory.PrinSat.hasSatGL_of_equiv e (GlobalTheory.PrinSat.hasSatGL_prinSeries w α)).1
  exact ⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩
end UpperTheory.V.Z.Desc.W
end
end
end
