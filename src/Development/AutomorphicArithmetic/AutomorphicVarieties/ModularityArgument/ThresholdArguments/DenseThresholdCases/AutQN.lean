module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardQuotPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CountQuadraticOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfCmEigensystemCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OneCharOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CountVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ConductorAtMapInjectiveCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ResidualBernoulliNonvanishing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitaryLiftTheoremOfReducedForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Xpp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoHostVanE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.HasHTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeCU

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
structure AdmKNAlt [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
  level : Level l M m r
  odd : _root_.UpperTheory.V.Keep.OddA l r
structure AdmRNAlt [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : _root_.UpperTheory.V.Z.Win.IsAutQA ι r
  level : Level l M m r
  dual : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ
  safe : _root_.UpperTheory.V.Z.Win.A4.SafeRA l M m r
structure AdmPNAlt [IsCMField F] [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π
  unl : _root_.UpperTheory.V.Z.Win.WitA ι r
  level : Lev.LevelF l M m r
  safe : _root_.UpperTheory.V.Z.Win.A4.SafePA l M m r
theorem csdN'_alt [IsCMField F] [IsAlgClosure F Ω] (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := h
end
section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
theorem autQN'_alt (_ : _root_.UpperTheory.V.Af.Hypotheses') (_ : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {r : G ℚ Ω →* GL (Fin n) (Qbar l)} {wt : ℤ}
    (_ : ∃ θ, IsCycWt l wt θ ∧ DualTw r θ) (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r := h
variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]
omit [IsAlgClosure ℚ Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] in
structure Adm3NAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
  unl : _root_.UpperTheory.V.Keep.OddA l ρ
end
def LevelKNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Level l M m r → _root_.UpperTheory.V.Keep.OddA l r → _root_.UpperTheory.V.Z.Win.WitA ι r → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)
def LevelPNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Lev.LevelF l M m r → _root_.UpperTheory.V.Z.Win.A4.SafePA l M m r → _root_.UpperTheory.V.Z.Win.WitA ι r →
      (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
      π ∈ Br.SigP K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)
def AdmResNAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ),
    StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r → IsIrr (r.comp (res ℚ Ω K)) → _root_.UpperTheory.GalN.V.AdmPNAlt ι M m (r.comp (res ℚ Ω K))
end UpperTheory.GalN.V
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.U
theorem pt_s (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GlobalTheory.Published.PoitouTateDuality := GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hN.coh.pt
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
end UpperTheory.V.HV.U
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartU
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MkAtLT
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdAtLOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord.AtLOrdinary
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1
end UpperTheory.V.Z.Ord.AtLOrdinary
open UpperTheory.V.Z.Ord.AtLOrdinary in
theorem UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → AtLOf := by
  intro _ l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw ω hs hd ⟨e⟩ rc hrc _ O _ _ _ Bw hj
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  have hP := plainTor_of_ps τ ω hs hd e
  have hG : Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  obtain ⟨h1, h2⟩ := hHT hP A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · have hemb : ∃ j : UpperTheory.V.W.Emb l w,
        j.1.comp (algebraMap L (w.adicCompletion L)) = t := by
      have hplace : w = GlobalTheory.EvExtend.placeOf t := by
        refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
        rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
        let f := LL'.1.val.comp τ'
        let y : Bw.Kw.1 := ⟨Bw.j (algebraMap L Ω x), Bw.j_E x⟩
        have hnorm : ‖f y‖ = ‖(y : PadicAlgCl l)‖ := by
          rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm,
            spectralNorm, minpoly.algHom_eq f f.injective,
            ← minpoly.algHom_eq Bw.Kw.1.val Bw.Kw.1.val.injective]
          rfl
        refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
        exact iff_of_eq (congrArg (· < 1) hnorm.symm)
      rw [hplace]
      obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext t
      exact ⟨⟨j, hc⟩, RingHom.ext hx⟩
    obtain ⟨j, rfl⟩ := hemb
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · rw [((hLG A h rc hrc).2 O Bw hj hG).2]
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.P
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}
theorem ordinary_at_l_of_local_global_hodge_tate_weights (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) (lam : Wt L l n) (_ : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, HtGT r HT w τ)
    (k : HtGT r HT w τ) (hL : LocGlobT ι r w τ)
    (hw : ∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) :
    Ord.AtLT ι h (r.comp (Dec (F := L) A).subtype) lam τ := _root_.UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n N l L Ω ι n A w h r HT τ lam k hL hw
end UpperTheory.V.Z.Desc.P
end
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
open UpperTheory.V.Z.Desc.P in
theorem UpperTheory.V.Z.Desc.P.partX_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, (Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ)) ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) := by
  intro PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY
  have P := PH.toClassicalTheorems
  have hAx := _root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hl : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hsp : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hw) w rfl
  have hspS : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv => hsp _ (by rw [hwv]; exact V.sub hv)
  have hspQ : ∀ q, IsSplitAt (Q.wq q) := fun q => hsp _ (by rw [Q.range]; exact Or.inr ⟨q, rfl⟩)
  have hin : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w.under (𝓞 (Lp L)) ∈ V.S' := fun w hw =>
    V.sub (Or.inl ((hl w).1 hw))
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hwt := partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
        (IsUnramU σ w → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w (n := n))) := fun w hw => by
    obtain ⟨τ, -, h1, h2⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    refine ⟨τ, h1, fun h => ?_⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h2.1 h)
    exact ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
  choose loc hloc hfix using hex
  obtain ⟨R, HT, hRc, hRs, hRu, hW, hLH, hpair, hcusp⟩ :=
    _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH PH L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ
  obtain ⟨ρ, hρc, rfl, hform⟩ := UpperTheory.exists_descent_to_level_group_of_unramified l L Ω s n V c R hRc fun w hw A hA =>
    hRu w (mt (hin w) hw) (hunr w hw) A hA
  have hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ := fun w hw τ hτ => (hLH w hw τ hτ).1
  have hHG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ := fun w hw τ hτ => (hLH w hw τ hτ).2
  have hall : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ :=
    fun w hw => ⟨_, hHG w (hsp w (hin w hw)) _ (hloc _ (hsp w (hin w hw)))⟩
  have hsat : ∀ w : (hset Q τ₀).Wp, ∃ a : ℕ → ℂ, a 0 = 1 ∧
      (∀ j, ∀ v ∈ fixd (loc w.1 w.2.2).ρ (KO (w.1.adicCompletion L) (Fin n)), sphOp (loc w.1 w.2.2).ρ j v = a j • v) ∧
      ∀ (B : ValuationSubring Ω) (g : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) g →
        (ρ (V.pr g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) a := fun w => by
    obtain ⟨b, hb'⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P L n w.1 _).1 (hfix w.1 w.2.2 (hunr _ w.2.1))
    obtain ⟨-, a, h0, h1, h2⟩ := satT L n w.1 _ b hb'
    have hw := mt (hin w.1) w.2.1
    refine ⟨a, h0, h1, fun B g hB hg => ?_⟩
    rw [← h2]
    exact (_root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P L Ω l ι n _ hRc w.1 hw _ b hb'
      (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG w.1 w.2.2 _ (hloc _ _)) hw) B hB).2 g hg
  choose a ha0 ha1 ha2 using hsat
  refine ⟨{ Y := YOf Q ι τ₀ e ξ σ
            le := inf_le_left
            ne := hY
            σl := fun v => loc (s.w v.1) (hspS _ (Or.inl v.2))
            isoL := fun v => partUR2IsoL l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ v _ (hloc _ _)
            σq := fun q => loc (Q.wq q) (hspQ q)
            isoQ := fun q => partUR2IsoQ l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx q _ (hloc _ _)
            a := a
            a_zero := ha0
            sph := fun w j => partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx w.1 w.2.1 w.2.2 _ (hloc _ _) j _
              (ha1 w j)
            r := ρ
            cont := hρc
            ss := fun M hM => ?_
            frob := ha2
            atL := fun v => _root_.UpperTheory.V.Z.Desc.P.ordinary_at_l_of_local_global_hodge_tate_weights P.litN (s.hw v.1) lam hall (hHG _ (hspS _ (Or.inl v.2)) _ (hloc _ _))
              (hLG _ (hspS _ (Or.inl v.2)) _ (hloc _ _)) fun j => hW _ _ (hwt ⟨v, j⟩)
            atQ := fun q => _root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspQ q) _ (hloc _ _)) (hAx.Q_away q) },
    ⟨rfl, ⟨?_, fun t ht u => ?_, fun hi => ?_, ?_⟩, fun v => hloc _ _, hLG⟩, fun hi => ?_⟩
  · obtain ⟨M', h1, h2⟩ := hRs M fun g => hM (V.pr g)
    refine ⟨M', fun g => ?_, h2⟩
    obtain ⟨g, rfl⟩ := hpr g
    exact h1 g
  · obtain ⟨P', hP'⟩ := hpair s.c s.hc
    exact ⟨P', hform P' hP'⟩
  · have hS : ∀ u : s.St, (u : Plc (Lp L)) ∈ s.S := fun u => Or.inr (Or.inl u.2)
    obtain ⟨rc, hrc⟩ : ∃ rc : IrrGL (k := (s.w u).adicCompletion L) → WD (s.hw u), _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc := P.exists_reciprocity_dense (s.hw u)
    have hT := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hτ t ht)
      (fun u => loc (s.w u) (hspS _ (hS u))) (fun u => hloc _ _) u rc hrc
    have hu : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => s.St_l u u.2 (by simpa only [hwv] using (hl _).1 h)
    obtain ⟨g, hg⟩ := UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD l L Ω ι n _ _ (s.hw u) hu (ρ.comp V.pr)
      (fun i => W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) _
      (_root_.UpperTheory.V.Z.Desc.P.woTypeT (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspS _ (hS u)) _ (hloc _ _)) hu _ (s.hw u) rc hrc)
        (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) hT) hT
    refine ⟨g, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hx⟩
  · obtain ⟨π, h1, h2, h3, h4, -⟩ := hcusp ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hI g⟩
    exact ⟨π, h1, h2, h3, fun v j => h4 _ _ (hwt ⟨v, j⟩)⟩
  · exact ⟨σ, hσ, hLG, hwt, hunr, fun w hw => ⟨_, hloc w hw⟩, loc _ (hspS _ (Or.inr (Or.inr rfl))), hloc _ _,
      partUR2V0 l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hloc _ _)⟩
  · obtain ⟨π, h1, h2, h3, -, h5, h6⟩ := hcusp hi
    exact ⟨π, h1, h2, h3, h5, h6⟩
theorem UpperTheory.V.Z.Desc.P.partU_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ :=
  fun PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY =>
    (_root_.UpperTheory.V.Z.Desc.P.partX_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY).imp fun _ h => h.1
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutCsdIso
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoAltAlt
noncomputable abbrev UpperTheory.V.Z.Win.WitA.isobaricDense := @UpperTheory.V.Z.Win.WitA.iso'
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
namespace UpperTheory.GalN.V
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
theorem autCsd_iso_alt {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).isobaricDense h⟩
end
def AutomorphyOverRationalsIsobaricDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r' → _root_.UpperTheory.V.Z.Win.IsAutQA ι r
theorem autQIsoN : _root_.UpperTheory.GalN.V.AutomorphyOverRationalsIsobaricDense := by
  intro F Ω _ _ _ _ l _ ι n r r' e h hc K _ _ _ _ _ _ h2 hi
  let φ : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have e' : RepIso (r.comp φ) (r'.comp φ) :=
    e.imp fun _ hg s => hg _
  have hi' : IsIrr (r'.comp φ) := by
    obtain ⟨g, hg⟩ := e'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    let T := Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) (Qbar l))
    have hcomm (s : G K Ω) : g * (r.comp φ) s = (r'.comp φ) s * g := by
      rw [hg s, inv_mul_cancel_right]
    have hcomap := hi.2.2 (W.comap T) le_top (fun s v hv => by
      change T ((↑((r.comp φ) s) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ W
      dsimp only [T]
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hcomm,
        Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hW s (T v) hv)
    have hsurj : Function.Surjective T := fun v =>
      ⟨(↑(g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [T]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hcomap with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  obtain ⟨⟨π, h1, h3⟩, hw⟩ := h (continuous_of_iso hc e) K h2 hi'
  exact ⟨⟨π, h1, attC_iso e'.symm' h3⟩, hw.isobaricDense e'.symm'⟩
end UpperTheory.GalN.V
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu
section
variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)
end
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
end
def SeedIVAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧ Supp nM s.r ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁)) ∧
          InA (Q.map (𝔞.red c₁)) ∧ Ent (Q.map (𝔞.red c₁)).r (-wBe) ∧ Ent (Q.map (𝔞.red c₁)).r (-wTh)
def ChainRankFour : Prop :=
  CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O)
    (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C →
    30 * (C + 1) * (C + 1) ≤ T.d → ∀ x : X.A →ₐ[c'.O] ResidueField c'.O,
      (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      Good4 (T.fr ∅) ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x)
def RankFourChainReductionDense : Prop :=
  CohomologyHyp → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → Four T₀ → TameL l T₀.F →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            Chain4 (T.fr ∅) (𝔞.red c) c₀' (Q.map (𝔞.red c₁))
def PromodularityCaseThreeDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r
def AutomorphyRankFourDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Ws.SeedIIAlt → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → _root_.UpperTheory.V.Aut.SymplecticFourImageDense
end UpperTheory.V.Cu
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFreeW
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
namespace UpperTheory.V.Z.Win.RR
theorem freePUA_alt : _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Continuous r → AutP ι r → WitA ι r → Th.Unl l M m r → FreeAt l r :=
  fun P K Ω _ _ _ _ _ _ hK l _ hl ι n hn r M m h1 h2 h3 h4 hW h5 => _root_.UpperTheory.V.Z.Win.RR.freeAt_of_autPA_of_unl_of_finrank_eq_two P K Ω hK l hl ι n hn r M m h1 h2 h3 ⟨h4, fun _ => hW⟩ h5
end UpperTheory.V.Z.Win.RR
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinPm
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.pmPur_w_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → PureW ι r := by
  intro hU Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hw r hr
  have hD : D.Good := hT.2.elim (fun a => a.1.1) fun a => a.1.1
  obtain ⟨wt, hwt⟩ := Pu.arith hU.pr.litN.aut.art K X B φ y hD hφ hw
  obtain ⟨ρ, -, hss, hρ, a, d, m, ρ', hd, hcp, hpure⟩ := _root_.UpperTheory.GalN.V.end1W' hM.end1 _ wt (K.le_ker_pt φ y J₀ (hJ ▸ hy)) hwt
  have hm := Pu.mOne c' ρ _ (chiO T.L Ω l c'.O) (cycBar T.L Ω l) (Pu.ptRed K.V B _ ρ hρ) rfl (Pu.noOm K hD hT.1) a d m ρ'
    (fun i => ⟨(hd i).1, (hd i).2.1⟩) hcp
  obtain ⟨Z, hZ, hZ'⟩ := Pu.levFin K.V
  refine Pu.pureOf_w ι T.L r ρ K.kapQ _ (hZ.union (Filter.eventually_cofinite.1 (hpure hm))) (fun g => ?_) fun w hw0 => ?_
  · rw [Pu.ptCp K X B φ y ρ hφ hρ g, ← hr]
    rfl
  · have hw : w ∉ Z := fun k => hw0 (Or.inl k)
    have hw' := not_not.1 fun k => hw0 (Or.inr k)
    obtain ⟨b, hb⟩ := Pu.frobEigEx ι ρ w fun A hA s hs => Pu.repKill K.V B _ ρ hρ hss s ((hZ' w hw).2 A hA s hs)
    exact Pu.frobAbs_w ι ρ w b hb (hw' b hb)
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section SlopeTestRemainingChoices
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end SlopeTestRemainingChoices
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1
private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]
theorem UpperTheory.V.Ws.fin0_no_end_all_irr_of_good_con_purity_aut :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Con D → _root_.UpperTheory.V.Ws.PurityAtPoints D ι → _root_.UpperTheory.V.Ws.AutmAlt D ι → D.Fin0 ∧ D.NoEnd ∧ D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) := by
  intro hP Ω _ _ _ l _ c D hD ι hC hPu hA
  obtain ⟨⟨𝔟, e, he⟩, -⟩ := ambZero l
  refine ⟨?_, ?_, ?_⟩
  · by_contra hF
    obtain ⟨𝔞, r, hch, hr, x, hx, hne⟩ := ptOver hP D hD hF
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔞 r hr
    rcases triV hP D hD 𝔞 r hr with h | h | ⟨h02, h20, h⟩
    · exact hC 𝔞 hch r u hu (Or.inl h)
    · obtain ⟨n, hn, hxn⟩ := diagConst D hD 𝔞 hch r hr u hu h x hx
      exact hne n hn hxn
    · obtain ⟨r₁, u₁, hu₁, hb, hs⟩ := blockPart D hD 𝔞 r hr u hu h02 h20 h
      obtain ⟨r₂, u₂, hu₂, hE, -⟩ := bl hP D hD 𝔞 r₁ u₁ hu₁ hb hs
      exact hC 𝔞 hch r₂ u₂ hu₂ (Or.inr hE)
  · intro r hr hb hs
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    have hb' : ∀ g, IsBlock (r' g) := fun g i j hij =>
      Subtype.ext (e.injective ((hb g i j hij).trans (map_zero e).symm))
    have hs' := span_of_equiv e (fun g => (mapRep 𝔟.toK r' g).submatrix ixA ixA) _ (fun _ _ _ => rfl) hs
    obtain ⟨r₂, u₂, hu₂, hE, hcp⟩ := bl hP D hD 𝔟 r' u hu hb' hs'
    refine nePure_w D hD ι 𝔟 e he r' u hu hb' ?_
    obtain ⟨H, M, hH, hM, h⟩ := _root_.UpperTheory.GalN.V.pureW' (hPu 𝔟 e he r₂ u₂ hu₂ (Or.inr hE))
    have hc := charpoly_mapRep ((e : 𝔟.K →+* PadicAlgCl l).comp 𝔟.toK) r₂ r' hcp
    refine ⟨H, M, hH, hM, fun p hp hpM A hA f σ hf hσ hF => ?_⟩
    rw [← hc]
    exact h p hp hpM A hA f σ hf hσ hF
  · intro r hr hI
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    exact hA 𝔟 e he r' u hu (span_of_equiv e (mapRep 𝔟.toK r') _ (fun _ _ _ => rfl) hI)
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OffDiagonalNilpotentRankFour
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
theorem UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ (v : T.ι) (i j : Fin 4), i ≠ j → ∀ (q : Ideal X.B), q.IsPrime → J ≤ q → (maximalIdeal c'.O).map (algebraMap c'.O X.B) ≤ q →
      (∀ s ∈ T.U1 v, X.ψ v i s - X.ψ v j s ∈ q) → ∀ dv : ℕ, dv * Nat.card T.ι = T.d → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * T.d + 1 : ℕ) := by
  classical
  intro _ Ω _ _ _ l _ c D T hFit _ ι c' h X J hPM v i j hij q hq hJ hϖ hU dv hdv
  have hOk := hFit.1
  have hl2 : l ≠ 2 := by
    rcases hFit.2 with h | h
    · exact h.1.1.l_odd
    · exact h.1.1.l_odd
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  haveI : Nonempty T.ι := ⟨v⟩
  have hg : 0 < Nat.card T.ι := Nat.card_pos
  haveI hcD : ∀ u, CompactSpace (Dec (F := T.F) (T.pl u)) := fun u =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (T.pl u)).isCompact
  let I : ∀ u, Subgroup (Dec (F := T.F) (T.pl u)) := fun u => (Ine (F := T.F) (T.pl u)).subgroupOf _
  have hs : ∀ u, ∃ s : Fin dv → Dec (F := T.F) (T.pl u), (∀ k, s k ∈ I u) ∧ Pins l (I u) (Set.range s) := fun u => by
    obtain ⟨w, hw, hlw, hd⟩ := UpperTheory.exists_place_over_l_locDeg_mul_card_eq D T u
    obtain ⟨A⟩ := UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place l (T.pl u) w hw hlw
    obtain rfl : locDeg w = dv := Nat.eq_of_mul_eq_mul_right hg (hd.trans hdv.symm)
    exact UpperTheory.exists_pinning_elements_of_locAb l _ _ _ A
  choose s hsI hsP using hs
  obtain ⟨s0, hs0, hP0⟩ := UpperTheory.exists_mem_pins_insert_ker_of_padic_character l hl2 _ (I v) ((isClosed_Ine (T.pl v)).preimage continuous_subtype_val)
    ((cycZ T.F Ω l).comp (Dec (F := T.F) (T.pl v)).subtype) ((continuous_cycZ T.F Ω l).comp continuous_subtype_val)
  obtain ⟨a, ha, ha'⟩ : ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧ ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧
      ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev) i j hij
  let x : (T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit → X.B :=
    Sum.elim (fun y => X.ψ y.1 a (s y.1 y.2) - 1)
      (Sum.elim (fun y => X.ψ y.1.1 i (s y.1.1 y.2) - 1) fun _ => X.ψ v i s0 - X.ψ v j s0)
  have hm : ∀ u m (t : Dec (F := T.F) (T.pl u)), t ∈ I u → X.ψ u m t - 1 ∈ maximalIdeal X.B := fun u m t ht => by
    obtain ⟨-, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (residue X.B) (fun b hb => by
      rw [(residue_eq_zero_iff b).2 hb]; exact zero_mem _) (fun b hb => (residue_eq_zero_iff _).2 (map_nonunit _ b hb))
    have h1 := ((hκ u m).2.2 t ht).1
    rw [(hκ u m).1, maximalIdeal_eq_bot, Ideal.mem_bot, ← map_one (residue X.B), ← map_sub, residue_eq_zero_iff] at h1
    exact h1
  have hdim := UpperTheory.krullDim_quotient_le_card_of_radical_parameters X.B q _ x ?_ ?_
  · have hc : Nat.card ((T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit) + dv = 2 * T.d + 1 := by
      have h1 : Nat.card {u // u ≠ v} + 1 = Nat.card T.ι := by
        rw [← Finite.card_option]
        exact Nat.card_congr (Equiv.optionSubtypeNe v)
      simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin dv), Fintype.card_fin, Nat.card_unique]
      rw [← hdv, ← h1]
      ring
    rw [← hc, Nat.cast_add]
    gcongr
  · rintro (y | y | y)
    · exact hm _ _ _ (hsI _ _)
    · exact hm _ _ _ (hsI _ _)
    · simpa [x] using sub_mem (hm v i s0 hs0) (hm v j s0 hs0)
  intro p hp hqp hx
  haveI : IsLocalRing (X.B ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨h0, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (Ideal.Quotient.mk p) (fun b hb => map_nonunit _ b hb)
    (fun b hb => Ideal.Quotient.eq_zero_iff_mem.2 (hqp (hϖ (Ideal.mem_map_of_mem _ hb))))
  have h1 : ∀ u m (t : Dec (F := T.F) (T.pl u)), κ u m t = 1 ↔ X.ψ u m t - 1 ∈ p := fun u m t => by
    rw [← Units.val_eq_one, (hκ u m).1, ← Ideal.Quotient.eq, map_one]
  have hpin : ∀ u m, (∀ k, X.ψ u m (s u k) - 1 ∈ p) → ∀ t ∈ I u, κ u m t = 1 := fun u m hk =>
    hsP u _ h0 (κ u m) (hκ u m).2.1 (fun t ht => ((hκ u m).2.2 t ht).1) (by
      rintro _ ⟨k, rfl⟩; exact (h1 _ _ _).2 (hk k))
  have hA : ∀ u, ∀ t ∈ I u, κ u a t = 1 := fun u => hpin u a fun k => hx (.inl (u, k))
  have hE : ∀ t ∈ I v, κ v i t = κ v j t := by
    refine hP0.eq h0 _ _ (hκ v i).2.1 (hκ v j).2.1 (fun t ht => ((hκ v i).2.2 t ht).1)
      (fun t ht => ((hκ v j).2.2 t ht).1) fun t ht => Units.ext ?_
    rw [(hκ v i).1, (hκ v j).1, Ideal.Quotient.eq]
    rcases ht with rfl | ⟨ht, ht'⟩
    · exact hx (.inr (.inr ()))
    · exact hqp (hU t ⟨ht, ht', hOk.ineL _ (T.ovl v) _ ht⟩)
  have hI : ∀ u, ∀ t ∈ I u, κ u i t = 1 := fun u => by
    by_cases hu : u = v
    · subst hu
      intro t ht
      rcases ha with rfl | rfl
      · exact (hE t ht).trans (hA u t ht)
      · have h2 := (hκ u i).2.2 t ht
        refine Units.val_eq_one.1 (eq_one_of_pow h0 h2.1 two_ne_zero ?_)
        rw [← Units.val_pow_eq_pow_val, sq, Units.val_eq_one]
        rw [← hE t ht] at h2
        exact h2.2
    · exact hpin u i fun k => hx (.inr (.inl (⟨u, hu⟩, k)))
  have hall : ∀ u m, ∀ t ∈ I u, κ u m t = 1 := fun u m t ht => by
    rcases ha' m with rfl | rfl | rfl | rfl
    · exact hA u t ht
    · simpa [hA u t ht] using ((hκ u a).2.2 t ht).2
    · exact hI u t ht
    · simpa [hI u t ht] using ((hκ u i).2.2 t ht).2
  obtain ⟨n, hn⟩ := hPM.fin
  refine hp.le_of_pow_le (n := n) (hn.trans (sup_le (sup_le (hJ.trans hqp) (hϖ.trans hqp)) (Ideal.span_le.2 ?_)))
  rintro _ ⟨u, m, t, ht, rfl⟩
  exact (h1 u m ⟨t, Ine_le_Dec _ ht⟩).1 (hall u m _ ht)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Link2
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
theorem link2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : Plc E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2)
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hρc : Continuous ρ) (hρi : Af.IsIrr ρ)
    (hρF : ∀ᶠ w : Plc E in Filter.cofinite, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B →
        Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨r, HT, hc, hs, -, -, hLG, -, hcusp⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl2 ι n hn σ hσ
  have hoff : ∀ᶠ w : Plc E in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hunram : ∀ᶠ w : Plc E in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hagree : ∀ᶠ w : Plc E in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι ρ w B := by
    filter_upwards [hoff, hunram, hρF] with w hl hu hw hd
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    obtain ⟨τ, hτ⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E n σ hσ w hsp).1
    obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hσ hsp τ.ρ hτ hu)
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨_, _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hl hB (hLG w hsp τ hτ).1, hw hsp τ hτ B hB⟩
  have hρss : IsSSRep ρ := fun M hM => by
    rcases hρi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hρi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have e : Af.RepIso r ρ := by
    have hchar := UpperTheory.V.Af.Es.charpoly_eq_prod ι (I := Unit) (a := fun _ => n)
      r (fun _ => ρ) hc (fun _ => hρc) (hagree.mono fun w h hd => by
        obtain ⟨B, h1, h2⟩ := h hd
        exact ⟨fun _ => B, by simpa using h1, fun _ => h2⟩)
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix
      r ρ hs hρss (fun g => by simpa using hchar g)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hri : Af.IsIrr r := by
    obtain ⟨P, hP⟩ := Af.RepIso.symm' e
    refine ⟨hρi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hi : IsInv ρ (M.comap T.toLinearMap) := fun g v hv => by
      have h1 := hM g _ hv
      change (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) ∈ M at h1
      change T _ ∈ M
      have e1 : P * ρ g = r g * P := by rw [hP g, inv_mul_cancel_right]
      rw [hT, Matrix.mulVec_mulVec, ← Units.val_mul, e1, Units.val_mul,
        ← Matrix.mulVec_mulVec, ← hT]
      exact h1
    have hm := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hρi.2.2 _ le_top hi with h0 | h1
    · left
      rw [hm, h0, Submodule.map_bot]
    · right
      rw [hm, h1, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, p1, p2, p3, -, p4, p5⟩ := hcusp hri
  refine ⟨π, p1, p2, ⟨hρss, p3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩, p4, fun w hw τ => ⟨p5 w hw τ, fun hτ => ?_⟩⟩
  obtain ⟨τ', hτ'⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact (GlobalTheory.BCT.isLocComp_iff_equiv hτ' τ).2 (UpperTheory.building_component_uniqueness E n σ hσ w hw _ _ _ _ hτ (p5 w hw τ' hτ'))
end UpperTheory.Gal.projectedFormsSystemPart
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FFreeCU
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _
private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
theorem UpperTheory.V.Z.J.free_at_of_unlinked_of_automorphic_cyclotomic_twist :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (a : ℤ) (M : ℕ) (m : Fin n → ℤ), Continuous r →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw r (cycBar F Ω l ^ a)) → 1 ≤ M → StrictAnti m → Unl l M m r → FreeAt l r := by
  intro P F Ω _ _ _ _ _ _ l _ hl ι n hn r a M m hr haut hM hm hun A' hA'
  obtain ⟨w, hw', hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A' l).2 hA'
  obtain ⟨A, hA, κ, ⟨χ, hk, ⟨g, hg⟩, hκ⟩, hne⟩ := hun w hw
  have hAl : A.valuation (l : Ω) < 1 := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).1 ⟨w, hA, hw⟩
  obtain ⟨k, hk0, hkf⟩ := pow_fixes F Ω hM
  have hz : Continuous fun s : G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ F Ω l)
  have hcyc : Continuous fun s : G F Ω => (cycBar F Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G F Ω => cycBar F Ω l s ^ a := (cont_units _ hcyc).zpow a
  have hc : Continuous (tw r (cycBar F Ω l ^ a)) := by
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  obtain ⟨s, hs1, hs2⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar P F Ω l hl ι n hn _ hc haut A hAl
    (fun i => κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) (fun i => m i + a) k
    (flag_tw r _ _ κ g hg)
    (fun i j hij => by have := hm hij; dsimp only; omega) hk0
    (fun i s hs => by
      show (κ i s * cycBar F Ω l s ^ a * cycBar F Ω l s ^ (-(m i + a))) ^ k = 1
      rw [hκ i s hs, mul_right_comm _ (χ i s), ← zpow_add, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul,
        ← map_pow]
      exact hk i _ (hkf s))
    (by
      intro i j e
      apply hne i j
      rw [mul_right_comm] at e
      exact mul_right_cancel e)
  have hb : cycBar F Ω l s = 1 := by
    simp only [cycBar, MonoidHom.comp_apply, hs1, map_one]
  have hfr : Pr.FreeRatios fun i => κ i s := by
    have e : (fun i => (κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) s) = fun i => κ i s := by
      funext i
      show κ i s * cycBar F Ω l s ^ a = κ i s
      rw [hb, one_zpow, mul_one]
    rwa [e] at hs2
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hw'
  refine ⟨t * s * t⁻¹, ?_, ?_, fun i => κ i s, hfr, ?_⟩
  · rw [mem_Dec, mul_smul, inv_smul_smul, mul_smul, mem_Dec.1 s.2]
  · rw [map_mul, map_mul, hs1, mul_one, map_inv, mul_inv_cancel]
  · have e : r (t * s * t⁻¹) = (r t * g⁻¹) * (g * r s * g⁻¹) * (r t * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    show (r (t * s * t⁻¹)).val.charpoly = _
    rw [e, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end
end
