module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.EvenOnto.LiftUp

theorem liftUp_stage_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  intro hDS hHC hCD hCW D c k s s' ω f hc hk hs _hs' hp
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hIn : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X hIn (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X hIn (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X hIn)))
  have hW := hp.weil
  have hstd : IsStdChar D c.ψ (-1) := hW.std
  have hadj : AdjLaw c.ψ s.V s'.V := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D c.ψ hstd s.V s'.V
  have h0 : adjO s.V s'.V 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D c.ψ s.V s'.V (c.χ k) (c.χ k) ω hW
  obtain ⟨j, -, hj⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D c.ψ c.θ hstd hc.inf s.V s'.V (Fr.ofModel s.M) (Fr.ofModel s'.M)
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hp.vac)
  have hω'e : IsWeilExp c.ψ s'.V s.V (c.a k) (c.a k) ω' :=
    ⟨c.χ k, c.χ k, hW', fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  have hne : dag s.V s'.V f ≠ 0 := by
    intro hz
    apply hp.vac.ne
    funext x
    have hx := congrFun hz (adjO s'.V s.V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec c.ψ c.θ s'.M s.M (dag s.V s'.V f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair hDS hHC D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf hp.par).2
  have hItW := hIt ω' (dag s.V s'.V f) hω'e hf'
  have hrule : ∀ τ, RulePar X (s'.par τ) (s.par τ) (c.a k τ) (c.a k τ) :=
    fun τ => ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t _ _ _ _ (hp.par τ)).2 X h3 h4 h5).2
  have hL := hPL _ _ _ _ hrule s'.V s.V s'.M s.M c.θ c.ψ hc.inf ω' hω'e (dag s.V s'.V f) It hf' hItW s.ν s.fd hs.haar hs.fund
    (dag s.V s'.V f) (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v =>
    GlobalTheory.T.real_intertwiner_values_kFinite D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf' hItW (j P) v, ?_, ?_⟩
  · refine (GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf'
      hItW).trans (Submodule.span_mono ?_)
    rintro w ⟨P, v, -, rfl⟩
    exact ⟨j.symm P, v, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf c.ψ c.θ s.M s'.M f P)) =
        thetaKO ω' h g (ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P)) := by
      intro g
      have e1 : ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P) = dag s.V s'.V (ptOf c.ψ c.θ s.M s'.M f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.EvenOnto.LiftUp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  first | exact @GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | exact GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | (intros; apply GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto.UpLift

variable {D : D7}

theorem multT_le_noLevel' {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem upSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' p hp u φ v _hv
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors h1 h2 h3 h4 D c k s s' p.ω p.f hc hk hs hs' hp.pre
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel' c.θ s.M _ _ u.2)
  have hlaw : ∀ P v', ∀ κ ∈ s'.J, ∀ g, F' (T P v') (g * κ) = F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) =
        thetaKO p.ω g' g (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := hp.pre.law P 1 (one_mem _) κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, h2]
    simp only [hω]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact hs'.fin hκ
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', rfl⟩ := hx
        simpa using hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

theorem upAdj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D c hc k hk s s' hs hs' p hp u y φ v _ w _
  have hru : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) :=
    ((GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hP D c hc k hk.le s hs).1 u v).2.2.2.2
  have hry : GlobalTheory.Grow.RapidDec s'.V (PiLocalization₂.val y w) :=
    ((GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hP D c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs').1 y w).2.2.2.2
  have hF := GlobalTheory.T.thetaKernel_iterated_integrals_swap D c.ψ c.θ s.V s'.V (c.χ k) (c.χ k) p.ω hc.inf hp.pre.weil (p.pt φ)
    (GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua D c hc k hk s s' hs hs' p hp φ).1
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w) hru hry
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

theorem upSpan_upAdj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D ∧ UpAdj D :=
  fun h1 h2 h3 h4 D => ⟨upSpan h1 h2 h3 h4 D, upAdj h3 D⟩

end GlobalTheory.EvenOnto.UpLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpward_cuspSpan_and_adjoint : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D ∧ UpAdj D := by
  first | exact @GlobalTheory.EvenOnto.UpLift.upSpan_upAdj | exact GlobalTheory.EvenOnto.UpLift.upSpan_upAdj | (intros; apply GlobalTheory.EvenOnto.UpLift.upSpan_upAdj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie

section Place

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem complMap_apply_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} {w : Pl E} (h : w.under (𝓞 F) = v) (b : Af F) :
    complMap h (b v) = GlobalTheory.AdeleBaseChange.locMap F w (b (w.under (𝓞 F))) := by
  subst h; rfl

theorem piW_tmul (b : AF D.host.F) (x : D.host.E) : piW τ (b ⊗ₜ[D.host.F] x) = evFin D.host.F v b * τ x := by
  show splitProj τ (compFin D.host.F D.host.E v (b ⊗ₜ[D.host.F] x)) = _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem cpt_tmul (w : Pl D.host.E) (b : AF D.host.F) (x : D.host.E) :
    cpt (D := D) w (toEAf D (b ⊗ₜ[D.host.F] x)) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.locMap D.host.F w (b.2 (w.under (𝓞 D.host.F))) := by
  have e : toEAf D (b ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] b.2 := rfl
  rw [e]
  show (toAd D (x ⊗ₜ[D.host.F] b.2)) w = _
  rw [toAd_spec]
  rfl

theorem isPlaceIso_complEquiv : IsPlaceIso τ (splitPrime τ) (complEquiv τ (splitPrime_under τ)) := by
  intro a
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [piW_tmul, cpt_tmul, complEquiv_apply, map_mul, complMap_apply_emb, mul_comm]
    congr 1
    exact complMap_apply_under (splitPrime_under τ) b.2
  | add x y hx hy =>
    rw [RingHom.map_add (piW τ), RingEquiv.map_add (e := _), RingHom.map_add (toEAf D), RingHom.map_add (cpt _), hx, hy]

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) :
    (ValuativeRel.valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((complEquiv τ (splitPrime_under τ)).symm y) = Valued.v y := by
  conv_rhs => rw [← (complEquiv τ (splitPrime_under τ)).apply_symm_apply y]
  rw [complEquiv_apply, SplitTie.valued_complMap]

theorem continuous_complEquiv_symm : Continuous (complEquiv τ (splitPrime_under τ)).symm := by
  refine continuous_of_continuousAt_zero (complEquiv τ (splitPrime_under τ)).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv : IsLocIso (complEquiv τ (splitPrime_under τ)) := by
  refine ⟨SplitChart.continuous_complMap _, continuous_complEquiv_symm τ, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    (isEquiv_Fv v).le_one_iff_le_one, complEquiv_apply, SplitTie.valued_complMap]

end Place

section Chars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem chrW_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (hα : X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (hβ : X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
    {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : (Fv D.host.F v)ˣ) :
    chrW X.ν τ x = (locGrid G t (splitPrime τ)).nu i j
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := by
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hα, hβ]
    exact mul_div_mul_right_eq_div _ _ _
  have e2 : chrW X.ν τ x = locChar X.ν (splitPrime τ)
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := rfl
  rw [e2, e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, div_eq_mul_inv]
  rfl

end Chars

section Psi

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem at_atPl {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : Kw (D := D) (splitPrime τ)) :
    At (evFin D.host.F v) (atPl (splitPrime τ) y) := by
  classical
  intro u hu
  refine ae_ext ?_ fun Q => ?_
  · rw [Algebra.smul_def, RingHom.map_mul, (atPl_spec _ y).1, mul_zero, map_zero]
  · rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, (atPl_spec _ y).2, map_zero, map_zero]
    by_cases h : Q = splitPrime τ
    · subst h
      have h1 : cpt (D := D) (splitPrime τ) (toEAf D (algebraMap (AF D.host.F) (AE D) u)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F (splitPrime τ) (u.2 ((splitPrime τ).under (𝓞 D.host.F))) :=
        (comp_toAd D).base u (splitPrime τ)
      rw [h1, ← complMap_apply_under (splitPrime_under τ)]
      have h2 : u.2 v = 0 := hu
      rw [h2, map_zero, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]

theorem psiLoc_eq_psiAt (W : G.Weil) {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Fv D.host.F v) :
    psiLoc W.ψ v x = psiAt W (splitPrime τ) ((xiAt (splitPrime τ))⁻¹ * complEquiv τ (splitPrime_under τ) x) := by
  classical
  set w := splitPrime τ with hw
  set jj := complEquiv τ (splitPrime_under τ) with hjj
  have hξ : xiAt (D := D) w ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have hz : incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x) = atPl w (jj x) := by
    rw [← Good.atPl_mul]
    congr 1
    rw [← mul_assoc]
    change xiAt w * (xiAt w)⁻¹ * jj x = jj x
    rw [mul_inv_cancel₀ hξ, one_mul]
  have hcm := isCMExt_host D
  have hp1 : piW τ (atPl w (jj x)) = x :=
    jj.injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec w _).2, Pi.single_eq_same])
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl w (jj x)) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec w _).2, Pi.single_eq_of_ne (splitPrime_comp_ne hcm τ),
        map_zero])
  show psiLoc W.ψ v x = W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x)))
  rw [hz, GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v τ _ (at_atPl τ _), hp1, hp2, add_zero]
  rfl

end Psi

theorem exists_placeIso_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  intro D T L sc G μ₀ hL W t i j X hα hβ v τ w hw
  subst hw
  exact ⟨complEquiv τ (splitPrime_under τ), isPlaceIso_complEquiv τ, isLocIso_complEquiv τ,
    fun x => chrW_nu hL t i j X hα hβ τ x, fun x => psiLoc_eq_psiAt W τ x⟩

end GlobalTheory.FlipMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placeIso_reading_components_characters : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  first | exact @GlobalTheory.FlipMatch.exists_placeIso_chars | exact GlobalTheory.FlipMatch.exists_placeIso_chars | (intros; apply GlobalTheory.FlipMatch.exists_placeIso_chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceLaw
variable {D : D7}

theorem omegaG_levelDatum_zero_indep_chars (a r t : ℕ) (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {b : ℕ}
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG (Lev.datY a r t 0 ha Pg ∅ P χ ξ Lev.Frm.B) χj y = omegaG (Lev.datY a r t 0 ha Pg ∅ P χ' ξ' Lev.Frm.B) χj y := by
  unfold omegaG
  rfl


open GlobalTheory.AdjDatumMove in
theorem levelDatum_target_under_sourceLevel_element (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (r t : ℕ) (ha : r ≤ T.rank) (hb : r ≤ S.rank) (hTS : T.rank ≤ S.rank) (ea : T.rank = r + 0 * t)
    (eb : S.rank = r + (0 + 1) * t)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D)
    (g : GA D S) (sg : finE S g ∈ St βS)
    (hG : ∀ PP ∈ Pg, redFn βS PP (finE S g) ∈ blockTri (blkOf r t))
    (hP : (fun PP : ↥Pg => upperLeftBlock hb (redFn βS PP.1 (finE S g))) ∈ P.H)
    (hQ : ∀ PP ∈ Q, redFn βS PP (finE S g) ∈ blockTri (blk2 T.rank)) (x : WO S T) :
    GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e
                 (actO S T g⁻¹ 1⁻¹ x) =
      ((((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (0 + 1),
            m PP (dBlk (blkOf r t) (i + 1) (redFn βS PP (finE S g))))⁻¹ *
          ∏ PP ∈ Pg, m PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, (((m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hTS (redFn βS PP (finE S g))⁻¹)))⁻¹ : ℂˣ) : ℂ)) *
      GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e x := by
  have sg' : finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem sg
  have s1 : finE T (1 : GA D T)⁻¹ ∈ St βT := by rw [inv_one, map_one]; exact one_mem _
  have hγ : ∀ PP, redFn βS PP (finE S g⁻¹) = (redFn βS PP (finE S g))⁻¹ := fun PP => by rw [map_inv, redFn_inv sg]
  have h1' : ∀ PP, (redFn βT PP (finE T (1 : GA D T)⁻¹))⁻¹ = 1 := fun PP => by
    rw [inv_one, map_one, redFn_one, inv_one]
  unfold GlobalTheory.FinZeta.levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT sg' s1 hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T g⁻¹ 1⁻¹ x)) =
        ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x) := fun PP => by
      rw [h1.2 PP, hγ PP, h1' PP, Units.val_one, Matrix.mul_one]
    have hq := omegaQ_mul hTS Q m (fun PP => (redFn βS PP (finE S g))⁻¹) (fun _ => 1) (fun PP hP => inv_mem (hQ PP hP))
      (fun PP => redM PP (frMapAdj S T βS βT x))
    simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, mul_one] at hq
    have hm := GlobalTheory.ChainOnto.omegaG_levelP_move D T.rank S.rank r t 0 ha hb ea eb Pg P (fun _ => m) (fun _ => 1)
      (fun PP => redFn βS PP (finE S g)) hG hP (fun PP => redM PP (frMapAdj S T βS βT x))
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2, hq,
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x)),
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => redM PP (frMapAdj S T βS βT x)), hm]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T g (1 : GA D T) x
    have h3 := isHalf_actO' g (1 : GA D T) h1
    have h4 := (red_actO S T βS βT sg (by rw [map_one]; exact one_mem _) h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw


open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
set_option maxHeartbeats 1000000 in
theorem om_src_law {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (h : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io) (κ : GA D (Vc D i))
    (hκ : κ ∈ Lev.levA (Vc D i) (levV R i t P m)) :
    ω (κ, 1) f = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • f := by
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hκG : κ ∈ GfC (Vc D i) := (Subgroup.mem_inf.1 hκ).1
  have hκL : finE (Vc D i) κ ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m) := (Subgroup.mem_inf.1 hκ).2
  have sV : finE (Vc D i) κ ∈ St (R.βV i) := parLev_St hκL.1
  have sW : finE (Wc D i) 1 ∈ St (R.βW i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => GlobalTheory.ZetaLaw.isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW
    fV fW hvac he (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 hκG (one_mem _) sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hb : D.R.r ≤ (Vc D i).rank := (datV i R.Pg (R.Q t) P m).hr
  have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 (Wc D i).rank) := fun PP hP => by
    rw [rW]; exact parLev_q hκL.1 hP
  have hlaw := levelDatum_target_under_sourceLevel_element (Vc D i) (Wc D i) (R.βV i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) hb hr (by rw [rW]; ring)
    (by rw [rV]; ring) R.Pg (R.Q t) P m e κ sV (fun PP hP => parLev_g hκL.1 hP) hκL.2 hQ
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW κ 1 sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t).1
  have hQf : ∀ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ *
      (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := fun PP hP => by
    have h1 := (GlobalTheory.VecInv.TwoBlockDet.det_blocks (kP PP) _ _ 0 hr (redFn (R.βV i) PP (finE (Vc D i) κ))).1 (hQ PP hP)
    have e1 : dBlk (blk2 (Wc D i).rank) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) =
        dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) := by rw [rW]
    have e2 : upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹ = (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ)))⁻¹ :=
      extendOne_inv _ (hQ PP hP)
    rw [e2, map_inv, map_inv, inv_inv, h1, e1, map_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel,
      one_mul]
  have hone : ∀ PP, m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) 1))) = 1 := fun PP => by
    rw [map_one, redFn_one, map_one, map_one]
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hκL.2]
  have hchi : (datV i R.Pg (R.Q t) P m).P.chi ⟨rTup (R.βV i) (datV i R.Pg (R.Q t) P m) (finE (Vc D i) κ), hκL.2⟩ =
      P.chi ⟨fun PP => upperLeftBlock hb (redFn (R.βV i) PP.1 (finE (Vc D i) κ)), hκL.2⟩ := rfl
  rw [hchi]
  simp only [IndefiniteRowSideFullHecke.TwistedLevelValues.datV, hone, mul_one]
  rw [← Units.coe_prod, ← Units.val_mul, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [Finset.prod_union hd]
  have hX2 : (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) *
      ∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hQf, Finset.prod_inv_distrib]
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) = X2 at hX2 ⊢
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹) = Z at hX2 ⊢
  obtain rfl : X2 = (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ * Z⁻¹ := by
    rw [← hX2, mul_inv_cancel_right]
  rw [Finset.prod_inv_distrib]
  simp only [zero_add]
  rw [show (R.datWp i P).Pg = R.Pg from rfl]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

theorem sourceLevelLaw : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io h κ hκ Q
  have hf := om_src_law R F i t σ s P cμ cη m ω BW f₀ f c io h κ hκ
  obtain ⟨hC, -, -, -, -, hW, -, -, hpt, -, -⟩ := h
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hC.models.inf hW _ _ _ _ f hpt κ
    (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ hf Q

end GlobalTheory.SourceLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_sourceLevelCharacter_law : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  first | exact @GlobalTheory.SourceLaw.sourceLevelLaw | exact GlobalTheory.SourceLaw.sourceLevelLaw | (intros; apply GlobalTheory.SourceLaw.sourceLevelLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FirstRowEndLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
def stepType (L : LevCh D T) (t : T) (w : Pl D.host.E) (j : ℕ) : TypeDatum (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) :=
  if w ∈ L.Pg then
    (TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j
  else if h : w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹ then parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ h.2
  else TypeDatum.full _ _


open Classical in
def endLamAt (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ) (κ : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)) : ℂ :=
  if h : (reGL (ixFin G t w j)).symm κ ∈ (stepType L t w j).J then (((stepType L t w j).lam ⟨_, h⟩)⁻¹ : ℂˣ) else 1

def endLam (G : GridData L sc) (t : T) (w : Pl D.host.E) (κ : GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w)) : ℂ :=
  endLamAt G t w D.R.m κ

end GlobalTheory.FirstRowEndLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalCoeffSpan
namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgCoeff

open MeasureTheory

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem coeffSpan_finiteDimensional {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | (apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan ..)

theorem coeffSpan_mulRight {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (k' : K)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) : (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
  exact this hf

end GlobalTheory.AvgCoeff

namespace GlobalTheory.CuspKFin

open Formalism.REAL GlobalTheory.Published.AutFin GlobalTheory.AvgCoeff

theorem kFinAt_avg_of_kFinAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ),
    GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  intro D θ hθ N ψ hψ τ τ' e he hK
  obtain ⟨W, i1, i2, i3, ρ, hρc, hρ⟩ := hK
  refine ⟨W, i1, i2, i3, ρ, hρc, fun x => ?_⟩
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := coeffSpan_finiteDimensional ρ
  have hec : Continuous e := by
    obtain ⟨F, -, heF, hc, -⟩ := he
    exact hc e heF
  have hAc : Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ').comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
      fun k => conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k
  have hmem : ∀ k' : Formalism.REAL.KG (N.M.ε τ'), (fun k => ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro k'
    by_cases h : τ' = τ
    · subst h
      have h2 := coeffSpan_mulRight ρ k' (hρ x)
      convert h2 using 2 with k
      rw [mul_assoc]
      congr 2
      simp only [kAt]
      rw [← GlobalTheory.SeriesToClosure.at_mul hθ (N.M.fr_unit τ') (N.M.fr_gram τ')
        (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k'))]
      rfl
    · have hc : ∀ k, kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') =
          atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k := fun k =>
        GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm h) _
          (conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) _ (conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k')
      have h2 := hρ (x * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))
      convert h2 using 2 with k
      rw [mul_assoc, hc, ← mul_assoc]
  have hcont : ∀ k, Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')) := fun k =>
    hec.mul (hψ.cont.comp (continuous_const.mul hAc))
  have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ')) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun k' k => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')))
    (fun k' => Submodule.smul_mem _ (e k') (hmem k')) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
  exact key

end GlobalTheory.CuspKFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFinitenessStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_preserves_K_finiteness : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | exact GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical


open Matrix in
theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inMaxCompactOfModelFrame_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.CuspGK.InK M τ g → GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  first | exact @GlobalTheory.CuspGK.inK_inv | exact GlobalTheory.CuspGK.inK_inv | (intros; apply GlobalTheory.CuspGK.inK_inv <;> assumption)
end
end
