module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProducStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrTestVec

theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end GlobalTheory.SchrTestVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_schroedingerFixed_localField : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  first | exact @GlobalTheory.SchrTestVec.exists_fixed | exact GlobalTheory.SchrTestVec.exists_fixed | (intros; apply GlobalTheory.SchrTestVec.exists_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AdelicFourierUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t2Space_infiniteAdeleRing_of_numberField : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI := secondCountable_completion F
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI := t2Space_infiniteAdeleRing_of_numberField F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_AF : SecondCountableTopology (AF F) := by
  haveI := secondCountable_inf F
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem continuousAdd_AE : ContinuousAdd (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  IsModuleTopology.toContinuousAdd (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))

def homAE : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) ≃ₜ (Fin (Module.finrank F E) → AF F) :=
  haveI := continuousAdd_AE F E
  let e := (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem t2Space_cm_host_adeles : T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
  haveI := t2Space_adeleRing_of_numberField F
  exact (homAE F E).isEmbedding.t2Space

theorem secondCountable_AE : SecondCountableTopology (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
  haveI := secondCountable_AF F
  exact (homAE F E).isEmbedding.secondCountableTopology

theorem locallyCompact_AE : LocallyCompactSpace (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (homAE F E).isClosedEmbedding.locallyCompactSpace

theorem topAddGroup_AE : IsTopologicalAddGroup (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  IsModuleTopology.topologicalAddGroup (R := AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))

end GlobalTheory.AdelicFourierUniq


open GlobalTheory.AdelicFourierUniq in
theorem GlobalTheory.AdelicFourierUniq.eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → AE F E) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → AE F E) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  intro F E _ _ _ _ _ ψ hψ d A _ p hp hsep μ hμ N hN hi h
  letI : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI := t2Space_cm_host_adeles F E
  haveI := secondCountable_AE F E
  haveI := locallyCompact_AE F E
  haveI := topAddGroup_AE F E
  have hp0 : p 0 = 0 := by simpa using hp 0 0
  refine GlobalTheory.CharFourierInj.eq_zero (fun a u => ψ (p a u))
    (fun a => hψ.1.comp (IsModuleTopology.continuous_of_linearMap (R := AF F) (p a)))
    (fun a x y => by simp only [map_add (f := _), AddChar.map_add_eq_mul])
    (fun a b x => by simp only [hp, LinearMap.add_apply, AddChar.map_add_eq_mul])
    (fun x => by simp only [hp0, LinearMap.zero_apply, AddChar.map_zero_eq_one])
    (fun a x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _) hsep μ N hN hi h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanishStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  first | exact @GlobalTheory.AdelicFourierUniq.eq_zero | exact GlobalTheory.AdelicFourierUniq.eq_zero | (intros; apply GlobalTheory.AdelicFourierUniq.eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivMapsOpenFiniteSubgroupToOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivMapsOpenFiniteSubgroupToOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

theorem fintrans_cont (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    Continuous B :=
  IsModuleTopology.continuous_of_linearMap B.toLinearMap

def finIdem (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F := (0, 1)

theorem finIdem_mul (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    finIdem F * a = (0, a.2) := by
  change ((0 : InfiniteAdeleRing F) * a.1, (1 : FiniteAdeleRing (𝓞 F) F) * a.2) = _
  rw [zero_mul, one_mul]

theorem finiteAdelesVecPairAsAdeles_eq_idempotent_smul (F : Type) [Field F] [NumberField F] (κ : Type)
    (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F m = finIdem F • finE2 F m := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.1 i)); rw [finIdem_mul]; rfl
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.2 i)); rw [finIdem_mul]; rfl

theorem finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    finIdem F • w = finE2 F (fun i => (w.1 i).2, fun i => (w.2 i).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change finIdem F * w.1 i = _; rw [finIdem_mul]; rfl
  · change finIdem F * w.2 i = _; rw [finIdem_mul]; rfl

theorem finiteAdelesVecPairAsAdeles_add (F : Type) [Field F] [NumberField F] (κ : Type)
    (a b : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F (a + b) = finE2 F a + finE2 F b := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change ((0 : InfiniteAdeleRing F), a.1 i + b.1 i) = ((0 : InfiniteAdeleRing F) + 0, a.1 i + b.1 i)
    rw [add_zero]
  · change ((0 : InfiniteAdeleRing F), a.2 i + b.2 i) = ((0 : InfiniteAdeleRing F) + 0, a.2 i + b.2 i)
    rw [add_zero]

theorem finiteAdelesVecPairAsAdeles_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    finE2 F (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rfl

theorem fintrans : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  intro F _ _ κ _ B M hM
  let g : ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →+
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    { toFun := fun m' => (fun i => ((B.symm (finE2 F m')).1 i).2, fun i => ((B.symm (finE2 F m')).2 i).2)
      map_zero' := by
        simp only [finiteAdelesVecPairAsAdeles_zero, map_zero]; rfl
      map_add' := fun a b => by
        simp only [finiteAdelesVecPairAsAdeles_add, map_add (f := _)]; rfl }
  have hg : ∀ m', finE2 F (g m') = B.symm (finE2 F m') := by
    intro m'
    rw [finiteAdelesVecPairAsAdeles_eq_idempotent_smul F κ m', map_smul, finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair]
    rfl
  have hgc : Continuous g := by
    have h1 : Continuous fun m' : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => B.symm (finE2 F m') := by
      refine (fintrans_cont F κ B.symm).comp ?_
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_fst)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_snd)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp h1))
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp h1))
  refine ⟨M.comap g, hM.preimage hgc, fun m' hm' => ⟨g m', hm', ?_⟩⟩
  rw [hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivMapsOpenFiniteSubgroupToOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleLinearEquiv_maps_open_finite_subgroup_to_open : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  first | exact @GlobalTheory.WeilAdm.fintrans | exact GlobalTheory.WeilAdm.fintrans | (intros; apply GlobalTheory.WeilAdm.fintrans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVector
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem globalIntegralMatrix_mem_stdThetaLattice (D : D7) (δ : ℂ) {a d : ℕ} (x : Matrix (Fin d) (Fin a) D.host.E)
    (hx : ∀ i j, ∃ b : 𝓞 D.host.E, x i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun v hv i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, x i j * v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := hx i j
      have h1 := (1 : Submodule (𝓞 D.host.E) D.host.E).smul_mem b (hv j trivial)
      rw [hb]
      simpa [Algebra.smul_def] using h1
    exact this

end GlobalTheory.FunObj.StdDatum.LiftCoset

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem unitBlock_mul_int (D : D7) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = 0 + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D 0 a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

end GlobalTheory.FunObj.StdDatum.LiftCoset

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVectorStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_cosetVector_eq_translate_unitVector : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  first | exact @GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq | exact GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq | (intros; apply GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProduct
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.GoodCharProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIrrChar_of_abs {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K] (σ : K →+* ℂ) {χ : G → K}
    (h : IsAbsIrrChar χ) : Formalism.L2.NT.IsIrrChar (fun g => σ (χ g)) := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ∀ x : K, ι (algebraMap K (AlgebraicClosure K) x) = σ x := fun x => ι.commutes x
  have hch : ∀ g, ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := fun g => by
    rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
      LinearMap.toMatrix_eq_toMatrix']
  let ρm : G →* GL (Fin n) (AlgebraicClosure K) :=
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv' : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K)
      ≃ₐ[AlgebraicClosure K] Matrix (Fin n) (Fin n) (AlgebraicClosure K)).toRingEquiv.toMonoidHom.comp ρ)
  let ρc : G →* GL (Fin n) ℂ := (Matrix.GeneralLinearGroup.map (ι : AlgebraicClosure K →+* ℂ)).comp ρm
  have htr : ∀ g, Matrix.trace (ρc g : Matrix (Fin n) (Fin n) ℂ) = σ (χ g) := fun g => by
    rw [← hι, ← hχ g, hch g]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ρc, ρm, Matrix.trace, Matrix.diag, map_sum]
  have hC : ∀ g, star (σ (χ g)) = σ (χ g⁻¹) := fun g => by
    have := PI.SerBridgeGLW.conjugate_character_formula G (PI.SerBridgeGLW.repOfGL ρc) g
    rwa [PI.SerBridgeGLW.repOfGL_character, PI.SerBridgeGLW.repOfGL_character, htr, htr] at this
  refine ⟨⟨n, ρc, fun g => (htr g).symm⟩, ?_⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := AlgebraicClosure K) (ψ := ρ.character) (ψ' := ρ.character)
    ⟨n, ρ, hρ, rfl⟩ ⟨n, ρ, hρ, rfl⟩
  rw [if_pos rfl] at horth
  have hcard : (Nat.card G : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : AlgebraicClosure K) := by
    rw [← mul_one (Nat.card G : AlgebraicClosure K), ← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  unfold Formalism.L2.NT.ipG
  simp only [hC]
  have := congrArg ι hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_natCast, Nat.card_eq_fintype_card] at this
  rw [← this]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hχ, hχ, hι, hι]

theorem isIrrChar_comp {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (e : G' ≃* G) {χ : G → ℂ}
    (h : Formalism.L2.NT.IsIrrChar χ) : Formalism.L2.NT.IsIrrChar fun x => χ (e x) := by
  obtain ⟨⟨n, ρ, hρ⟩, hip⟩ := h
  refine ⟨⟨n, ρ.comp e.toMonoidHom, fun x => hρ _⟩, ?_⟩
  unfold Formalism.L2.NT.ipG at hip ⊢
  rw [Fintype.card_congr e.toEquiv, ← hip]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ => rfl

theorem isProdCuspChar_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hrec hE hX χ hχ
  classical
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hrec
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  have hirr : Formalism.L2.NT.IsIrrChar fun x : G0g D.nd => D.what₂.embLL (χ (eR.symm x)) :=
    isIrrChar_comp eR.symm (isIrrChar_of_abs D.what₂.embLL (hX χ hχ))
  have he0 : ∑ x : G0g D.nd, D.ntypes.e0.coeff x * D.what₂.embLL (χ (eR.symm x)) = D.what₂.embLL (χ (eR.symm 1)) := by
    have h0 := congrArg D.what₂.embLL (GlobalTheory.IdemChar.sum_coeff_idemOf_mul D.what₂.LL G A.X hX χ hχ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    rw [map_one, ← h0]
    symm
    refine Fintype.sum_equiv eR.toEquiv _ _ fun g => ?_
    simp [h1]
  obtain ⟨θ, hθ, hχθ⟩ := GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' D hE _ hirr he0
  have key : ∀ PP : R.Pg, ∃ θ' : GL (Fin D.R.r) (kP PP.1) → ℂ,
      @GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) D.R.r θ' ∧
        ∀ g, θ' (R.eG g PP) = θ (plg.symm PP) (eR g (plg.symm PP)) := by
    intro PP
    obtain ⟨kv, rfl⟩ := plg.surjective PP
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    letI := Ideal.Quotient.field (plg kv).1.asIdeal
    refine ⟨_, GlobalTheory.FinGL.Transport.isCuspProdChar_transport _ _ (iso kv) _ _ (hθ kv), fun g => ?_⟩
    rw [Equiv.symm_apply_apply, h2]
    exact congrArg _ ((GlobalTheory.FinGL.Transport.glEquiv (iso kv) D.R.r).symm_apply_apply _)
  choose θ' hθ' hθ'' using key
  refine ⟨θ', hθ', fun x => ?_⟩
  obtain ⟨g, rfl⟩ := R.eG.surjective x
  simp only [hθ'', MulEquiv.symm_apply_apply]
  have h3 := hχθ (eR g)
  rw [MulEquiv.symm_apply_apply] at h3
  rw [h3]
  exact (Fintype.prod_equiv plg.symm _ _ fun _ => rfl).symm

end GlobalTheory.GoodCharProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProductStatement
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  first | exact @GlobalTheory.GoodCharProd.isProdCuspChar_good | exact GlobalTheory.GoodCharProd.isProdCuspChar_good | (intros; apply GlobalTheory.GoodCharProd.isProdCuspChar_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.RealDirCoord

theorem continuous_ringEquiv_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem eps_smul_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (z : AF F ⊗[F] E) :
    (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)
    simp
  | add a b ha hb => rw [smul_add, ha, hb, map_add (f := _), map_add (f := _)]

theorem eps_smul_eq (D : D7) (z : AE D) :
    (pairA D.host.F 0 1) • z =
      LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (finPart D z) :=
  eps_smul_gen z

theorem eps_mul_snd {F : Type} [Field F] [NumberField F] (x : AF F) :
    (pairA F 0 1 * x).2 = x.2 := one_mul x.2

theorem darboux_real_coords : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  intro D S T κ _ e k L hL hfin

  have hε : ∀ t, (pairA D.host.F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPart D (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]
    rfl
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩

  have he : Continuous e := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
      inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
        map_add' := by
          intro a b
          funext i
          rw [map_add (f := _), LinearEquiv.map_add (e := _), hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (continuous_ringEquiv_mixed D.host.F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

end GlobalTheory.RealDirCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_real_family_archimedean_linear : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  first | exact @GlobalTheory.RealDirCoord.darboux_real_coords | exact GlobalTheory.RealDirCoord.darboux_real_coords | (intros; apply GlobalTheory.RealDirCoord.darboux_real_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsBijectiveOfParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexCoordsPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexCoordsPrincipalLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem iC_principal_injective : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC _hIB t
  have hj : GlobalTheory.QPosCompare.IsForm ((R.toCx3 F).jR t) :=
    GlobalTheory.TwistPlacesObj.isForm_tw _ R.toRealDat.emb0 (GlobalTheory.QPosCompare.isForm_jX hC.base.models t)
  exact GlobalTheory.TwistPlacesObj.lin_injective ((R.toCx3 F).Θ t) hj
    ((A3.A.fam.R t).toF (A3.A.fam.lvl ⊥ 1) ((R.toCx3 F).zs.Z t))
    (BlockDat.toF_injective _ _ _) (fun y => GlobalTheory.TwistPlacesObj.toF_mem _ _ _ y)

end GlobalTheory.PrimIn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexCoordsPrincipalLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_complexCoords_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  first | exact @GlobalTheory.PrimIn.iC_principal_injective | exact GlobalTheory.PrimIn.iC_principal_injective | (intros; apply GlobalTheory.PrimIn.iC_principal_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCoordsPrincipalLevelRangeEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCoordsPrincipalLevelRangeEqTop
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem theta_Z_mem_range_iC {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) (t : A3.fam3.base3.Tup) :
    ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R t).ZHg A3.A.fam.X := hIB.1 t hz
  obtain ⟨x, hx⟩ := GlobalTheory.PrincipalRows.mem_range_toF_full (A3.A.fam.R t) A3.A.fam.X (X.zs.Z t) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ t (X.jR t y)) hx


set_option maxHeartbeats 1000000 in
theorem iC_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC hUp hRT hIB t
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := GlobalTheory.PrincipalRows.theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT t
    (LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t))
    (theta_Z_mem_range_iC A3 (R.toCx3 F) hIB t)
  have hinj : Function.Injective (LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    show Function.Injective (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)))
    rw [Tw.adjoint_map]
    intro x y hxy
    exact hUp t hxy
  have hinj2 : Function.Injective ((R.toCx3 F).Θ t ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have h0 : LinearMap.adjoint ((R.toCx3 F).Θ t) e = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_left]
      have : (R.toCx3 F).Θ t (LinearMap.adjoint ((R.toCx3 F).Θ t) e) = 0 := he
      rw [this, inner_zero_right]
    exact hinj (h0.trans (map_zero _).symm)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj2
  rw [eq_top_iff]
  intro e _
  obtain ⟨e', rfl⟩ := hsurj e
  exact hmem e'

end GlobalTheory.PrimIn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCoordsPrincipalLevelRangeEqTopStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoords_principalLevel_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  first | exact @GlobalTheory.PrimIn.iC_range_eq_top | exact GlobalTheory.PrimIn.iC_range_eq_top | (intros; apply GlobalTheory.PrimIn.iC_range_eq_top <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimIn

theorem principalLevel_rows_bijective_of_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → R.PrincipalLevelBijective F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hOk hW hUp hRow hIn
  have hinj := GlobalTheory.T.injective_complexCoords_principalLevel R F hOk hW hIn
  have htop := GlobalTheory.T.complexCoords_principalLevel_range_eq_top R F hOk hW hUp hRow hIn
  refine ⟨hinj _, fun t => ⟨hinj t, ?_⟩⟩
  rw [htop t, htop _]

end GlobalTheory.PrimIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLaurentCoeffSubConst
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]


end Abstract

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

end Unitary



end GlobalTheory.LaurentAut
end
end
