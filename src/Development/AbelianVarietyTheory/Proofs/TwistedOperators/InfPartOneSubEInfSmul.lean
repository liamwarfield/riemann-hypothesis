module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaClosed

open GlobalTheory.FinTranslate

variable {D : D7}

theorem finPart_eInf_smul (a : Formalism.L2.Theta.AE D) : finPart D (eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h0 : sndA D.host.F (eInf D) = 0 := rfl
    rw [smul_eq_mul, map_mul, h0, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem infPart_one_sub_eInf_smul (a : Formalism.L2.Theta.AE D) : infPart D ((1 - eInf D) • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h1 : fstA D.host.F (eInf D) = 1 := rfl
    rw [smul_eq_mul, map_mul, map_sub, map_one, h1, sub_self, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem isThetaFunO_heisO_all {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by

  have hre : (eInf D • u).map (finPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, finPart_eInf_smul]
  have hfin : ((1 - eInf D) • u).map (infPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, infPart_one_sub_eInf_smul]
  have hsplit : (1 - eInf D) • u + eInf D • u = u := by
    rw [sub_smul, one_smul, sub_add_cancel]

  have hcomp : heisO ψ S T ((1 - eInf D) • u) (heisO ψ S T (eInf D • u) f) = heisO ψ S T u f := by
    rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_fin_real hfin hre, AddChar.map_zero_eq_one, one_smul,
      hsplit]
  rw [← hcomp]
  exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hre hf) hfin

theorem thetaClosed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ u, IsThetaFunO ψ S T (heisO ψ S T u f)) ∧ ∀ τ z, IsThetaFunO ψ S T (Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ hψ hθ S T f hf
  exact ⟨fun u => isThetaFunO_heisO_all hψ hf u, fun τ z => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf⟩

end GlobalTheory.ThetaClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistAdelicTop

theorem locallyCompact_secondCountable_borel_countable :
    ∀ {D : D7} (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧
      BorelSpace (GA D V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  exact ⟨hlc, hsc, ⟨rfl⟩, (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2⟩

end GlobalTheory.TwistAdelicTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcreteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_unitaryGroup_concrete : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple := by
  first | exact @GlobalTheory.RegSSObj.regularSemisimple | exact GlobalTheory.RegSSObj.regularSemisimple | (intros; apply GlobalTheory.RegSSObj.regularSemisimple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubquot

theorem exists_covBy_submodule {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    ∃ S T : Submodule R M, T ⋖ S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI := CompleteLattice.Iic_coatomic_of_compact_element (Submodule.singleton_span_isCompactElement (R := R) m)
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Set.Iic (Submodule.span R {m})) with h0 | ⟨c, hc, -⟩
  · have h1 : (⊥ : Submodule R M) = Submodule.span R {m} := congrArg Subtype.val h0
    exact absurd (Submodule.mem_span_singleton_self m) (by rw [← h1]; simpa using hm)
  · refine ⟨Submodule.span R {m}, c.1, lt_of_le_of_ne c.2 fun h => hc.1 (Subtype.ext h), ?_⟩
    intro x h1 h2
    have := congrArg Subtype.val (hc.2 ⟨x, h2.le⟩ h1)
    exact h2.ne this

theorem exists_irreducible_subquotient : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Nontrivial V → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ G Y), σ.IsIrreducible ∧ IsSubquotient σ ρ := by
  intro G _ V _ _ ρ hV
  haveI : Nontrivial ρ.asModule := hV
  obtain ⟨S, T, h⟩ := exists_covBy_submodule (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e.symm T ⋖ e.symm S :=
    ⟨e.symm.lt_iff_lt.2 h.1, fun c h1 h2 => h.2 (c := e c) (by simpa using e.lt_iff_lt.2 h1)
      (by simpa using e.lt_iff_lt.2 h2)⟩
  refine ⟨_, _, _, subQuot (e.symm S) (e.symm T), isIrreducible_subQuot h', e.symm S,
    ⟨Submodule.mkQ _, fun g => ?_⟩, Submodule.mkQ_surjective _⟩
  ext x
  rfl

end GlobalTheory.IrrSubquot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvIdempotentAct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

theorem act_sum_smul {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g : Formalism.L2.DIV.G0 L.Pg L.r) {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → GA D V → ℂ) :
    actG0 V β L g (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • actG0 V β L g (F i) := by
  unfold actG0
  split_ifs with hk
  · funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · simp

theorem convIdempotent_act : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) [Fintype (Formalism.L2.DIV.G0 L.Pg L.r)], LiftsExist V β L → ∀ c : Formalism.L2.DIV.G0 L.Pg L.r → ℂ, (∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F)) = ∑ g, c g • actG0 V β L g F := by
  intro D V β L _ hL c hc F hF
  have hA := levelGroupAction_isAction V β L hL F hF
  calc (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F))
      = ∑ g, ∑ g', (c g * c g') • actG0 V β L (g * g') F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [act_sum_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun g' _ => ?_
        rw [hA.2 g g', smul_smul]
    _ = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by
          simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_smul.symm
    _ = ∑ g, c g • actG0 V β L g F := by
        simp only [hc]

end GlobalTheory.FlagAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private lemma atTau_mem_GinfC_twisted_operators {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem isMultMap_rightTranslate_finite : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  intro D V S θ M J χ κ hκ hJ T hT
  refine ⟨(LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)).compMultilinearMap T,
    ⟨fun v => ?_, fun v => ?_, fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v => rfl⟩
  ·
    exact GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite θ V κ hκ (T v) (hT.aut v)
  ·
    intro r C hC μ 𝓕 hμ h𝓕 g
    have h := hT.cusp v r C hC μ 𝓕 hμ h𝓕 (g * κ)
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, Function.comp, mul_assoc] using h
  ·
    obtain ⟨hk1, hk2⟩ := hJ k hk
    show T v (g * k * κ) = χ k * T v (g * κ)
    have h := hT.lev v _ hk1 (g * κ)
    rw [hk2] at h
    rw [← h]
    congr 1
    group
  ·
    rw [LinearMap.compMultilinearMap_apply, hT.equiv τ g hg v w hw]
    funext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.funLeft_apply, rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.T.mul_comm_of_mem_GfC_of_mem_GinfC V κ _ hκ (atTau_mem_GinfC_twisted_operators θ V τ g)]
  ·
    obtain ⟨ℓ, hℓ, hℓw⟩ := hT.cont τ v (x * κ)
    exact ⟨ℓ, hℓ, fun w => hℓw w⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMultMap_rightTranslate_finiteAdelic_normalizer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  exact @GlobalTheory.isMultMap_rightTranslate_finite
end
end
