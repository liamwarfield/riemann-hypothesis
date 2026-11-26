module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem countable_numberField : Countable F := by
  exact Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective

theorem separableSpace_Fv : TopologicalSpace.SeparableSpace (Fv F v) := by
  haveI := countable_numberField F
  exact ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
    HeightOneSpectrum.denseRange_algebraMap F v⟩⟩

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  haveI := separableSpace_Fv F v
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) := by
  have hK := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers (F := F) (v := v)
  have hN : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈ 𝓝 (0 : v.adicCompletion F) := by
    exact (Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem
  exact hK.locallyCompactSpace_of_mem_nhds_of_addGroup hN

theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  have h : {r : Fv F v | IsUnit r} = {0}ᶜ := by
    ext r
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton

end Local

theorem densFibV_holds : DensFibV := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv
    hSB hdens
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  exact DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1)
    (fun X => rfl) Subtype.val_injective
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX)
    hSB.1.continuous hSB.2 hdens Filter.univ_mem
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
noncomputable section

namespace PI.VolStabS.TopoAF

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology TopologicalSpace Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F]

instance countable_field : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)

instance countable_ringOfIntegers : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ)

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hs.countable

instance countable_spectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have := countable_ideal F
  have hi : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  exact hi.countable

variable {F} in
instance separable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SeparableSpace (v.adicCompletion F) := by
  let h := (HeightOneSpectrum.adicCompletion.equivCompletion F v).toHomeomorphOfIsInducing
    (HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion F v).isInducing
  have : Countable (WithVal (v.valuation F)) := (WithVal.equiv (v.valuation F)).injective.countable
  exact h.symm.surjective.denseRange.separableSpace h.symm.continuous

variable {F} in
instance secondCountable_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable _

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

instance secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := fun S => by
    rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Πʳ v, [R v, A v]) := fun S =>
    Set.range (RestrictedProduct.inclusion R A (hS S))
  have hemb : ∀ S, IsOpenEmbedding (RestrictedProduct.inclusion R A (hS S)) := fun S =>
    RestrictedProduct.isOpenEmbedding_inclusion_principal (isOpen_integers F) (hS S)
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 : SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (hemb S).toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : {v | x v ∉ A v}.Finite := x.eventually
    refine Set.mem_iUnion.2 ⟨hx.toFinset, ?_⟩
    show x ∈ Set.range (RestrictedProduct.inclusion R A (hS hx.toFinset))
    rw [RestrictedProduct.range_inclusion]
    simp only [Set.mem_ofPred_eq, eventually_principal, Set.mem_compl_iff, Finset.mem_coe,
      Set.Finite.mem_toFinset, not_not]
    exact fun v hv => hv
  exact @secondCountableTopology_of_countable_cover _ _ _ _ U hsc (fun S => (hemb S).isOpen_range) hcov

instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

section HA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F} {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

instance secondCountable_tensAF : SecondCountableTopology (AF F ⊗[F] E) := inferInstance

theorem secondCountable_HA_of (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : SecondCountableTopology (HA R σ J) := by
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have h1 : SecondCountableTopology (HR R σ J) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (HR R σ J))

instance secondCountable_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    SecondCountableTopology (HA (AF F) σ J) :=
  secondCountable_HA_of (AF F) σ J

end HA

end PI.VolStabS.TopoAF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasOrbSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MeasOrb : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ, IsAdm F E Φ →
    Measurable fun g : HA (AF F) σ J => Φ (g • ratTup (AF F) X0)

def MeasGrp : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  MeasurableMul (HA (AF F) σ J) ∧ MeasurableInv (HA (AF F) σ J)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem orb_mk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

theorem orb_smul (x0 : X) (g : G) (q : G ⧸ MulAction.stabilizer G x0) :
    (g • q).out • x0 = g • (q.out • x0) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  have : g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) =
      ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0) := rfl
  rw [this, orb_mk, mul_smul]

end Abstract

def SecCtblG : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def OrbTup : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ y : Fin a → Fin M → AF F ⊗[F] E, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) →
    ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y

def StabClosed : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))

def NuInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ (g : HA (AF F) σ J) (s : Set (Fin a → Fin M → AF F ⊗[F] E)), MeasurableSet s →
      νX ((fun y => g • y) ⁻¹' s) = νX s

def NuFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → νX K < ⊤

def NuNeZero : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX → νX ≠ 0

def OrbEmb : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  MeasurableEmbedding (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ∧
    Continuous (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def LocEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    ∃ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E))
      (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf ∧ SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf ∧
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) ∧
      (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) ∧
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf ∧
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)

def SdUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ1 μ2, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ1 → SdW F E σ M J (Ainf F) (psiInf F ψ) a μ2 →
      μ1 = μ2) ∧
    (∀ ν1 ν2, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν1 → SdHerm F E σ (Ainf F) (psiInf F ψ) a ν2 →
      ν1 = ν2) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ μ1 μ2, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ1 → SdW F E σ M J (Fv F v) (psiV F ψ v) a μ2 →
        μ1 = μ2) ∧
      (∀ ν1 ν2, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν1 →
        SdHerm F E σ (Fv F v) (psiV F ψ v) a ν2 → ν1 = ν2)

def FibPin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
      ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      ∀ fib1 fib2 : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib1 →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib2 →
      ∀ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf → HasCompactSupport Φinf →
        ∫ X, Φinf X ∂(fib1 (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fib2 (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
      ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      ∀ fib1 fib2 : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib1 →
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib2 →
      ∀ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv →
        ∫ X, Φv X ∂(fib1 (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv X ∂(fib2 (hermOf (Fv F v) σ (gramE σ J X0) hT))

def MultFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))

def RestrProd : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    ∃ νX : Measure (Fin a → Fin M → AF F ⊗[F] E),
      νX {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = 0 ∧
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ νX ∧
        ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))

theorem exOmT_of (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c1 := h1 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c2 := h2 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c3 := h3 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c4 := h4 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c5 := h5 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μinf, νinf, μv, νv, fibInf, fibV, hμi, hνi, hμv, hνv, hfi, hfv⟩ := c1
  obtain ⟨νX, hsupp, hform⟩ :=
    c5 μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv (c4 μv hμv νv hνv fibV hfv)
  refine ⟨νX, hsupp, ⟨μinf, hμi⟩, fun μinf' hμi' => ?_⟩
  obtain rfl := c2.1 _ _ hμi hμi'
  refine ⟨⟨νinf, hνi⟩, fun νinf' hνi' => ?_⟩
  obtain rfl := c2.2.1 _ _ hνi hνi'
  refine ⟨⟨μv, hμv⟩, fun μv' hμv' => ?_⟩
  obtain rfl : μv = μv' := funext fun v => (c2.2.2 v).1 _ _ (hμv v) (hμv' v)
  refine ⟨⟨νv, hνv⟩, fun νv' hνv' => ?_⟩
  obtain rfl : νv = νv' := funext fun v => (c2.2.2 v).2 _ _ (hνv v) (hνv' v)
  refine ⟨⟨fibInf, hfi⟩, fun fibInf' hfi' => ⟨⟨fibV, hfv⟩, fun fibV' hfv' => ?_⟩⟩
  intro d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  obtain ⟨hI, hF⟩ := hform d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  refine ⟨hI, c4 μv hμv νv hνv fibV' hfv' d b Φf Φv hp, ?_⟩
  rw [hF, c3.1 μinf hμi νinf hνi fibInf fibInf' hfi hfi' Φinf hc1 hc2]
  congr 1
  exact tprod_congr fun v => c3.2 v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (fibV' v) (hfv v)
    (hfv' v) (Φv v) (hp.1 v)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InvInvSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def InvInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant) ∧
    ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
      ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
        μ'.IsInvInvariant

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation

theorem densFibInf_holds : DensFibInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ μinf hμ νinf hν fibInf hfib Φ g
    hΦc hΦs hg
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have hD : {S : HermR (Ainf F) σ a | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} ∈
      𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT) :=
    (isOpen_unitHerm (Ainf F) (isOpen_units_Ainf F) σ a).mem_nhds
      (isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  exact DensGen.densGen (f' := gramH (Ainf F) σ hσ J hJ.1) hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) Subtype.val_injective
    (fun v hv => linIndep_of_isUnit_det (Ainf F) σ J v hv) hΦc hΦs hg Filter.univ_mem hD hD

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibOfTens
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib

def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}

def TensAll : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  TensFacts F E σ M J a (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), TensFacts F E σ M J a (Fv F v)

def DensInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      DensAll μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {X | LinearIndependent (Ainf F ⊗[F] E) X}

def DensV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensAll μv (gramR (Fv F v) σ J) Subtype.val νv {X | LinearIndependent (Fv F v ⊗[F] E) X}

theorem fib_of_tens {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {a : ℕ} {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hG : FibOfDens) (hT : TensFacts F E σ M J a R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hD : DensAll μ (gramR R σ J) Subtype.val ν {X | LinearIndependent (R ⊗[F] E) X}) :
    ∃ fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E),
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
        Set.univ fib := by
  obtain ⟨hLC, hT2, hSC, hCl, hCont, hMem, hOpen⟩ := hT
  haveI := hLC
  haveI := hT2
  haveI := hSC
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (HermR R σ a) := by
    first
      | infer_instance
      | exact hCl.isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.toIsEmbedding.toIsInducing.secondCountableTopology
  haveI : BorelSpace (HermR R σ a) := by
    first
      | infer_instance
      | exact ⟨rfl⟩
  haveI : LocallyCompactSpace (HermR R σ a) := hCl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact hG _ _ _ μ ν inferInstance inferInstance inferInstance (gramR R σ J) Subtype.val _ hCont
    hCl.isClosedEmbedding_subtypeVal (fun v => ⟨⟨_, hMem v⟩, rfl⟩) hOpen hD

theorem fibInfEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensInf) : FibInfEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν
  exact fib_of_tens hG (hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).1 μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν)

theorem fibVEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensV) : FibVEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν
  exact fib_of_tens hG ((hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).2 v) μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HformSmulRight
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

@[reducible] def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by
    show σ (x * y) = σ y * σ x
    rw [map_mul, mul_comm]
  star_add x y := map_add σ x y

section General

variable {E : Type} [Field E] {M : ℕ}

theorem hform_add_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J (c • x) y = σ c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J x (c • y) = RingHom.id E c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [StarRing E]

def hSes (J : Matrix (Fin M) (Fin M) E) : (Fin M → E) →ₗ⋆[E] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (hform_add_left' _ J) (hform_smul_left' _ J) (hform_add_right' _ J) (hform_smul_right' _ J)

theorem hSes_apply (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hSes J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hSes_herm (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (x y : Fin M → E) : star (hSes J x y) = hSes J y x := by
  rw [hSes_apply, hSes_apply]
  show starRingEnd E _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hSes_nondeg (J : Matrix (Fin M) (Fin M) E) (hdet : J.det ≠ 0) (x : Fin M → E)
    (hx : ∀ y, hSes J x y = 0) : x = 0 := by
  have h1 : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have := hx (Pi.single j 1)
    rw [hSes_apply] at this
    simpa [Formalism.UG.hform, Pi.single_apply, vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have := congrFun h2 i
  simpa using this

theorem linInd_of_gram (J : Matrix (Fin M) (Fin M) E) {a : ℕ} (X : Fin a → Fin M → E)
    (G : Matrix (Fin a) (Fin a) E) (hG : ∀ i j, G i j = Formalism.UG.hform (starRingEnd E) J (X i) (X j))
    (hdet : G.det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : G *ᵥ c = 0 := by
    funext j
    have := congrArg (hSes J (X j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [mulVec, dotProduct, Pi.zero_apply, hG]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSes_apply]
    ring
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h1) i

variable [CharZero E]

theorem witt_tuple (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (hdet : J.det ≠ 0) {a : ℕ} (X0 X : Fin a → Fin M → E) (h0 : LinearIndependent E X0)
    (h1 : LinearIndependent E X)
    (hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j)) :
    ∃ g ∈ Formalism.UG.UJ (starRingEnd E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E) *ᵥ X0 i = X i := by
  let U := Submodule.span E (Set.range X0)
  let bU : Module.Basis (Fin a) E U := Module.Basis.span h0
  have hb : ∀ i, ((bU i : U) : Fin M → E) = X0 i := fun i => by
    show ((Module.Basis.span h0 i : U) : Fin M → E) = X0 i
    rw [Module.Basis.span_apply]
  let f : U →ₗ[E] (Fin M → E) := bU.constr E X
  have hf : ∀ i, f (bU i) = X i := fun i => bU.constr_basis E X i
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hs := bU.sum_repr u
    rw [← hs] at hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hf] at hu
    have hc := (Fintype.linearIndependent_iff.mp h1) _ hu
    rw [← hs]
    simp [hc]
  have key : ((hSes J).comp f).compl₂ f = ((hSes J).comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis bU bU fun i j => ?_
    show hSes J (f (bU i)) (f (bU j)) = hSes J ((bU i : U) : Fin M → E) ((bU j : U) : Fin M → E)
    rw [hf, hf, hb, hb]
    exact hG i j
  have hiso : ∀ x y : U, hSes J (f x) (f y) = hSes J x y := fun x y =>
    DFunLike.congr_fun (DFunLike.congr_fun key x) y
  obtain ⟨g, hgiso, hgf⟩ :=
    witt_extension_theorem E (Fin M → E) (hSes J) (hSes_herm J hJ) (hSes_nondeg J hdet) U f hinj hiso
  let m : Matrix (Fin M) (Fin M) E := LinearMap.toMatrix' (g : (Fin M → E) →ₗ[E] (Fin M → E))
  let mi : Matrix (Fin M) (Fin M) E :=
    LinearMap.toMatrix' (g.symm : (Fin M → E) →ₗ[E] (Fin M → E))
  have hc1 : (g : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hc2 : (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hm1 : m * mi = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
  have hm2 : mi * m = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id]
  have hmv : ∀ v, m *ᵥ v = g v := fun v => by
    simp only [m]
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  refine ⟨⟨m, mi, hm1, hm2⟩, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd E) m * J * m = J
    ext i j
    have h := hgiso (Pi.single i 1) (Pi.single j 1)
    rw [hSes_apply, hSes_apply, ← hmv, ← hmv, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single,
      Formalism.UG.P.hform_single] at h
    exact h
  · intro i
    show m *ᵥ X0 i = X i
    rw [hmv, ← hb i]
    exact (hgf (bU i)).trans (hf i)

end General

theorem sigma_invol_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem witt_holds : Witt := by
  unfold Witt InCtx
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ hdet X hX
  letI : StarRing E := starOfInv (σ : E →+* E) (sigma_invol_cm σ hCM)
  have hs : starRingEnd E = (σ : E →+* E) := RingHom.ext fun _ => rfl
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := by
    rw [hs]; exact hJ.1
  have hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j) := by
    rw [hs]; exact fun i j => congrFun (congrFun hX i) j
  have hl0 : LinearIndependent E X0 :=
    linInd_of_gram J X0 (gramE σ J X0) (by rw [hs]; intro i j; rfl) hdet
  have hl1 : LinearIndependent E X :=
    linInd_of_gram J X (gramE σ J X) (by rw [hs]; intro i j; rfl) (hX ▸ hdet)
  obtain ⟨g, hg, hgX⟩ := witt_tuple J hJ' hJ.2 X0 X hl0 hl1 hG
  rw [hs] at hg
  exact ⟨g, hg, hgX⟩

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStab
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)

theorem exFDStab_of (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩

theorem discHF_of_discHA (h : PI.VolSemiDirect.W.DiscHA) : DiscHF := by
  intro F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _
  exact (h F E σ hE M J hJ).2

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SWeqOm
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Decay

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem continuous_sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))

theorem rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩

end Decay

theorem sWeqOm_of (h1 : DensFibInf) (h2 : DensFibV) : SWeqOm := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr, hsm⟩ := hΦ
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hsm hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  have hmean' : meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) =
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) *
        ∏' v, gv v (hermOf (Fv F v) σ (gramE σ J X0) hT) := hmean
  rw [hmean', hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)

end PI.VolStabS
end
end
