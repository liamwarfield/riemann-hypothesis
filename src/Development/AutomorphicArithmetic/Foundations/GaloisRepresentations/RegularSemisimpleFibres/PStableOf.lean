module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem splitStrong_holds : UpperTheory.ConvolutionTheory.T.SplitStrong :=
  UpperTheory.ConvolutionTheory.T.splitStrong
    (UpperTheory.ConvolutionTheory.T.descStep (UpperTheory.ConvolutionTheory.T.coreDesc UpperTheory.ConvolutionTheory.ci (UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit))
      (UpperTheory.ConvolutionTheory.T.liftAll (UpperTheory.ConvolutionTheory.T.liftStep (UpperTheory.ConvolutionTheory.T.coreLift UpperTheory.ConvolutionTheory.ci
        (UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit)))))

theorem UpperTheory.Gal.InertialTypesAlt.stableOf :
    StableOf := by
  intro K M _ _ _ _ _ _ _ _ hp n hn π P hW
  have hc := (UpperTheory.ConvolutionTheory.Sph.weakStable K M hp n hn π P hW).1
  refine ⟨hc, ?_⟩
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  exact splitStrong_holds K M σ hσ hp n hn π P hc hW
