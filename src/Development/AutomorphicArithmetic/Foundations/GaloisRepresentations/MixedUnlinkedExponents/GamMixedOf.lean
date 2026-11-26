module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BijectiveOfSplit
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharLiftStep

open Matrix

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem cycAt_or_split [IsGalois K M] (hp : (Module.finrank K M).Prime) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal] :
    GlobalTheory.FunExt.CycAt v u ∨ (u.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ u.asIdeal.inertiaDeg (𝓞 K) = 1) := by
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  rw [IsGalois.card_aut_eq_finrank, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal u.asIdeal Gal(M/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal u.asIdeal Gal(M/K)] at h2
  have hp' := hp
  rw [← h2] at hp'
  rcases Nat.prime_mul_iff.1 hp' with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr (mul_eq_one.1 h)
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    have hu : u.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.asIdeal) (p := v.asIdeal)).symm
    refine ⟨inferInstance, hp, hu, fun u' hu' => ?_⟩
    have : u'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu']; rfl⟩
    have m1 : u.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u.isPrime, inferInstance⟩
    have m2 : u'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u'.isPrime, inferInstance⟩
    rw [ha, Set.mem_singleton_iff] at m1 m2
    exact HeightOneSpectrum.ext (m2.trans m1.symm)

section Split

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
theorem bijective_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Function.Bijective (GroundTheory.Global.adicCompletionMap v u) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  haveI : Module.Free (v.adicCompletion K) (u.adicCompletion M) := Module.Free.of_divisionRing _ _
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  refine ⟨(GroundTheory.Global.adicCompletionMap v u).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion K) (u.adicCompletion M)) :=
    (Subalgebra.bot_eq_top_of_finrank_eq_one h1) ▸ Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
  exact ⟨x, hx⟩

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
theorem normU_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Continuous (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm ∧
      ∀ y : (u.adicCompletion M)ˣ, ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm y := by
  set i := RingEquiv.ofBijective _ (bijective_of_split v u he hf)
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  haveI : Module.Free (v.adicCompletion K) (u.adicCompletion M) := Module.Free.of_divisionRing _ _
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K M v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  have key : ∀ y : u.adicCompletion M, Algebra.norm (v.adicCompletion K) y = i.symm y := by
    intro y
    conv_lhs => rw [← i.apply_symm_apply y]
    show Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (u.adicCompletion M) (i.symm y)) = _
    rw [Algebra.norm_algebraMap, h1, pow_one]
  refine ⟨?_, fun y => key y⟩
  have e : (i.symm : u.adicCompletion M → v.adicCompletion K) = fun y => Algebra.norm (v.adicCompletion K) y :=
    funext fun y => (key y).symm
  rw [e]
  exact hc

end Split

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (h : ∀ y : k'ˣ, χ' y = χ (Units.map (i.symm : k' →* k) y)) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar χ' hχ' := by
  refine congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ?_)
  obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) χ hχ)
  refine ⟨Representation.Equiv.mk φ.toLinearEquiv fun g => ?_⟩
  have H := φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)
  refine LinearMap.ext fun x => ?_
  have Hx := LinearMap.congr_fun H x
  simp only [LinearMap.coe_comp, Function.comp_apply] at Hx ⊢
  change φ.toLinearEquiv _ = _
  refine Hx.trans ?_
  erw [Function.comp_apply, LinearMap.comp_apply, SmGL.twist_apply, SmGL.twist_apply]
  have e1 : ∀ g' : GL (Fin 1) k', (detChar (Fin 1) χ') g' =
      (detChar (Fin 1) χ) (GeneralLinearGroup.map i.symm.toRingHom g') := fun g' => by
    rw [detChar_apply, detChar_apply, Matrix.GeneralLinearGroup.map_det]; exact h _
  erw [e1 g]
  rfl

end Char

end GlobalTheory.CharLiftStep

end
end

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def NmEq : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v),
    nm w = GlobalTheory.BCChar.normU v w.1

def ChsTr : Prop :=
  ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi' : Continuous i.symm)
    (s : Multiset (IrrGL (k := k))),
    chs (s.map (GlobalTheory.SuppIne.trGL i hi')) = (chs s).map fun ξ => ξ.comp (Units.map (i.symm : k' →* k))

def SplitSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), (¬ ∀ u : PlacesOver L v, u = w) →
      ∃ (i : v.adicCompletion K ≃+* w.1.adicCompletion L) (hi' : Continuous i.symm), Continuous i ∧
        (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
        nm w = Units.map (i.symm : w.1.adicCompletion L →* v.adicCompletion K) ∧
        ∀ s s', SuppAt π v s → SuppAt P w.1 s' → s' = s.map (GlobalTheory.SuppIne.trGL i hi')

def RkSupp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (π : CuspSub K 1) (ψ : HChar K), CG.mk π = CG.ofChar ψ →
    ∀ v s, SuppAt π v s → chs s = {ψ.loc v}

def RkLift : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] [Algebra K L]
    (ψ : HChar K) (ψ' : HChar L), WeakBC (CG.ofChar ψ).HasSat (CG.ofChar ψ').HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v), ψ'.loc w.1 = (ψ.loc v).comp (nm w)

def UpThru : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v)
    (s : Multiset (IrrGL (k := v.adicCompletion K))), (up w s).filter (Thru w) = up w s

def SplitSuppOf : Prop := NmEq → SuppFacts → UpperTheory.ConvolutionTheory.Sph.WeakStable → UpperTheory.ConvolutionTheory.T.SplitStrong → SplitSupp
def RkLiftOf : Prop := NormLoc → RkLift
def UpThruOf : Prop := ChsFacts → UpThru

theorem gamMixed_of (h1 : GamOne) (h2 : SplitSupp) (h3 : ChsTr) (h4 : RkSupp) (h5 : RkLift) (h6 : UpThru) : GamMixed := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v w s s' hs hs'
  by_cases hw : ∀ u : PlacesOver L v, u = w
  · rcases hn.eq_or_lt with rfl | h
    · have e : CG.mk π = CG.ofChar _ := (CG.ofChar_toChar _).symm
      have e' : CG.mk P = CG.ofChar _ := (CG.ofChar_toChar _).symm
      have hW' := hW
      rw [e, e'] at hW'
      have : chs s' = up w s := by
        rw [up, h4 K π _ e v s hs, h4 L P _ e' w.1 s' hs', h5 K L _ _ hW' v w, Multiset.map_singleton]
      rw [this, h6]
    · exact h1 K L hp n h π P hW v w hw s s' hs hs'
  · obtain ⟨i, hi', -, -, hN, H⟩ := h2 K L hp n hn π P hW v w hw
    have : chs s' = up w s := by rw [H s s' hs hs', h3, up, hN]
    rw [this, h6]

end UpperTheory.Gal.GamX
