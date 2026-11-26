module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

def IsCurve (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] : Prop :=
  SmoothOfRelativeDimension 1 (strHom k (X := C)) ∧ IsProjOver (strHom k (X := C)) ∧ GeometricallyConnected (strHom k (X := C))

def SemiNeg (k : Type) [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (F : C.Modules) : Prop :=
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ i : W ⟶ F, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

def IsGen {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) : Prop := IsDominant x ∧ IsPreimmersion x

theorem isGen_fromSpecStalk (C : Scheme.{0}) [IsIntegral C] :
    IsGen (K := C.functionField) (C.fromSpecStalk (genericPoint C)) :=
  ⟨show IsDominant (C.fromSpecStalk (genericPoint C)) from ⟨by
      refine Dense.mono (s₁ := {genericPoint C}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec C).def)
      rintro _ rfl
      exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩,
    inferInstanceAs (IsPreimmersion (C.fromSpecStalk (genericPoint C)))⟩

end GlobalTheory.NeronCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

def SerClause (D : D7) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C),
      ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f

structure TiesA {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  w1 : ∀ w, (R.toCx3 F).W1 F.cr (R.num F 0 0) w → w ∈ R.twPl
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

structure TiesG (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) : Prop where
  fw : ∃ fw : FWTie T R.toRealDat κ v₀, BarTie fw
  pins : ∀ i, OMPins T R.toRealDat κ v₀ O i
  phase : ∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i
  unif : R.toRealDat.LUnif
  ioExt : IoExt R.toRealDat
  oneMap : ∀ i, OneMapRowR T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i
  cover : GlobalTheory.TwistField.CoverField T R.toRealDat

section Real

open Formalism.L2 Formalism.L2.Rows

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

end Real

section Api

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

end Api

end GlobalTheory.PrimIn

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.Model

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem ιMulti_comb {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) K) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = c.det • exteriorPower.ιMulti K m b := by
  have h : (exteriorPower.ιMulti K m).compLinearMap (Fintype.linearCombination K b) =
      (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).smulRight (exteriorPower.ιMulti K m b) := by
    refine (Pi.basisFun K (Fin m)).ext_alternating fun v hv => ?_
    let s : Equiv.Perm (Fin m) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have e : (fun i => Pi.basisFun K (Fin m) (v i)) = (fun i => Pi.basisFun K (Fin m) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K) (fun i => Pi.basisFun K (Fin m) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]
  exact AlternatingMap.congr_fun h c


omit [NumberField K] in
theorem ιMulti_comb_int {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) (𝓞 K)) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b := by
  have := ιMulti_comb b (c.map (algebraMap (𝓞 K) K))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  rw [← this]
  congr 1
  funext i
  exact Finset.sum_congr rfl fun j _ => (algebraMap_smul K _ _).symm


omit [NumberField K] in
theorem detSpan_span {m : ℕ} (b : Fin m → V) :
    detSpan K m (Submodule.span (𝓞 K) (Set.range b)) = Submodule.span (𝓞 K) {exteriorPower.ιMulti K m b} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨y, hy, rfl⟩
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hy i)
    rw [show y = fun i => ∑ j, (Matrix.of c) i j • b j from funext fun i => (hc i).symm, ιMulti_comb_int]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rintro _ rfl
    exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩



end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ}

end GlobalTheory.FlatCM.Model

end
end
