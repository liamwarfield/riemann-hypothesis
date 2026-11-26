module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.CharPolSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
namespace Amb
variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)
end Amb
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def PurityAtPoints (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
    _root_.UpperTheory.GalN.V.PureW ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
def AutmAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Irr (mapRep 𝔞.toK r) →
    _root_.UpperTheory.V.Aut.IsAut4Alt ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
namespace Tower
variable {D : Raw Ω c} (T : Tower D)
structure IsSeedAlt (ι : PadicAlgCl l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop where
  irr : Irr (P.r.comp T.G'.subtype)
  aut : ∃ (h : Fin 4 → ℤ) (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ),
    (∀ i : Fin 3, ∃ n : ℤ, 2 ≤ n ∧ h i.castSucc = h i.succ + 2 * n) ∧ T.Wts h P ∧ Continuous κ ∧ 0 < k ∧ Even (a + h 0) ∧
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) ∧
    _root_.UpperTheory.V.Z.Win.Birth.CuspidalRankFourRegularAlgebraicTotallyComplex π ∧ Af.AttC ι (Af.tw (P.r.comp (resLe T.F_le)).toHomUnits κ) π
structure SeedPairAlt (ι : PadicAlgCl l ≃+* ℂ) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O) : Prop where
  pair : (T.fr ∅).IsPair (inc h) Q
  cont : Q.Cont (maximalIdeal c₁.O)
  res : (T.fr ∅).Res ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O))
  seed : T.IsSeedAlt ι (Q.map (algebraMap c₁.O (PadicAlgCl l)))
structure PotentialModularityTower (ι : PadicAlgCl l ≃+* ℂ) {c' : Coef l} {h : c.O ≤ c'.O} (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) : Prop where
  fin : ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
    Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1}
  p1 : ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
    (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
    (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
    Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
    X.LocZero J (y : X.A →+* PowerSeries k)
  seed : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
    X.LocZero J (y : X.A →+* PadicAlgCl l)
  pur : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → _root_.UpperTheory.GalN.V.PureW ι r
  aut : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
      Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r
end Tower
def SeedIIAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    Ctx2 D → T.Ok → T.Two → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ,
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
def PMExAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    T.Fit → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ, ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∀ X : Space (T.fr ∅) (inc h), ∃ J, T.PotentialModularityTower ι X J
def ProModAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  ∃ (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V)
    (r₁ : G ℚ Ω →* M4 𝔞.V), T.Fit ∧ T.Deep ∧ T.PotentialModularityTower ι X J ∧ y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧
    (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧ (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧
    IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK r₁) ∧ (∀ g, IsGSp (𝔞.a c (D.th g)) (r₁ g)) ∧
    r₁.comp (resQ T.F) = (X.P.map y).r ∧
    ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s))
end UpperTheory.V.Ws
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuWrap
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Gu
theorem spehOf_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : GlobalTheory.BcSpeh.BcSpeh :=
  _root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge H.litN.aut.bc H.litN.loc.bern)
theorem galUnitaryT_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → GalUnitaryT := fun H => _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
theorem endShape'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → IsSSRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → LocGlobT ι ρ w τ) → ∃ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, G E Ω →* GL (Fin (d i)) (Qbar l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i ∧ Continuous (ρ' i)) ∧ (∀ g, (UpperTheory.V.W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (UpperTheory.V.W.mat (UpperTheory.V.Af.tw (ρ' i) (cycBar E Ω l ^ (-(j : ℤ)))) g).charpoly) ∧ ((∀ i, m i = 1) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ b : Multiset ℂ, UpperTheory.V.Af.FrobEig ι ρ w b → ∀ z ∈ b, ∀ z' ∈ b, ‖z‖ < (normV w : ℝ) * ‖z'‖) :=
  fun H => _root_.UpperTheory.V.Z.Win.Gu.endShapeT' H (_root_.UpperTheory.V.Z.Win.Gu.spehOf_alt H) (_root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal)
end UpperTheory.V.Z.Win.Gu
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.Ord
section At
variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {n : ℕ} (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
end At
def AutYAlt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
    (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
    (P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)
end U
def OrdScalAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → ∀ F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e, F ≠ 0 →
    ∀ (v : H.V) (b : Fin n → ℂ), (∀ j, b j ≠ 0 ∧ H.opC ι lam d (.inr (v, j)) F = b j • F) →
      ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient (Y.σl v).ρ (PS ω) ∧
        (∀ i (y : Uo ((H.Sl v).adicCompletion L)), (ω i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ j : Fin n, b j = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)
def PartPtAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (y : H.TK θ a K →ₐ[c.O] Qbar l),
      y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d),
        P lam d ξ Y ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F
def CoreOrdAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
      [Alg.IsCO c.O (H.TK θ a K)] (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ),
      H.IsUniv θ a K (maximalIdeal _) D ψ → ∀ lam ∈ H.admitted, ∀ y : H.TK θ a K →ₐ[c.O] Qbar l,
      H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam →
      ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ), P lam d ξ Y ∧ D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧
        ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
          ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i))
def AutUOAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → _root_.UpperTheory.V.Z.Ord.AutYAlt (hset Q τ₀) ι fun _ _ _ Y =>
      Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)
def EndOrdAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∀ J : Ideal B.B, R.IsJ B K J → ENDO B ι J
end UpperTheory.V.Z.Ord
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreEig
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eig_cont {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedField K] (I : Ideal R) (y : R →+* K) (a : ℝ)
    (h1 : a < 1) (h0 : 0 ≤ a) (hy : ∀ N, ∀ x ∈ I ^ N, ‖y x‖ ≤ a ^ N) {f : Γ → R} (hf : Alg.AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (hy N _ (Ideal.Quotient.eq.1 hg')).trans_lt hN
private theorem eig_chi_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial B :=
    { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
  have h := D.nat (Polynomial A) (Polynomial B) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
  refine Eq.trans ?_ h
  change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem eig_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) (b : ℕ → B)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem eig_tele {n : ℕ} {K : Type} [Field K] (f g : Fin n → K) (hg : ∀ i, g i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) (j : Fin n) : f j = g j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : Finset.univ.filter (fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have h1 := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (by simpa using hi)] at h1
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i) h1
private theorem eig_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S K : Type} [Group S] [Field K] (a : S →* kˣ) (ha : Function.Surjective a) (P Q : S →* K)
    (h1 : ∀ s, a s ∈ Uo k → P s = Q s) (h2 : ∀ s, a s = unif k → P s = Q s) (s : S) : P s = Q s := by
  obtain ⟨t, ht⟩ := ha (unif k)
  have e : s = s * (t ^ ord k (a s))⁻¹ * t ^ ord k (a s) := by group
  have h3 : a (s * (t ^ ord k (a s))⁻¹) ∈ Uo k := by
    rw [map_mul, map_inv, map_zpow, ht, ← div_eq_mul_inv]
    exact GlAx.val_div_ord _
  rw [e, map_mul, map_mul Q, h1 _ h3, map_zpow, map_zpow, h2 t ht]
section Pow
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
private theorem eig_ne (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private theorem eig_mul (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) :
    algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]
private theorem eig_ht {n : ℕ} (lam : Wt F l n) (i : Fin n) (x : (w.adicCompletion F)ˣ) :
    algPow w (-htW lam i) (x : w.adicCompletion F) * algPow w (lowW lam i) (x : w.adicCompletion F) *
      algPow w (fun _ => 1) (x : w.adicCompletion F) ^ (i : ℕ) = 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  simp only [finprod_eq_prod_of_fintype]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  have h0 : j.1 (x : w.adicCompletion F) ≠ 0 := (map_ne_zero j.1).2 x.ne_zero
  rw [zpow_one, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0]
  simp [htW]
end Pow
private theorem eig_loc (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → Weil h →* Qbar l)
    (h1 : ∀ i s, a s ∈ Uo _ → ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ) *
      algPow w (lowW lam i) (a s : w.adicCompletion F) = ι.symm (ω i (a s)))
    (h2 : ∀ (j : Fin n) s, a s = Hi.unif _ → ι (∏ i with i ≤ j, ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ)) =
      (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) (s : Weil h) : ψ i s = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F) := by
  let Q : Weil h →* Qbar l :=
    { toFun := fun s => ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      map_one' := by simp [algPow]
      map_mul' := fun s t => by
        simp only [map_mul, Units.val_mul, eig_mul]
        ring }
  have he := Loc.epsArt hG h hl a ha
  have hq : ((normV w : ℕ) : Qbar l) ≠ 0 := by
    rw [← resCard_eq_normV]
    exact Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[w.adicCompletion F])).ne'
  refine eig_gen a ha.surj (ψ i) Q (fun s hs => ?_) (fun s hs => ?_) s
  · have hd : deg s = 0 := by
      have := ha.ord_eq s
      rw [ord_eq_zero hs] at this
      omega
    have e1 := h1 i s hs
    rw [he, hd, zpow_zero, one_mul] at e1
    have e2 := eig_ht w lam i (a s)
    change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
    rw [← e1]
    linear_combination (-ψ i s) * e2
  · have hd : deg s = -1 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_one GlAx.unif_spec] at this
      omega
    have e1 := eig_tele (fun i => ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ))
      (fun i => (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω i (a s)) * (((normV w : ℕ) : Qbar l) ^ (i : ℕ))⁻¹))
      (fun i => mul_ne_zero (inv_ne_zero (eig_ne w _ _)) (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _))
        (inv_ne_zero (pow_ne_zero _ hq)))) (fun j => ι.injective ?_) i
    · have e2 := eig_ht w lam i (a s)
      have e3 := eig_ne w (lowW lam i) (a s)
      have e4 := pow_ne_zero (i : ℕ) hq
      rw [he, hd, mul_pow, zpow_neg_one, inv_pow] at e1
      change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      field_simp at e1
      linear_combination (-ψ i s) * e2 + algPow w (-htW lam i) (a s : w.adicCompletion F) * e1
    · have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i => i ≤ j := by
        ext i; simp [Nat.lt_succ_iff]
      rw [h2 j s hs, psEig, e, hs, map_prod ι, map_prod ι, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, ι.apply_symm_apply, map_inv₀, map_inv₀, map_pow, map_natCast, ← resCard_eq_normV]
      rfl
private theorem eig_det {n : ℕ} {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] (y : R →+* Qbar l)
    (D : W.GDet n R Γ) (r : Γ →* GL (Fin n) (Qbar l)) (hr : Continuous r) (S : Set Γ) (hS : Dense S)
    (hD : ∀ i, Continuous fun g => y (D.lam i (MonoidAlgebra.single g 1)))
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map y = (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    D.map y = W.GDet.ofRep (W.mat r) := by
  refine AlgebraTools.Det.extDense _ _ S hS (fun i _ => (hD i).congr fun g => ?_)
    (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hr) i) fun g hg => ?_
  · simp [W.GDet.lam, eig_chi_map]
  · rw [eig_chi_map, (AlgebraTools.Det.repApi _).2.1]
    exact h g hg
private theorem eig_ord (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) {R : Type} [CommRing R]
    (y : R →+* Qbar l) (ψ : Fin n → Dec (F := F) B →* Rˣ) (hψ : ∀ i, Continuous fun g => y (ψ i g : R))
    (ε : Dec (F := F) B →* Rˣ) (he : ∀ g, y (ε g : R) = (cycBar F Ω l (g : G F Ω) : Qbar l))
    (t : Fin n → Uo (w.adicCompletion F) → R) (u : Fin n → R)
    (u1 : ∀ i (s : Weil h) (g : Dec (F := F) B) (x : Uo (w.adicCompletion F)), (g : G F Ω) = (s : G F Ω) → a s = x →
      (ψ i g * ε g ^ (i : ℕ) : Rˣ) * t i x = 1)
    (u2 : ∀ (j : Fin n) (s : Weil h) (g : Dec (F := F) B), (g : G F Ω) = (s : G F Ω) → a s = Hi.unif _ →
      ((∏ i with i ≤ j, ψ i g * ε g ^ (i : ℕ) : Rˣ) : R) = u j)
    (h1 : ∀ i (x : Uo (w.adicCompletion F)), (ω i x : ℂ) *
      ι (y (t i x) / algPow w (lowW lam i) ((x : (w.adicCompletion F)ˣ) : w.adicCompletion F)) = 1)
    (h2 : ∀ j : Fin n, ι (y (u j)) = (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) : OrdChar ι a (ω i) (htW lam i) (W.pushCh y (ψ i)) := by
  refine ⟨hω i, Units.continuous_iff.2 ⟨hψ i, ((hψ i).comp continuous_inv).congr fun g => by simp⟩, fun s g hg _ => ?_⟩
  obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
  refine eig_loc hG h hl a ha ι lam ω
    (fun i => ((Units.coeHom _).comp (W.pushCh y (ψ i))).comp (Subgroup.inclusion (Weil_le_Dec h)))
    (fun i s hs => ?_) (fun j s hs => ?_) i s
  · have e1 := congrArg y (u1 i s (Subgroup.inclusion (Weil_le_Dec h) s) ⟨_, hs⟩ rfl rfl)
    have e2 := congrArg ι.symm (h1 i ⟨_, hs⟩)
    rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he, map_one, Subgroup.coe_inclusion] at e1
    rw [map_mul, ι.symm_apply_apply, map_one, mul_div_assoc', div_eq_one_iff_eq (eig_ne _ _ _)] at e2
    change y (ψ i (Subgroup.inclusion (Weil_le_Dec h) s) : R) * _ * _ = _
    rw [← e2]
    linear_combination (ι.symm (ω i (a s) : ℂ)) * e1
  · refine Eq.trans (congrArg ι (Eq.trans ?_ (congrArg y (u2 j s (Subgroup.inclusion (Weil_le_Dec h) s) rfl hs)))) (h2 j)
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he]
    rfl
private theorem eig_pt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] :
    Fact (∀ y : R →ₐ[c.O] Qbar l, (∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → R), Alg.AdicCont (maximalIdeal R) f → Continuous fun g => y.toRingHom (f g)) ∧
      ∀ (v : H.V) (g : Dec (F := L) (H.pl v)), y.toRingHom (H.epsV R v g : R) = (cycBar L Ω l (g : G L Ω) : Qbar l)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨-, b, b1, b0, hb⟩ := (GradeZeroInterpolatingElement.coPt c R).1 y
  exact ⟨fun Γ _ f hf => eig_cont _ y.toRingHom b b1 b0 hb hf,
    fun v g => (y.commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l (g : G L Ω) : ℤ_[l]))).trans rfl⟩

theorem UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (y : H.TK θ a K →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d), F ∈ Y.Y → F ≠ 0 → (∀ w j, H.opC ι lam d (.inl (w, j)) F = ι (y (H.gen θ a K (.inl (w, j)))) • F) → D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v (ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i (u : Uo ((H.Sl v).adicCompletion L)), (ω i u : ℂ) * ι (H.finPart θ (y.toRingHom.comp (algebraMap A _)) lam v i u) = 1) → (∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) → ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i)) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι a K _ _ D ψ hU y lam d ξ Y F hF hF0 hev
  obtain ⟨hc, he⟩ := (eig_pt H (H.TK θ a K)).out y
  refine ⟨eig_det _ D Y.r Y.cont _ hH.dense (fun i => hc _ _ (hU.cont i)) ?_,
    fun v ω hω h1 h2 i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hU.frob ⟨w, hw⟩ B σ hB hσ]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Polynomial.map_map]
    refine (eig_pol _ n _ _ (Y.a ⟨w, hw⟩) fun j hj => ?_).trans (Y.frob ⟨w, hw⟩ B σ hB hσ).symm
    unfold HSet.genW
    split_ifs with h
    · have e := hev ⟨w, hw⟩ ⟨j - 1, h.2⟩
      have e' := Y.sph ⟨w, hw⟩ (j - 1 + 1) F hF
      have e2 := smul_left_injective ℂ hF0 (e.symm.trans e')
      rw [show j - 1 + 1 = j by omega] at e2
      exact e2
    · rw [show j = 0 by omega, Y.a_zero, map_one]
  · have h3 := eig_ord hN.aut.art (H.ovr v) (hH.Sl_over v) (H.art v) (hH.art_spec v) ι lam ω hω _ (ψ v)
      (fun i => hc _ _ (hU.ψ_cont v i)) _ (he v)
    have h4 := h3 (fun i x => algebraMap A (H.TK θ a K) (θ (eV n H.Sl v i x))) (fun j => H.gen θ a K (.inr (v, j)))
      (hU.ψ_unit v) (hU.ψ_unif v) h1 h2
    exact h4 i
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobLG
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
theorem frobLG'_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (hc : Continuous r) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hB : GlobalTheory.LFun.HasSatGL w τ.ρ B)
    (H : Win.LocGlobT ι r w τ) : Af.FrobEig ι r w (Af.algSat n (normV w) B) :=
  _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P F Ω l ι n r hc w hw τ B hB fun A h rc hrc => (H A h rc hrc).1 hw
end
end UpperTheory.Gal.projectedFormsSystemPart
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOk
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Pa.Lev
section Th
variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
end Th
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} {b : TWBase (pairOf B.u) J Empty D}
  {V : s.Lev} {h : (globOf r V).Hom (globOf r V0)} {q : ℕ} {w : Fin q → Plc L}
def LocalLevelConditions (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (ph ta : Fin q → (globOf r V).G₀) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, (∀ m : A.P, (∀ y : _root_.UpperTheory.V.Pa.LevPtAlt A ι, y.sp m = 0) → m = 0) ∧ ∀ (y : _root_.UpperTheory.V.Pa.LevPtAlt A ι) j,
    _root_.UpperTheory.V.Z.Win.LocRelT l (x j) (δ j) (y.σ j).ρ ((mat y.rep (ph j)).map ι) ((mat y.rep (ta j)).map ι)
end UpperTheory.V.Pa.Lev
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartLinkAltAlt
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.Gal.projectedFormsSystemPart
open UpperTheory.V.Z.Ord UpperTheory.Zero.LLC
def PartLinkAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → ∀ (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ →
    ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
end UpperTheory.Gal.projectedFormsSystemPart
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartRep
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
def Ord1Alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (b : ℕ) (φ : Fin n → Uo k → ℂ) (μ : Fin n → ℂ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (b + 1) → φ i y = 1) → Reg k μ → Module.rank ℂ (locEig π b φ μ) ≤ 1
def SphSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ σ σ', IsAutRepU σ → IsAutRepU σ' →
    (∀ w, IsSplitAt w → ∃ τ, Cp σ w τ ∧ Cp σ' w τ) → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev = YOf Q ι τ₀ e ξ σ' ⊓ zL (hset Q τ₀) θ ι x.toRingHom lam c0 ev d ((hset Q τ₀).X.rpF ℂ d m)
def AtSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), ∀ σ σ', IsAutRepU σ → IsAutRepU σ' → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → ∀ π : CuspSub L n, At π σ → At π σ'
def BcOfAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.BCT.Unr E →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → Af.IsIrr ρ →
    (∀ᶠ w : Plc E in cofinite, IsSplitAt w → ∀ τ, Cp σ w τ → _root_.UpperTheory.V.Z.Win.LocGlobT ι ρ w τ) →
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B
def PartRepAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom → ∀ (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ → ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ →
    Af.IsIrr ρ → D.map z.toRingHom = W.GDet.ofRep (W.mat ρ) → ∀ Y : H.PartAltAlt ι lam ξ,
    Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) ≠ ⊥ → ∃ g : GL (Fin n) (Qbar l), ∀ h, Y.r h = g * ρ h * g⁻¹
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ZEqDimE
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
open UpperTheory.V.Z.J.D
namespace UpperTheory.V.Z.Desc.V0
section Abs
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
end Abs
section Set
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (K : H.Lev) {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ)
def IsDimEAlt (D : ℕ) : Prop :=
  ∃ (x : A →ₐ[c.O] Qbar l) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d)
    (ev : H.Op → ℂ), H.IsSpec θ ι x.toRingHom lam ξ c0 sp ∧ (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) ∧
    zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ ∧
    (∀ Y : H.PartAltAlt ι lam ξ, Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) ∧
    D = Module.finrank ℂ ↥(zPart H θ ι x.toRingHom lam ξ K c0 ev ⊓ ePart ((trF H d).comp β) a N)
end Set
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {m : ℕ}
variable {r : Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r)
end U
def CountEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n), ∃ a₀ : ℕ,
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) →
    zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → (∀ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) →
    ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
      π.IsLocComp (s.w s.v0) C.o ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧ IsAutRepU σ ∧
      ∀ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), (∀ g ∈ a.support, g ∈ KO _ (Fin n)) →
        (Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ⊓ eC Q τ₀ d a N) : Cardinal) = a₀ * Module.rank ℂ (cInv C ι τ₀ a N)
def ZEqDimEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 →
    ∃ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), IsE (KO _ (Fin n)) (Kc _ n 1) a N ∧ ¬ l ∣ N ∧
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : (hset Q τ₀).X.I.T →* Aˣ), (hset Q τ₀).IsWt θ → ∀ (lam : Wt L l n) (K : (hset Q τ₀).Lev) (D D' : ℕ),
    _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a N D → _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a N D' → 1 ≤ D ∧ D = D'
def NumJEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    NumE B Λ J
end UpperTheory.V.Z.Desc.V0
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharPolOfChar
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem charPol_supp (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.Zero.LLC.LawsT a ha rc)
    (x : IrrGL (k := w.adicCompletion E)) (s : Multiset (IrrGL (k := w.adicCompletion E))) (hs : HasSupport x.rep s) (g : Weil h) :
    (rc x).charPol g = (s.map fun y => (rc y).charPol g).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : s = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
  rw [he, H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)
private theorem charPol_ofChar (H : UpperTheory.Zero.LLC.LawsT a ha rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
end
theorem UpperTheory.V.Z.Sym.W.eigW_alt :
    _root_.UpperTheory.V.Z.Sym.W.EigWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n r w hl A h a ha τ hτ hP ψ hψ hsub s
  have Q := P.litN
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  have hg : UpperTheory.V.Z.Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  have hx := ((hτ A h rc hrc).1 hl).isWDOf hg
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hpol : (rc (algNorm τ)).charPol s =
      (r (s : G L Ω)).val.charpoly.map ι.toRingHom := by
    rw [← hw]; exact hN.charPol_wdOf hl ht ι s
  obtain ⟨a', ha', H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := Q.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective Q.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  let τ' : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, τ.ρ, τ.smooth, τ.irred⟩
  have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ' hsub).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hc := charPol_supp Q.loc.zel H (algNorm τ) _ h2 s
  have e0 : (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = -(((n : ℂ) - 1) / 2) := by push_cast; ring
  rw [← hpol, hc, UpperTheory.V.Z.Sym.W.psPol, Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  have e1 : (IrrGL.ofChar (ψ i) (hψ i)).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) =
      IrrGL.ofChar (ψ i * absPow (w.adicCompletion L) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
        ((hψ i).mul (isSmoothChar_absPow _)) := IrrGL.tw_ofChar _ _ _ _
  rw [e1, charPol_ofChar H]
  simp only [e0, MonoidHom.mul_apply]
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalExW
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.galois_exists_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GalExWAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Sym.W.plain_of_statement :
    _root_.UpperTheory.V.Z.Sym.W.PlainOfAlt := by
  intro _ L _ _ n w τ ψ hψ hs hl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    exact hl i j h
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWitApi
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactBis
noncomputable abbrev UpperTheory.V.Z.Win.WitA.weak_admissible_iso := @UpperTheory.V.Z.Win.WitA.iso
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
section
variable (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
end
theorem WitQ.weak_admissible_iso (e : RepIso r r') (h : _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.WitAQ ι r' := by
  intro K _ _ _ _ _ _ h2 hi
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed F, haveI := IsAlgClosure.isAlgebraic (R := F) (K := Ω); Algebra.IsAlgebraic.tower_top (K := F) K⟩
  obtain ⟨g, hg⟩ := e
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    ⟨g, fun s => hg _⟩
  have hirr : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
    obtain ⟨a, ha⟩ := e'.symm'
    let A := Matrix.mulVecLin (a : Matrix (Fin n) (Fin n) (Qbar l))
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    have hinv := hi.2.2 (W.comap A) le_top (fun s v hv => by
      have hmem := hW s _ (show A v ∈ W from hv)
      rw [ha s] at hmem
      simpa [A, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hmem)
    have hsurj : Function.Surjective A := fun v =>
      ⟨((a⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [A]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hinv with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  exact (h K h2 hirr).weak_admissible_iso e'
theorem IsAutCsdN.weak_admissible_iso [IsCMField F] (e : RepIso r r') (h0 : AutCsd0 ι r') (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) :
    _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' := ⟨h0, fun c => (h.2 (continuous_of_iso c e.symm')).weak_admissible_iso e⟩
end UpperTheory.GalN.V
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
variable {l : ℕ} [Fact l.Prime]
section Pt
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)
variable (T : TWGrp G0)
end Pt
section Mod
variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)
variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)
end Mod
section Bar
variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
end Bar
section Ar
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}
def LevelAtOrdinaryDeterminantRing {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
def LevelIdealCondition (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x
end Ar
def HidaFamilyCondition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PointTheoremBaseObject ι J ∧ _root_.UpperTheory.V.Th.LevelIdealCondition B J
def HasHeckeOperatorDense : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T
def OrdinaryMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → _root_.UpperTheory.V.Th.LevelIdealCondition B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0
end UpperTheory.V.Th
end
end
end
