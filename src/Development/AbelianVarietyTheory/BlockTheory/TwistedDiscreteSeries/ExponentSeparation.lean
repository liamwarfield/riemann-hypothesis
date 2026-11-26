module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def strictCone (ϖ : kˣ) (r : ℕ) : Set (Fin r → kˣ) :=
  {t | ∃ a : Fin r → ℤ, StrictAnti a ∧ t = fun i => ϖ ^ a i}


open Classical in
def IsExp {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V)
    (E : Multiset ((Fin r → kˣ) →* ℂˣ)) : Prop :=
  ∀ χ, expMult π χ = (E.count χ : ℕ∞)

def charSum {r : ℕ} (E : Multiset ((Fin r → kˣ) →* ℂˣ)) (t : Fin r → kˣ) : ℂ :=
  (E.map fun χ => (χ t : ℂ)).sum

def ExponentsSeparate : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (r n : ℕ) (V : Fin n → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ (GL (Fin r) k) (V i)),
      (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) →
      (∀ i j, i ≠ j → IsEmpty ((π i).Equiv (π j))) →
      (∀ i, fixed (π i) (iwahori k (Fin r)) ≠ ⊥) →
      ∀ (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)), (∀ i, IsExp (π i) (E i)) →
        ∀ c : Fin n → ℂ, (∀ t ∈ strictCone ϖ r, ∑ i, c i * charSum (E i) t = 0) → ∀ i, c i = 0

theorem IsExp.unramified {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin r) k) V} {E : Multiset ((Fin r → kˣ) →* ℂˣ)}
    (h : IsExp π E) {χ : (Fin r → kˣ) →* ℂˣ} (hχ : χ ∈ E) {t : Fin r → kˣ}
    (ht : t ∈ torusO k (Fin r)) : χ t = 1 := by
  classical
  have h0 : expMult π χ ≠ 0 := by
    rw [h χ]
    have : Multiset.count χ E ≠ 0 := Multiset.count_ne_zero.2 hχ
    intro h1
    apply this
    convert Nat.cast_eq_zero.1 h1
  have h1 := Model.scalar_of_isSubquotient (g := t) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0)
    (fun v => Subtype.ext (by
      have h2 : jacBU π t v.1 = _ := v.2 ⟨t, ht⟩
      show jacBU π t v.1 = _
      simpa using h2)) 1
  ext
  simpa using h1


end GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

section Abstract

variable {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E]

def HasRationalTest (σ : K →+* ℂ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ e ∈ S, ∀ a, ∃ z : K, σ z = ψ a e

end Abstract

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

end Interface

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowTestModel (R : RealDat D A Ks) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (R.HE.H →ₗ[ℂ] ℂ)), (∀ e : R.HE.H, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), ∃ z : D.what₂.LL, D.what₂.embLL z = ψ a (R.Th t (R.jX t x))

def twFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E →ₗ[ℂ] ℂ) : Tw s E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.out x))
  map_add' x y := by rw [Tw.out_add, map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [Tw.out_smul, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

def untwFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Tw s E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.mkL s E x))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

theorem test_tw_iff {K E : Type} [Field K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {σ σ' : K →+* ℂ}
    (h : ∀ a, σ' a = cj s (σ a)) {ι : Type} {X : ι → Type} (v : ∀ t, X t → E) :
    (∃ (n : ℕ) (ψ : Fin n → (Tw s E →ₗ[ℂ] ℂ)), (∀ e : Tw s E, (∀ a, ψ a e = 0) → e = 0) ∧
      ∀ t x a, ∃ z : K, σ' z = ψ a (Tw.mk s (v t x))) ↔
    (∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ t x a, ∃ z : K, σ z = ψ a (v t x)) := by
  constructor
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => untwFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    refine ⟨z, ?_⟩
    have := congrArg (cj s) ((h z).symm.trans hz)
    rw [cj_cj] at this
    exact this
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => twFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    exact ⟨z, (h z).trans (congrArg (cj s) hz)⟩

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop := 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def transl (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) :
    MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def thetaTranslates (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (MMap (R.MW i (sg0 D A))) :=
  {y | ∃ (g : G) (x : (R.HV i t).H), y = transl R i g (R.thF i t x)}

def SpanAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  Submodule.span ℂ (thetaTranslates R i t) = R.Wall i (sg0 D A)

def goodModel (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def GoodRangeAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  LinearMap.range (R.thG i t) = goodModel R i

theorem range_eq_comap_iff {X H M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup M]
    [Module ℂ M] (e : H →ₗ[ℂ] M) (f : X →ₗ[ℂ] H) (p : X →ₗ[ℂ] M) (U : Submodule ℂ M) (hinj : Function.Injective e)
    (hle : U ≤ LinearMap.range e) (hc : ∀ x, e (f x) = p x) :
    LinearMap.range f = U.comap e ↔ LinearMap.range p = U := by
  have hcomp : e ∘ₗ f = p := LinearMap.ext hc
  rw [← hcomp, LinearMap.range_comp]
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_self hle]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hinj]


set_option maxHeartbeats 1000000 in
theorem goodRangeAt_iff {R : RealDat D A Ks} (hW : R.models_HW) (hG : R.thP_thG) (i : Fin D.R.m) (t : T) :
    GoodRangeAt R i t ↔
      LinearMap.range (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ∘ₗ R.thF i t) = R.Wat i (sg0 D A) R.triv :=
  range_eq_comap_iff (R.HW i (sg0 D A)).e (R.thG i t) _ (R.Wat i (sg0 D A) R.triv) (hW i (sg0 D A)).1
    (le_of_le_of_eq inf_le_left (hW i (sg0 D A)).2.1.symm) (fun x => hG i t x)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Arith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

abbrev pS : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qS : ℕ := ((Wc D i).sig (tauE D τ)).2

abbrev eS : ℚ := (D.hc τ).e i

abbrev aP (a : ℕ) : ℕ := aPl D i (pS D i τ) τ a

abbrev aM (a : ℕ) : ℕ := aMi D i (pS D i τ) (qS D i τ) τ a

def centred (a : ℕ) : ℚ := Formalism.L2.NTheta.lamAt (D.hc τ) a + eS D i τ

def aPlusQ (a : ℕ) : ℚ := centred D i τ a - ((pS D i τ : ℚ) - ((a : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2

def dRowQ (c : ℕ) : ℚ := centred D i τ (pS D i τ + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2

def dShift : ℚ := ((pS D i τ : ℚ) - (qS D i τ : ℚ)) / 2 - eS D i τ - 1 / 2

def thetaWt (a : ℕ) : ℤ :=
  if a < pS D i τ then (aP D i τ a : ℤ)
  else if a < pS D i τ + D.R.t then 0
  else -(aM D i τ (qS D i τ - 1 - (a - (pS D i τ + D.R.t))) : ℤ)

def IsDataOf (w : IndefiniteWeightData.WeightData) : Prop :=
  w.k = D.R.k ∧ w.m = D.R.m ∧ w.t = D.R.t ∧ w.j = (i : ℕ) + 1 ∧ (w.e : ℚ) = eS D i τ ∧
    (∀ a : Fin (D.R.k - 1), (w.v (a + 2) : ℚ) = (D.hc τ).v a) ∧ ∀ a : Fin D.R.m, (w.b (a + 1) : ℚ) = (D.hc τ).b a

structure ArithAt : Prop where

  sig : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)

  rank : pS D i τ + qS D i τ = D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t

  aP_eq_rat : ∀ a < pS D i τ, (aP D i τ a : ℚ) = aPlusQ D i τ a

  aM_eq : ∀ c < qS D i τ, (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c

  aPlus_antitone : ∀ a b, a ≤ b → b < pS D i τ → aP D i τ b ≤ aP D i τ a

  aM_anti : ∀ a b, a ≤ b → b < qS D i τ → aM D i τ b ≤ aM D i τ a

  aPlus_pos : ∀ a < pS D i τ, 1 ≤ aP D i τ a

  aM_pos : ∀ a < qS D i τ, 1 ≤ aM D i τ a

  kap_plus : ∀ a : Fin (pS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) : ℚ) =
      (aP D i τ a : ℚ) + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  kap_minus : ∀ c : Fin (qS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℚ) =
      -(aM D i τ (qS D i τ - 1 - c) : ℚ) - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  d_int : ∃ z : ℤ, dShift D i τ = z

  lamPrime_eq : ∀ w : IndefiniteWeightData.WeightData, IsDataOf D i τ w → ∀ a < D.R.r + D.R.t,
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ

  coef_isLamPrime : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ) ((i : ℕ) + 1) τ

  coef_eq : ∀ a : Fin (Vc D i).rank,
    ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℚ) = (thetaWt D i τ a : ℚ) + dShift D i τ

end Arith

structure InfTypesAt {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) : Prop where

  mu : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-eS D i τ)

  eta : HasInfExp D L.eta τ (1 / 2)

  chiV : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 τ (-eS D i τ)

  chiW : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 τ (-eS D i τ - 1 / 2)

end GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


theorem gap {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) {n : ℕ} (hn : n < Rk.r) :
    ((Rk.t : ℚ) + 3) / 2 ≤ |Formalism.L2.NTheta.lamAt h n + h.e j| := by
  have hk := Rk.m_add_three_le_k
  have hj := j.2
  have mono : ∀ a d : ℕ, a + d < Rk.r → Formalism.L2.NTheta.lamAt h (a + d) ≤ Formalism.L2.NTheta.lamAt h a := by
    intro a d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (a + d) hd).le.trans (ih (by omega))
  have val : ∀ (c : ℕ) (hc : c < Rk.m), Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
    intro c hc
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    simp
  unfold Ranks.r at hn mono
  by_cases hle : n ≤ Rk.k - 1 + j
  · have h1 := mono n (Rk.k - 1 + j - n) (by omega)
    rw [show n + (Rk.k - 1 + j - n) = Rk.k - 1 + j by omega, val j hj] at h1
    have h2 := h.gap_be j
    exact le_trans (by simp only [Fin.eta] at h1; linarith) (le_abs_self _)
  · have hj1 : (j : ℕ) + 1 < Rk.m := by omega
    have h1 := mono (Rk.k - 1 + (j + 1)) (n - (Rk.k - 1 + (j + 1))) (by omega)
    rw [show Rk.k - 1 + (j + 1) + (n - (Rk.k - 1 + (j + 1))) = n by omega, val _ hj1] at h1
    have h2 := h.gap_eb j hj1
    exact le_trans (by linarith) (neg_le_abs _)

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push_neg at hc
    apply h
    have hle : v.asIdeal ≤ (P.under (𝓞 D.host.F)).asIdeal := by
      intro x hx
      obtain ⟨y, hy, hyP⟩ := hc x hx
      have : y = algebraMap _ _ x := RingOfIntegers.ext hy
      subst this
      exact hyP
    have := v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top hle
    rwa [show P.under (𝓞 D.host.F) = v from HeightOneSpectrum.ext this.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteIndexDimensionCounts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def levW (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) :=
  lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i P)

def levK (i : Fin D.R.m) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) := levW R i R.triv

abbrev Cls (i : Fin D.R.m) : Type := Cl D.sp.cm (Wc D i).gram (levK R i)

def clsOf (i : Fin D.R.m) (x : UA D.sp.cm (Wc D i).gram) : Cls R i := Quotient.mk'' x

def levB (b : Bool) : LevelP R.Pg D.R.r ℂ := R.levL F b (sg0 D A)

def dimRho (i : Fin D.R.m) : ℕ := ∏ ρ, Module.finrank ℂ ((R.MW i (sg0 D A)).H ρ)

def dK (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wall i (sg0 D A))

def allAt (b : Bool) (i : Fin D.R.m) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (levB R F b))) (levChi _ (R.βW i) (R.datWp i (levB R F b)))

def d0 (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (allAt R F b i)

def dGood (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wat i (sg0 D A) (levB R F b))

def repB (b : Bool) (i : Fin D.R.m) : Representation ℂ (F.lvl b).P (R.HW i (sg0 D A)).H :=
  (R.gW i (sg0 D A)).comp (F.lvl b).P.subtype

def PrincipalCount (i : Fin D.R.m) : Prop :=
  Finite (Cls R i) ∧ Nonempty (Cls R i) ∧ (∀ c : Cls R i, Gam c = ⊥) ∧
    (∀ ρ, FiniteDimensional ℂ ((R.MW i (sg0 D A)).H ρ)) ∧ 1 ≤ dimRho R i ∧
    FiniteDimensional ℂ (R.Wall i (sg0 D A)) ∧ dK R i = Nat.card (Cls R i) * dimRho R i ∧ 1 ≤ dK R i

def ActsFreely (b : Bool) (i : Fin D.R.m) : Prop :=
  (∀ u ∈ (levB R F b).H, ∃ κ ∈ levW R i (levB R F b), rTup (R.βW i) (R.datWp i (levB R F b)) κ = u) ∧
    ∀ x κ : UA D.sp.cm (Wc D i).gram, (κ : GL (Fin (Wc D i).rank) (EAf D)) ∈ levW R i (levB R F b) →
      clsOf R i (x * κ) = clsOf R i x → rTup (R.βW i) (R.datWp i (levB R F b)) (κ : GL (Fin (Wc D i).rank) (EAf D)) = 1

def FreeCount (b : Bool) (i : Fin D.R.m) : Prop :=
  (∃ N : ℕ, Nat.card (F.lvl b).P * N = dK R i ∧
      Nonempty ((repB R F b i).asModule ≃ₗ[MonoidAlgebra ℂ (F.lvl b).P] (Fin N → MonoidAlgebra ℂ (F.lvl b).P))) ∧
    Nat.card (F.lvl b).P * d0 R F b i = dK R i ∧ 1 ≤ d0 R F b i

def GoodShare (δ : ℝ) (b : Bool) (i : Fin D.R.m) : Prop :=
  (1 - δ) * (d0 R F b i : ℝ) ≤ (dGood R F b i : ℝ) ∧ 0 < (1 - δ) * (d0 R F b i : ℝ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F

theorem GoodShare.ne_bot {δ : ℝ} {b : Bool} {i : Fin D.R.m} (h : GoodShare R F δ b i) :
    R.Wat i (sg0 D A) (levB R F b) ≠ ⊥ := by
  intro h0
  have h1 : (0 : ℝ) < dGood R F b i := lt_of_lt_of_le h.2 h.1
  unfold dGood at h1
  rw [h0, finrank_bot] at h1
  simp at h1

end Objects

theorem exists_last (D : D7) : ∃ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m :=
  ⟨⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩, by have := D.R.two_le_m; show D.R.m - 1 + 1 = _; omega⟩

def DefiniteFree : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
    PrincipalCount R i ∧ ∀ b : Bool, ActsFreely R F b i ∧ FreeCount R F b i

def DefiniteGoodShare : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x →
    Formalism.MainNotions.SizesAt L → GlobalTheory.GLq.ESerTie D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
      (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
      (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
      ∀ b : Bool, GoodShare R F (Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))) b i

def GoodVectorsDefinite : Prop := DefiniteFree ∧ DefiniteGoodShare

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem principalLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv) k = 1 := by
  have h : ∀ x, Formalism.L2.DIV.ext1 (R.toLevCh.datWp i R.toLevCh.triv).P.H (R.toLevCh.datWp i R.toLevCh.triv).P.chi x = 1 :=
    fun x => subgroupCharExtension_one_apply _ x
  unfold levChi Formalism.L2.DIV.levFn
  rw [h]
  simp [LevCh.datWp, datY]

end

end GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def typePl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def Differ (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c c' : Sys D) : Prop :=
  ∃ w d Rp, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb w d Rp ∧
    c w (dualLab d) ≠ c' w (dualLab d)

variable (t : T)

variable (P : LevelP R.Pg D.R.r ℂ)

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (PP : Pl D.host.E), R.C.P.Div k PP →
        ∀ (a : ℕ) (u : (kP PP)ˣ), (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 → (u : kP PP) = (a : kP PP) →
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            ((R.chi ((j : ℕ) + 1) PP u : ℂˣ) : ℂ) ∨
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            (((R.chi ((j : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GoodLiftPhase
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def withLift (X : CxData A) (θ : ∀ j t, X.FLC j t →ₗ[ℂ] X.W j) : CxData A := { X with θ' := θ }

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def cxPhase (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : CxData A.fam.amb :=
  withLift (R.toCx F) fun j t =>
    Tw.map (E := (R.HV j t).H) (F := (R.HW j (sg0 D A)).H) (twAt D.what₂.embLL A.v0) (ph j • R.thG j t)

theorem liftWeight_complexPoint_eq_twist (R : RealDat D A Ks) (F : Face D A) (b : Bool) (j : Fin D.R.m)
    (y : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → D.what₂.LL) :
    Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) ((R.toCx F).w0C b j (cpt A.v0.embedding y)) =
      (R.FW j).j (sg0 D A) (∑ k, y k • R.bL F b j k) := by
  have hn : (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) * (((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) = 1 := by
    have h0 : 0 < RealDat.nP F b := by
      unfold RealDat.nP
      exact_mod_cast Nat.card_pos
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h0).ne', Complex.ofReal_one]
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : (R.toCx F).w0C b j (cpt A.v0.embedding y) =
      ∑ k, A.v0.embedding (y k) • (R.toCx F).eW b j ((R.toCx F).bW b j A.v0 k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  have h2 : ∀ (s : Bool) (f : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → Tw s (R.HW j (sg0 D A)).H),
      Tw.out (∑ k, f k) = ∑ k, Tw.out (f k) := fun _ _ => rfl
  refine (h2 _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_smulₛₗ]
  show cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y k)) •
    ((((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) •
      (R.FW j).j (sg0 D A) (R.bL F b j k))) = _
  rw [smul_smul (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)), hn, one_smul, R.emb0, cj_cj]
  congr 1
  exact (DFunLike.congr_fun hs (y k)).symm

theorem twMap_smul {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (s : Bool) (c : ℂ) (f : E →ₗ[ℂ] E') : Tw.map s (c • f) = cj s c • Tw.map s f := by
  ext u
  show c • f (Tw.out u) = cj s (cj s c) • f (Tw.out u)
  rw [cj_cj]

theorem cxPhase_eq (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) :
    cxPhase R F ph = withLift (R.toCx F) fun j t => cj (twAt D.what₂.embLL A.v0) (ph j) • (R.toCx F).θ' j t :=
  congrArg (withLift (R.toCx F)) (funext fun j => funext fun t => twMap_smul _ (ph j) (R.thG j t))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

end
end
