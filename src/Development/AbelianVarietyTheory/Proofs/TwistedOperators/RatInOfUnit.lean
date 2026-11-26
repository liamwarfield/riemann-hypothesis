module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section Rat

variable {T L : Type} [Field L] (σ : L →+* ℂ) (t₀ : T)

def RatIn (f : T → ℂ) : Prop := ∀ t, f t ≠ 0 ∧ ∃ y : Lˣ, σ y = f t / f t₀

variable {σ t₀}

theorem RatIn.mul {f g : T → ℂ} (hf : RatIn σ t₀ f) (hg : RatIn σ t₀ g) : RatIn σ t₀ fun t => f t * g t := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  obtain ⟨hg0, z, hz⟩ := hg t
  refine ⟨mul_ne_zero hf0 hg0, y * z, ?_⟩
  rw [Units.val_mul, map_mul, hy, hz, mul_div_mul_comm]

theorem RatIn.inv {f : T → ℂ} (hf : RatIn σ t₀ f) : RatIn σ t₀ fun t => (f t)⁻¹ := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  refine ⟨inv_ne_zero hf0, y⁻¹, ?_⟩
  rw [map_units_inv, hy, inv_div, inv_div_inv]

theorem ratIn_const {κ : ℂ} (h : κ ≠ 0) : RatIn σ t₀ fun _ => κ := by
  intro _
  exact ⟨h, 1, by rw [Units.val_one, map_one, div_self h]⟩

theorem ratIn_of_unit {f : T → ℂ} (h : ∀ t, ∃ y : Lˣ, σ y = f t) : RatIn σ t₀ f := by
  intro t
  obtain ⟨y, hy⟩ := h t
  obtain ⟨y₀, hy₀⟩ := h t₀
  refine ⟨hy ▸ (map_ne_zero σ).2 y.ne_zero, y * y₀⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_units_inv, hy, hy₀, div_eq_mul_inv]

theorem RatIn.of_mul {f g u : T → ℂ} (hg : RatIn σ t₀ g) (hu : RatIn σ t₀ u) (h : ∀ t, f t * u t = g t) : RatIn σ t₀ f := by

  have e : f = fun t => g t * (u t)⁻¹ := funext fun t => by rw [← h t, mul_inv_cancel_right₀ (hu t).1]
  rw [e]
  exact hg.mul hu.inv

end Rat

variable {D : D7}

section Factor

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def Factor (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧
    ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
      (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
      Function.Surjective p ∧ (∀ t, Function.Injective (J t)) ∧
      (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧
      (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
      (∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I' ψ θ t P' = J t (p' P')) ∧
      ∃ P', p' P' ≠ 0 ∧ ∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m'

variable {X ψ θ}

theorem Factor.isConst [Nonempty T] {lam : T → ℂ} (h : Factor X ψ θ lam) : X.IsConst ψ θ lam := by
  unfold Factor at h
  obtain ⟨hlam, Pi, p, p', J, hp, hJ, hint, hI, hI', P', hP', hint'⟩ := h

  obtain ⟨P, hPP⟩ := hp (p' P')
  unfold Tri.IsConst
  refine ⟨⟨Classical.arbitrary T, hlam _⟩, P, P', fun t => ⟨fun h => ⟨hint t P h, hint' t h⟩, ?_, fun h => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    apply hP'
    apply hJ t
    rw [map_zero, ← hI' t P' (hint' t)]
    funext h
    exact hcon h
  · rw [hI t P, hI' t P' (hint' t), hPP]
    rfl

theorem Factor.eq_mul {lam c : T → ℂ} (h : Factor X ψ θ lam) (hc : X.IsConst ψ θ c) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, c t = κ * lam t := by
  unfold Factor at h
  unfold Tri.IsConst at hc
  obtain ⟨hlam, Pi, p, p', J, -, hJ, -, hI, hI', -⟩ := h
  obtain ⟨⟨t₁, ht₁⟩, P, P', hc⟩ := hc

  have key : ∀ t, lam t • p P = c t • p' P' := by
    intro t
    obtain ⟨hi, -, heq⟩ := hc t
    apply hJ t
    rw [map_smul, map_smul, ← hI t P, ← hI' t P' (fun h => (hi h).2)]
    funext h
    exact heq h
  have hne : p' P' ≠ 0 := by
    intro h0
    obtain ⟨hi, ⟨h₁, hh₁⟩, -⟩ := hc t₁
    apply hh₁
    rw [hI' t₁ P' (fun h => (hi h).2), h0, map_zero]
    rfl
  have hq : ∀ t, p P = ((lam t)⁻¹ * c t) • p' P' := by
    intro t
    rw [← smul_smul, ← key t, inv_smul_smul₀ (hlam t)]
  refine ⟨(lam t₁)⁻¹ * c t₁, mul_ne_zero (inv_ne_zero (hlam t₁)) ht₁, fun t => ?_⟩
  have e := smul_left_injective ℂ hne ((hq t).symm.trans (hq t₁))
  rw [← e]
  field_simp [hlam t]

end Factor

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks}

def NegIdx (V : HSp D) (q : ℕ) : Prop := ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) (V.rank - q) q

end GlobalTheory.ConstRatio

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def leviChar {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) : Levi R c →* ℂˣ :=
  ∏ j, (detChar (c j) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (c j) R) j)

theorem leviChar_apply {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) (g : Levi R c) :
    leviChar c χ g = ∏ j, χ j (Matrix.GeneralLinearGroup.det (g j)) := by
  simp [leviChar]

def wordMult {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (w : List ℂˣ) : ℕ∞ :=
  if w.length = n then jhMult (ofChar (torusChar fun i : Fin n => unrChar k (w.getD i 1))) (jacB π)
  else 0

theorem wordMult_ofFn {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (z : Fin n → ℂˣ) :
    wordMult π (List.ofFn z) = jhMult (ofChar (torusChar fun i => unrChar k (z i))) (jacB π) := by
  simp [wordMult]

theorem wordMult_of_ne {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) {w : List ℂˣ}
    (h : w.length ≠ n) : wordMult π w = 0 := by
  rw [wordMult, if_neg h]

def jacEquiv {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    (jac e π).Equiv (jac e τ) :=
  LocGL.equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap, fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v), fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem wordMult_congr {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V}
    {τ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv τ) (w : List ℂˣ) :
    wordMult π w = wordMult τ w := by
  unfold wordMult
  split_ifs
  · exact jhMult_congr_right _ (Representation.Equiv.mk (jacEquiv (points (Fin n)) φ).toLinearEquiv
      fun t => (jacEquiv (points (Fin n)) φ).isIntertwining' _)
  · rfl

instance instAddCommGroupTwo : ∀ x, AddCommGroup (Two V W x)
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup W)

instance instModuleTwo : ∀ x, Module ℂ (Two V W x)
  | false => inferInstanceAs (Module ℂ V)
  | true => inferInstanceAs (Module ℂ W)

def twoRep {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    ∀ x, Representation ℂ (GL (Two a b x) R) (Two V W x)
  | false => π₁
  | true => π₂

end GlobalTheory.SmGL.Exponents
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)

namespace GlobalTheory.DefFree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem finE_mem (V : HSp D) (h : GA D V) : finE V h ∈ UA D.sp.cm V.gram := by
  have h0 : matHom V h ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    let h' : HR (AF D.host.F) D.sp.cm.sig V.gram := h
    exact h'.2
  have h1 := Formalism.UG.P.bc_mem _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom ?c1 _ _ h0
  have h2 := Formalism.UG.P.bc_mem _ (Formalism.UG.sigR D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (swapAE D) ?c2 _ _ h1
  convert h2 using 1
  case e'_5 => rfl
  case e'_4 =>
    unfold UA Formalism.UG.UPts
    congr 1
  case c2 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [swapAE, sigR, Formalism.UG.sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  case c1 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

def finU (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (finE_mem V)

theorem coe_finU (V : HSp D) (h : GA D V) : (finU V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

def clsA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (h : GA D V) : Cl D.sp.cm V.gram K :=
  Quotient.mk'' (finU V h)

def evAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) :
    MMap M →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ where
  toFun T := (LinearMap.proj h : (GA D V → ℂ) →ₗ[ℂ] ℂ).compMultilinearMap T
  map_add' T T' := by ext v; simp
  map_smul' c T := by ext v; simp

theorem evAt_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) (T : MMap M) (v : M.Vec) :
    evAt M h T v = T v h := rfl

def eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P → ℂ) :
    Submodule ℂ M :=
  ⨅ g : P, LinearMap.ker (ρ g - χ g • LinearMap.id)

theorem mem_eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ G M} {P : Subgroup G}
    {χ : P → ℂ} {x : M} : x ∈ eig ρ P χ ↔ ∀ g : P, ρ g x = χ g • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

abbrev GProd (D : D7) : Type :=
  (D.nd.PlG 0 → GlobalTheory.BadShare.GG (D.host.g 0) D.R.r) × (D.nd.PlG 1 → GlobalTheory.BadShare.GG (D.host.g 1) D.R.r)

end GlobalTheory.DefFree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteClassSum

theorem invariant_sup {G X : Type} [Group G] {A B : Subgroup G} {Φ : G → X} (hA : ∀ k ∈ A, ∀ h, Φ (h * k) = Φ h)
    (hB : ∀ k ∈ B, ∀ h, Φ (h * k) = Φ h) : ∀ k ∈ A ⊔ B, ∀ h, Φ (h * k) = Φ h := by
  let S : Subgroup G :=
    { carrier := {k | ∀ h, Φ (h * k) = Φ h}
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha]
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {a} ha h => by rw [← ha (h * a⁻¹), inv_mul_cancel_right] }
  exact fun k hk => (sup_le (show A ≤ S from hA) (show B ≤ S from hB) : A ⊔ B ≤ S) hk

theorem integral_eq_sum {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] (ν : Measure G) [ν.IsMulLeftInvariant] (π : G →* H) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1)
    {I : Type} [Fintype I] (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i)
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ h, Φ (γ * h) = Φ h) (hr : ∀ k ∈ J.comap π, ∀ h, Φ (h * k) = Φ h) :
    (∀ i, Finite (Bridge.stab (π.comp Γ.subtype) J (y i))) ∧ IntegrableOn Φ 𝓖 ν ∧
      ∫ h in 𝓖, Φ h ∂ν = ∑ i, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y i)) : ℂ))⁻¹ * Φ (a i) := by
  have hs : ∀ i, (Bridge.stab (π.comp Γ.subtype) J (y i) : Set Γ) = {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    rw [SetLike.mem_coe, Bridge.mem_stab, Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, ha]
    rfl
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π}.Finite := fun i =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ _ h𝓖 (h1 ▸ one_ne_zero) (h1 ▸ ENNReal.one_ne_top) (a i)
  have him : ∀ i, {γ : G | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ J.comap π} =
      Subtype.val '' {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hu : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ J.comap π, x = γ * a i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, ((γ : G) * a i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, ha, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, ha]; rfl⟩
  obtain ⟨-, hi, he⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (h1 ▸ ENNReal.one_ne_top) I a hu (fun i => him i ▸ (hfin i).image _) Φ hl hr
  refine ⟨fun i => ?_, hi, ?_⟩
  · have := hfin i
    rw [← hs] at this
    exact this
  · rw [he, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, ← Nat.card_coe_set_eq]
    rfl

theorem classSumIntegral : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.ClassSumIntegral := by
  intro D V _ K hK μ 𝓕 hμ I _ y hy z hz Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have := hμ.1.1
  have hr : ∀ k ∈ K.comap (Lev.finE V), ∀ h, Φ (h * k) = Φ h := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact invariant_sup hΦ.level hΦ.real
  have ho : IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) := hK.1
  have h1 : μ ((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  exact integral_eq_sum μ (finHom V).rangeRestrict (GQ V) hμ.2 (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) ho h1 y hy z hz Φ hΦ.left hr

end GlobalTheory.DefiniteClassSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Ker.HeisDeriv

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
  {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {f : WO V W → ℂ}

theorem dRho_dir_linear (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau) :
    (∀ z z' : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z + z') f =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z' f) ∧
    ∀ (t : ℝ) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((t : ℂ) • z) f =
      (t : ℂ) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsm := GlobalTheory.OrientedHeis.theta_sm hσ hf
  have key : ∀ y : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f =
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W)
        (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1)) f := fun y => by
    rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, GlobalTheory.OrientedHeis.dLine_eq_hD hσ hψ (GlobalTheory.OrientedHeis.isRealDir_lineAt hθ τ y)]
  have hlin_add : ∀ u u' : GlobalTheory.FockCompare.RW W V,
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (u + u') f =
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u f +
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u' f := by
    intro u u'
    funext w
    simp only [Pi.add_apply, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_add (f := _)]
    push_cast
    ring
  have hlin_smul : ∀ (t : ℝ) (u : GlobalTheory.FockCompare.RW W V),
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (t • u) f =
        (t : ℂ) • GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V)
          (GlobalTheory.OrientedHeis.omO V W) u f := by
    intro t u
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_smul, Complex.real_smul]
    push_cast
    ring
  have hadd_u : ∀ y y' : Matrix (Fin W.rank) (Fin V.rank) ℂ, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ (y + y') 1) =
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) + GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y' 1) := by
    intro y y'
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    exact Pi.single_add (f := fun _ => Matrix (Fin W.rank) (Fin V.rank) ℂ) τ y y'
  have hsmul_u : ∀ (t : ℝ) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ),
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ ((t : ℂ) • y) 1) = t • GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) := by
    intro t y
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    have e : ((t : ℂ) • y) = t • y := by
      ext a b
      simp [Complex.real_smul]
    rw [e]
    exact Pi.single_smul' τ t y
  refine ⟨fun y y' => ?_, fun t y => ?_⟩
  · rw [key, key, key, hadd_u, hlin_add]
  · rw [key, key, hsmul_u, hlin_smul]

theorem matrix_eq_sum_re_im {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • Matrix.single i j (1 : ℂ) +
      (((z i j).im : ℝ) : ℂ) • Matrix.single i j Complex.I) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single z]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem dRho_eq_sum_heisDer (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
        (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := by
  obtain ⟨hadd, hsm⟩ := dRho_dir_linear hψ hθ hf τ
  let L : Matrix (Fin W.rank) (Fin V.rank) ℂ →+ (WO V W → ℂ) :=
    AddMonoidHom.mk' (fun y => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f) hadd
  have hL : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = L y := fun _ => rfl
  rw [hL]
  conv_lhs => rw [matrix_eq_sum_re_im z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add (f := _), ← hL, ← hL, hsm, hsm]
  simp [heisDer]

theorem theta_finsetSum {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ} (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) :
    IsThetaFunO ψ V W (∑ i ∈ s, g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact theta_zero) ?_
  intro a t ha ih hg
  rw [Finset.sum_insert ha]
  exact theta_add (hg a (Finset.mem_insert_self a t)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem sobO_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (∑ i ∈ s, g i) ≤ ∑ i ∈ s, sobO ψ θ μ 𝓕 d (g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => ?_) ?_
  · have h0 := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := (0 : WO V W → ℂ)) d 0
    simp only [smul_zero, enorm_zero, zero_mul] at h0
    simp [h0]
  · intro a t ha ih hg
    have ha' : IsThetaFunO ψ V W (g a) := hg a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, IsThetaFunO ψ V W (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sobO_add_le hψ hθ ha' (theta_finsetSum t ht) d).trans (add_le_add le_rfl (ih ht))

theorem sobO_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * sobO ψ θ μ 𝓕 (d + 1) f := by
  classical
  have hD : ∀ a, IsThetaFunO ψ V W (heisDer ψ θ a f) := fun a => by
    simpa [wordAct] using theta_word hψ hθ [a] hf
  have hT : ∀ i j, IsThetaFunO ψ V W ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
      (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := fun i j =>
    theta_add (theta_smul _ (hD _)) (theta_smul _ (hD _))
  have hre : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := fun r => by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [dRho_eq_sum_heisDer hψ hθ hf τ z]
  refine (sobO_sum_le hψ hθ Finset.univ (fun i _ => theta_finsetSum Finset.univ fun j _ => hT i j) d).trans ?_
  calc _ ≤ ∑ i, ∑ j, (ENNReal.ofReal |(z i j).re| + ENNReal.ofReal |(z i j).im|) *
        sobO ψ θ μ 𝓕 (d + 1) f := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (sobO_sum_le hψ hθ Finset.univ (fun j _ => hT i j) d).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (sobO_add_le hψ hθ (theta_smul _ (hD _)) (theta_smul _ (hD _)) d).trans ?_
        rw [sobO_smul, sobO_smul, hre, hre, add_mul]
        gcongr <;> exact sobO_heisDer_le d _
    _ = _ := by
        simp_rw [← Finset.sum_mul]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm

end GlobalTheory.Size

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodRowsLevel

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_lev_of_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {x : GL (Fin (Yc D 0).rank) (EAf D)}
    (hx : x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      levFn (R.βY 0) (R.dat0 P) x = levFn (R.βY 0) (R.dat0 R.triv) x := by
  have h1 : rTup (R.βY 0) (R.dat0 R.triv) x = 1 := Subgroup.mem_bot.1 hx.2
  have h1' : rTup (R.βY 0) (R.dat0 P) x = 1 := h1
  refine ⟨⟨hx.1, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    rfl

theorem isMultMap_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {S : MMap (R.MY 0)}
    (h : IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S) :
    IsMultMap R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) S := by
  refine ⟨h.aut, h.cusp, ?_, h.equiv, h.cont⟩
  intro v k hk g
  have hk2 : k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)).comap (finE (Yc D 0)) := hk
  rw [Subgroup.mem_inf, Subgroup.mem_comap] at hk2
  have hm := mem_lev_of_triv R P hk2.2
  have hk' : k ∈ levS _ (R.βY 0) (R.dat0 P) :=
    (show k ∈ GfC (Yc D 0) ⊓ (Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) from
      Subgroup.mem_inf.2 ⟨hk2.1, Subgroup.mem_comap.2 hm.1⟩)
  rw [h.lev v k hk' g]
  simp only [levChi]
  rw [hm.2]

theorem eeat_le_triv (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv := by
  intro S hS
  rw [RealDat.EEat, goodPart, Submodule.mem_inf] at hS ⊢
  refine ⟨?_, hS.2⟩
  exact Submodule.span_mono (fun S' hS' => isMultMap_triv R P hS') hS.1

theorem eeat_sub_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM
  have h2 : ∀ P, R.EEat P ≤ LinearMap.range R.HE.e := fun P => by
    rw [hM.HE.2.1]; exact eeat_le_triv R P
  refine ⟨eeat_le_triv R, h2, ?_⟩
  intro P S hS S' hS'
  obtain ⟨x, rfl⟩ := h2 P hS
  obtain ⟨y, rfl⟩ := h2 P hS'
  rw [← hM.HE.2.2 x y]
  exact GlobalTheory.SchurPolar.isMultiplicityInner_inner (R.MY 0) R.ν0 R.fd0 R.HE _ hM.HE x y

end GlobalTheory.GoodRowsLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  first | exact @GlobalTheory.GoodRowsLevel.eeat_sub_principal | exact GlobalTheory.GoodRowsLevel.eeat_sub_principal | (intros; apply GlobalTheory.GoodRowsLevel.eeat_sub_principal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModel
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem finiteGroup_acts_unitarily_hilbertMultiplicityModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  intro D V S θ M β L J χ H _ _ e d μ 𝓕 hin hinj hmem hμ h𝓕 g0 u hact x
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hμ

  have hchoose : ∀ (P Q : ℂ → Prop) (hP : ∃ c, P c) (hQ : ∃ c, Q c), P = Q → hP.choose = hQ.choose := by
    rintro P Q hP hQ rfl; rfl
  have hip : ipM M μ 𝓕 (e (u x)) (e (u x)) = ipM M μ 𝓕 (e x) (e x) := by
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · obtain ⟨hcpt, hlift⟩ := GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts V β L
      have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
      have hκi : hk.choose⁻¹ ∈ levG V β (flagL L) := inv_mem hκ
      set a : ℂ := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
      have ha : ‖a‖ = 1 := by rw [ha_def, norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
      have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
      have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      have hU : ∀ v g, e (u x) v g = a * e x v (g * hk.choose) := by
        intro v g
        rw [hact x v]
        simp only [actG0, dif_pos hk, ha_def]
      have hV : ∀ v g, e x v g = a⁻¹ * e (u x) v (g * hk.choose⁻¹) := by
        intro v g
        rw [hU, mul_assoc g, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      have hm1 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
      have hm2 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκi
      have hiff : ∀ c, IsMultIP M μ 𝓕 (e (u x)) (e (u x)) c ↔ IsMultIP M μ 𝓕 (e x) (e x) c := by
        intro c
        constructor
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ hai hm2 _ (hmem (u x)) _ (hmem (u x)) _ _ hV hV c hc
        · intro hc
          exact GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation θ M J χ μ 𝓕 hμ h𝓕 _ _ ha hm1 _ (hmem x) _ (hmem x) _ _ hU hU c hc
      unfold ipM
      split_ifs with h1 h2 h2
      · exact hchoose _ _ h1 h2 (funext fun c => propext (hiff c))
      · exact absurd (let ⟨c, hc⟩ := h1; ⟨c, (hiff c).1 hc⟩) h2
      · exact absurd (let ⟨c, hc⟩ := h2; ⟨c, (hiff c).2 hc⟩) h1
      · rfl
    ·
      have h0 : e (u x) = 0 := by
        ext v g
        rw [hact x v]
        simp only [actG0, dif_neg hk]
        rfl
      have hux : u x = 0 := hinj (by rw [h0, map_zero])
      have hx : x = 0 := by
        have := congrArg u.symm hux
        simpa using this
      rw [hux, hx]
  have hsq' : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hin, hin, hip]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModelStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  first | exact @GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | exact GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel | (intros; apply GlobalTheory.finiteGroup_acts_unitarily_hilbertMultiplicityModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalFactorUnitary

variable {D : D7}

theorem actO_gAt_of_wAt_eq_zero (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : wAt p u = 0) : actO S T (gAt S p g) (gAt T p h) u = u := by
  obtain ⟨hsplit, hcomm⟩ := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g h u
  have hz : idem D p • actO S T g h u = 0 := by
    rw [← wAt_eq_smul, hcomm, hu]
    unfold actO
    simp
  have hrest : (1 - idem D p) • u = u := by
    rw [sub_smul, one_smul, ← wAt_eq_smul, hu, sub_zero]
  rw [hsplit, hz, hrest, zero_add]

theorem compAt_mt_gAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : Place D) (g : GA D V) (τ : D.what₂.Tau)
    (hτ : Sum.inr τ ≠ p) : compAt θ τ (Formalism.L2.Theta.mt V (gAt V p g)) = 1 := by
  have h0 : (θ τ) ((infPart D) (idem D p)) = 0 := by
    obtain ⟨-, -, -, hfin, -, -, hinf⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
    rcases p with v | τ'
    · rw [(hfin v).1, map_zero]
    · have hne : τ' ≠ τ := fun e => hτ (by subst e; rfl)
      exact (hinf θ hθ τ).2 τ' hne
  unfold compAt
  rw [((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1 V p g).1]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, h0, zero_mul, zero_add, sub_zero, one_mul]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLocal_om_gAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT hW hθ p f hf g h
  unfold IsLocal IsLatVac IsFockVacAt at hf ⊢
  obtain ⟨hth, ⟨hdbl, hhalf⟩, hfock⟩ := hf
  have hoff : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun v => Sum.inl v ≠ p), wAt p u = 0 := fun u hu =>
    (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 (fun _ hv => hv)
  refine ⟨hW.om_pres _ f hth, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have hw2 : wAt p (2 • u) = 0 := by
      rw [wAt_eq_smul, smul_comm, ← wAt_eq_smul, hoff u hu, smul_zero]
    have key := hW.om_heis (gAt S p g) (gAt T p h) (2 • u) f hth
    rw [hdbl u hu, actO_gAt_of_wAt_eq_zero S T p g h (2 • u) hw2] at key
    exact key.symm
  · intro e he u hu hu'
    have key := hW.om_heis (gAt S p g) (gAt T p h) u f hth
    rw [hhalf e he u hu hu', actO_gAt_of_wAt_eq_zero S T p g h u (hoff u hu)] at key
    exact key.symm
  · intro τ hτ z
    have hT1 : compAt θ τ (Formalism.L2.Theta.mt T (gAt T p h)) = 1 := compAt_mt_gAt hθ T p h τ hτ
    have hS1 : compAt θ τ (Formalism.L2.Theta.mt S (gAt S p g)⁻¹) = 1 := by
      rw [← gAt_inv]
      exact compAt_mt_gAt hθ S p g⁻¹ τ hτ
    have e1 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ z hth
    have e2 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ (cplxO (sS τ) (sT τ) z) hth
    rw [hT1, hS1, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have hz := hfock τ hτ z
    unfold annih at hz ⊢
    rw [← e1, ← e2, ← map_smul, ← map_add (f := _), hz, map_zero]

end GlobalTheory.LocalFactorUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  first | exact @GlobalTheory.LocalFactorUnitary.isLocal_om_gAt | exact GlobalTheory.LocalFactorUnitary.isLocal_om_gAt | (intros; apply GlobalTheory.LocalFactorUnitary.isLocal_om_gAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem phiQ_eq_viaRed_qLoc : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  intro D v φ PP r hr a b k mu ξ hmu Y
  classical
  unfold phiQ viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dite_eq_right hint, dite_eq_right (fun h => hint h.2.2.1)]
  rw [dite_eq_left hint]

  set Yo : Matrix (Fin b) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y i j, hint i j⟩ with hYo
  have hy : (Matrix.of fun i j => r ⟨Y i j, hint i j⟩) = Yo.map r := rfl
  have htopY : topL k Y = (topL k Yo).map (v.adicCompletionIntegers D.host.F).subtype := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp [Yo]
  have htopy : topL k (Yo.map r) = (topL k Yo).map r := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp
  set d := (topL k Yo).det with hd
  have hdetY : (topL k Y).det = (d : Fv D.host.F v) := by
    rw [htopY]; exact (RingHom.map_det (v.adicCompletionIntegers D.host.F).subtype _).symm
  have hdety : (topL k (Yo.map r)).det = r d := by
    rw [htopy]; exact (RingHom.map_det r _).symm
  have hle : Valued.v (d : Fv D.host.F v) ≤ 1 := d.2
  have hunit : IsUnit (r d) ↔ Valued.v (d : Fv D.host.F v) = 1 := by
    constructor
    · intro hu
      refine le_antisymm hle (not_lt.mp fun hlt => ?_)
      exact hu.ne_zero ((hr.2.1 d).mpr hlt)
    · intro h1
      have hne : (d : Fv D.host.F v) ≠ 0 := by
        intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
      have hinv : ((d : Fv D.host.F v))⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
        show Valued.v ((d : Fv D.host.F v))⁻¹ ≤ 1
        rw [map_inv₀, h1, inv_one]
      have hdu : IsUnit d := by
        refine ⟨⟨d, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;> ext <;> simp [hne]
      exact hdu.map r
  have hlow : LowZero k (Yo.map r) ↔ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
    unfold LowZero
    refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => ?_
    exact hr.2.1 (Yo i j)
  rw [hy]
  unfold qLoc
  by_cases hc : Valued.v (d : Fv D.host.F v) = 1 ∧ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1
  · have hA : IsUnit (topL k Y).det ∧ Valued.v (topL k Y).det = 1 ∧ (∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
      refine ⟨?_, by rw [hdetY]; exact hc.1, hint, hc.2⟩
      rw [hdetY, isUnit_iff_ne_zero]
      intro h0; have := hc.1; rw [h0, map_zero] at this; exact zero_ne_one this
    have hB : LowZero k (Yo.map r) ∧ IsUnit (topL k (Yo.map r)).det :=
      ⟨hlow.mpr hc.2, by rw [hdety]; exact hunit.mpr hc.1⟩
    rw [dite_eq_left hA, dite_eq_left hB]
    have hrel : RedRel φ PP ((hA.1.unit : Fv D.host.F v)) ((hB.2.unit : Formalism.L2.DIV.kP PP)) := by
      refine (hr.2.2.1 _ _).mpr ⟨by convert d.2 using 2; rw [IsUnit.unit_spec, hdetY], ?_⟩
      rw [IsUnit.unit_spec hB.2, hdety]
      congr 1
      apply Subtype.ext
      simp [IsUnit.unit_spec, hdetY]
    have hm := hmu _ _ hrel
    rw [hm, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · rw [dite_eq_right (fun h => hc ⟨by rw [← hdetY]; exact h.2.1, h.2.2.2⟩),
      dite_eq_right (fun h => hc ⟨hunit.mp (by rw [← hdety]; exact h.2), hlow.mp h.1⟩)]

end GlobalTheory.StepVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTwistDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  first | exact @GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | exact GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | (intros; apply GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc <;> assumption)
end
end
