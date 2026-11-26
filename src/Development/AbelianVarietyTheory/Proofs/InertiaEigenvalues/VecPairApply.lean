module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

section General

def rect {Λ B : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] {r a : ℕ} (Z : Matrix (Fin r) (Fin a) Λ) (x : Fin a → B) :
    Fin r → B := fun c => ∑ j, Z c j • x j

abbrev what₂ {Λ μ ν : Type} [CommRing Λ] (Z : μ → ν → Λ) : Submodule Λ (ν → Λ) := Submodule.span Λ (Set.range Z)

def Cob {Γ Λ M : Type} [Group Γ] [CommRing Λ] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ Γ M) (f : Γ → M) : Prop :=
  ∃ m, ∀ g, f g = ρ g m - m

variable (Λ : Type) [CommRing Λ] {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [AddCommGroup Y'] [Module Λ Y'] {n : ℕ}

def Bal (β : Y →+ Y' →+ ZMod n) : Prop := ∀ (a : Λ) y y', β (a • y) y' = β y (a • y')

def Perf (β : Y →+ Y' →+ ZMod n) : Prop :=
  Bal Λ β ∧ (∀ y, (∀ y', β y y' = 0) → y = 0) ∧ ∀ y', (∀ y, β y y' = 0) → y' = 0

def vecPair (r : ℕ) (β : Y →+ Y' →+ ZMod n) : (Fin r → Y) →+ (Fin r → Y') →+ ZMod n :=
  ∑ c : Fin r, ((β.comp (Pi.evalAddMonoidHom (fun _ => Y) c)).flip.comp (Pi.evalAddMonoidHom (fun _ => Y') c)).flip

theorem vecPair_apply (r : ℕ) (β : Y →+ Y' →+ ZMod n) (x : Fin r → Y) (y : Fin r → Y') :
    vecPair r β x y = ∑ c, β (x c) (y c) := by
  simp [vecPair]

def CupB {Γ M M' : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [AddCommGroup M'] (χ : Γ → ZMod n)
    (act : Γ → M' → M') (P : M →+ M' →+ ZMod n) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → ZMod n, IsLocallyConstant f ∧ ∀ g h, P (x g) (act g (y h)) = χ g * f h - f (g * h) + f g

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def Kills (A : Type) [CommRing A] [Algebra (X.O0 i) A] : Prop := ∀ x ∈ idl i, algebraMap (X.O0 i) A x = 0

section Coef

variable {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)

def SelC (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] (Q : Finset (PlE D.host))
    (f : GE N → Fin D.R.r → Y) : Prop :=
  ∃ z : Z1 (repOn (Tgl i s) κ Y), z.1 = f ∧ Submodule.Quotient.mk z ∈ selOn bkP i (Tgl i s) κ Y Q

def Univ (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (Z : GE N → Matrix (Fin D.R.r) (Fin a) Λ) : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y],
    (∀ x : Fin a → Y, matAct Φ x = 0 → SelC bkP i s κ Y Q fun g => rect (Z g) x) ∧
    (∀ x : Fin a → Y, matAct Φ x = 0 → Cob (repOn (Tgl i s) κ Y) (fun g => rect (Z g) x) → x = 0) ∧
    ∀ f, SelC bkP i s κ Y Q f → ∃ x : Fin a → Y, matAct Φ x = 0 ∧
      Cob (repOn (Tgl i s) κ Y) fun g => f g - rect (Z g) x

variable (ρ : GE N →* GL (Fin D.R.r) (X.O0 i))

section Dual

variable {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1)))
  (Q : Finset (PlE D.host))

def DualSel (y : Z1 (repOn ρ κ⁻¹ Y')) : Prop :=
  (∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 v), y.1 τ = 0) ∧
  (∀ v, v ∈ Spl i ∨ v ∈ Q → ∃ m, ∀ g ∈ DecV N v, y.1 g = repOn ρ κ⁻¹ Y' g m - m) ∧
  ∀ v ∈ placesOver D.host.E (X.l i), ∀ x : Z1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype),
    Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) κ Y v →
    CupB (fun g : DecV N v => ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g.1 : (ZMod (X.l i ^ (nu X i + 1)))ˣ) :
        ZMod (X.l i ^ (nu X i + 1))))
      (fun g m => repOn ρ κ⁻¹ Y' g.1 m) (vecPair D.R.r β) x.1 (fun g => y.1 g.1)

def DualCl : Set (H1 (repOn ρ κ⁻¹ Y')) := {c | ∃ y, DualSel bkP i s κ ρ β Q y ∧ c = Submodule.Quotient.mk y}

end Dual

def OrderFormula (Q : Finset (PlE D.host)) : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] [Finite Y']
    (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Perf Λ β →
    Finite (DualCl bkP i s κ ρ β Q) ∧ Nat.card (selOn bkP i (Tgl i s) κ Y Q) =
      Nat.card (DualCl bkP i s κ ρ β Q) * ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype))

def NoInvDual : Prop := ∀ (Y' : Type) [AddCommGroup Y'] [Module Λ Y'] (m : Fin D.R.r → Y'),
  (∀ g, repOn ρ κ⁻¹ Y' g m = m) → m = 0

def LocCountFin : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y],
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ Y v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype))) *
        Nat.card Y ^ (D.R.f * D.R.r)


omit [Algebra (X.O0 i) Λ] in
def IsChar {M : ℕ} {ι : Type} [Fintype ι] (ξ : ι → Λ) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ g, ((κ g : Λˣ) : Λ) * ∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d q g)).val = 1

def bform (x y : GE N → Fin D.R.r → Λ) (h : GE N) : Λ := x h ⬝ᵥ y h - x (cConj X h) ⬝ᵥ y (cConj X h)

end Coef

def NewPl (M : ℕ) (L : Subgroup (GE N)) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N) : Prop :=
  (∀ v, Over p v → v ∉ X.S0 i) ∧ IsSplitPl D.host p ∧ normV p % (2 * X.l i ^ M) = 1 ∧ DecV N p ≤ L ∧
    IsOpen (d.ker : Set (GE N)) ∧ IsFrob (N.plOm.1 p) (normV p) σ ∧ γ ∈ Ine (F := D.host.E) (N.plOm.1 p) ∧
    d γ = Multiplicative.ofAdd 1


variable (X) in
def two (g : GE N) : Bool → GE N := fun b => if b then cConj X g else g

end GlobalTheory.NewPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.ExactMult

theorem finrank_add_of_exact {L A₀ A₁ A₂ : Type} [Field L] [AddCommGroup A₀] [Module L A₀]
    [AddCommGroup A₁] [Module L A₁] [AddCommGroup A₂] [Module L A₂] (i : A₀ →ₗ[L] A₁) (p : A₁ →ₗ[L] A₂)
    (hi : Function.Injective i) (hk : LinearMap.range i = LinearMap.ker p)
    (S₀ : Submodule L A₀) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂) [FiniteDimensional L S₁]
    (h0 : S₀ = S₁.comap i) (h2 : S₁.map p = S₂) :
    finrank L S₁ = finrank L S₀ + finrank L S₂ := by
  have e := LinearMap.finrank_range_add_finrank_ker (p.domRestrict S₁)
  rw [LinearMap.range_domRestrict, h2, LinearMap.ker_domRestrict, ← hk] at e
  have e1 : finrank L ((LinearMap.range i).comap S₁.subtype) = finrank L S₀ := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, h0,
      (Submodule.equivMapOfInjective i hi (S₁.comap i)).finrank_eq, Submodule.map_comap_eq, inf_comm]
  omega

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem mem_fil (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g x = x) ∧
      ∀ c : K, mulVdR (LL := LL) (V := V) c x = τ c • x) ∧ x ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]

theorem map_mul (f : V →ₗ[LL] V') (c : K) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V') c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g x) =
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, he]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem act_mul (ρ : Representation LL G V) (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem mul_mem_filV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (LL := LL) (V := V) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR, Algebra.smul_def]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz

noncomputable def ev (x : V ⊗[Qp] BdR) : LL ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun (c : LL) (k : K) => c • mulVdR (LL := LL) (V := V) k x)
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun c k k' => by
      rw [← smul_add]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR, add_mul, tmul_add]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel)
    (fun q c k => by
      rw [smul_comm q c]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : algebraMap K BdR (q • k) * b = q • (algebraMap K BdR k * b) := by
          rw [← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]
        simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, this,
          tmul_smul]
      | add y z hy hz => simp only [map_add (f := _), hy, hz, smul_add]))

theorem ev_tmul (x : V ⊗[Qp] BdR) (c : LL) (k : K) :
    ev (LL := LL) (K := K) x (c ⊗ₜ k) = c • mulVdR (LL := LL) (V := V) k x := rfl

theorem mul_mul (y k : K) (x : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) (V := V) (y * k) x = mulVdR (LL := LL) (V := V) y (mulVdR (LL := LL) (V := V) k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_fildR_eq [CharZero Qp] (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (f : V →ₗ[LL] V') (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hs : ∀ y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a,
      ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a,
        AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = y) :
    (FildR PD ρ τ a).map (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FildR PD ρ' τ a := by
  haveI := PD.finK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_fil PD ρ τ a x).1 hx
    refine (mem_fil PD ρ' τ a _).2 ⟨⟨fun g => ?_, fun c => ?_⟩, GlobalTheory.HTW.map_mem_FilV PD f a x h3⟩
    · rw [← map_act PD ρ ρ' f he, h1]
    · rw [← map_mul, h2, map_smul]
  · intro y hy
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hs y ⟨hy.1.1, hy.2⟩
    obtain ⟨⟨-, h2⟩, -⟩ := (mem_fil PD ρ' τ a _).1 hy
    have h1 : ∀ g, actVdR PD ρ g x = x := by
      simpa only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hx1
    obtain ⟨m, c, k, hc, hk⟩ := GlobalTheory.exists_embedding_idempotent_tensor Qp K LL τ
    refine ⟨∑ j, c j • mulVdR (LL := LL) (V := V) (k j) x,
      (mem_fil PD ρ τ a _).2 ⟨⟨fun g => ?_, fun y => ?_⟩, ?_⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_smul, act_mul, h1]
    · have := congrArg (ev (LL := LL) (K := K) x) (hk y)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, ev_tmul, mul_mul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, this, Finset.smul_sum, mul_smul]
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_filV PD a _ x hx2)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_smul, map_mul, h2, ← mul_smul, ← Finset.sum_smul, hc, one_smul]

variable {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]

theorem tensor_exact (ι : V₀ →ₗ[LL] V) (π : V →ₗ[LL] V') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hk : LinearMap.range ι = LinearMap.ker π) :
    Function.Injective (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) ∧
      LinearMap.range (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) =
        LinearMap.ker (AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  have e1 : ∀ x, AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (ι.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have e2 : ∀ x, AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (π.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hex : Function.Exact (ι.restrictScalars Qp) (π.restrictScalars Qp) :=
    (LinearMap.exact_iff.2 hk.symm : Function.Exact ι π)
  constructor
  · intro x y h
    rw [e1, e1] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := BdR) (ι.restrictScalars Qp) hι h
  · ext x
    have := rTensor_exact BdR hex hπ x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, e1, e2]
    exact this.symm

end General

theorem exact_hodge_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  intro l _ P AI T K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hi hs hk hd
  obtain ⟨d2, hst⟩ := (GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hd
  obtain ⟨t1, t2⟩ := tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι π hi hs hk
  have hf : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) =
      finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) := by
    intro τ a
    haveI := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a).1
    exact finrank_add_of_exact _ _ t1 t2 _ _ _ (GlobalTheory.HTW.FildR_eq_comap (P.PD K) ρ₀ ρ₁ ι hi hι τ a)
      (map_fildR_eq (P.PD K) ρ₁ ρ₂ π hπ τ a (hst a))
  refine ⟨(GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hi hd, d2, fun τ a => ?_⟩
  have hm : multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a := by
    unfold multV
    rw [hf τ a, hf τ (a + 1)]
    push_cast
    ring
  refine ⟨hf τ a, hm, ?_⟩
  obtain ⟨-, n0, j0⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₀ ρ₀ τ a
  obtain ⟨-, -, j1⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a
  obtain ⟨-, n2, j2⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₂ ρ₂ τ a
  rw [j0, j1, j2, hm]
  omega

end GlobalTheory.Per.ExactMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparisonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_representation_tensor_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  first | exact @GlobalTheory.Per.ExactMult.exact_hodge_add | exact GlobalTheory.Per.ExactMult.exact_hodge_add | (intros; apply GlobalTheory.Per.ExactMult.exact_hodge_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.ZSumOne

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

theorem zOf_coeff (χ : G → ℂ) (y : G) : (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem irr_one_eq_finrank {χ : G → ℂ} {V : FDRep ℂ G} (hV : ∀ x, V.character x = χ x) :
    χ 1 = (Module.finrank ℂ V : ℂ) := by
  rw [← hV 1, FDRep.char_one]

theorem zOf_eq_zIdem (χ : G → ℂ) (V : FDRep ℂ G) (hV : ∀ x, V.character x = χ x) :
    zOf χ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem V := by
  have h1 := irr_one_eq_finrank hV
  unfold zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, ← hV x⁻¹]
  rfl

theorem zOf_injOn : Set.InjOn (zOf (G := G)) {χ | IsIrr χ} := by
  intro χ hχ χ' hχ' h
  obtain ⟨V, hs, hV⟩ := hχ
  obtain ⟨V', hs', hV'⟩ := hχ'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := irr_one_eq_finrank hV
  have h1' := irr_one_eq_finrank hV'
  have e1 := congrArg (fun a => a.coeff 1) h
  simp only [zOf_coeff, inv_one] at e1
  rw [h1, h1'] at e1
  have e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) =
      ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ) := by
    push_cast
    field_simp at e1
    linear_combination e1
  have hn : Module.finrank ℂ V = Module.finrank ℂ V' := Nat.mul_self_inj.mp (by exact_mod_cast e2)
  have h11 : χ 1 = χ' 1 := by rw [h1, h1', hn]
  haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs
  have hpos : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hk : χ 1 / (Fintype.card G : ℂ) ≠ 0 := div_ne_zero (h1 ▸ hpos) hc
  funext y
  have e3 := congrArg (fun a => a.coeff y⁻¹) h
  simp only [zOf_coeff, inv_inv] at e3
  rw [← h11] at e3
  exact mul_left_cancel₀ hk e3

theorem zOf_image :
    zOf '' {χ : G → ℂ | IsIrr χ} =
      {z : MonoidAlgebra ℂ G | ∃ τ : FDRep ℂ G, Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z} := by
  ext z
  constructor
  · rintro ⟨χ, ⟨V, hs, hV⟩, rfl⟩
    exact ⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩
  · rintro ⟨τ, hs, rfl⟩
    exact ⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩

end GlobalTheory.GLq.ZSumOne

namespace GlobalTheory.GLq

theorem irr_finite_and_finsum_zOf_eq_one : ∀ (G : Type) [Group G] [Fintype G],
    {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  intro G _ _
  have hZ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G
  rw [← ZSumOne.zOf_image] at hZ
  refine ⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩
  have himg := finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))
  rw [← himg]
  exact hZ.2

end GlobalTheory.GLq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one : ∀ (G : Type) [Group G] [Fintype G] , {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  first | exact @GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | exact GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | (intros; apply GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DdREqDcris

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_mulVB (c : K₀) (d : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem act_mulVB (g : G) (c : K₀) (d : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVB, mulVB]

theorem mulVB_mem (c : K₀) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d ∈ Dcris PD ρ := by
  rw [CrisDR.mem_Dcris_iff] at hd ⊢
  intro g
  rw [act_mulVB, hd g]

theorem mulVdR_one (y : V ⊗[Qp] BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro d hd
  refine CrisDR.eq_zero_of_sum PD (LL := LL) (m := 1) (fun _ => (1 : K)) ?_ (fun _ => d) ?_ 0
  · intro b hb i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    apply PD.ι_inj
    simpa using hb
  · simp [hd]

theorem map_Dcris_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i))) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have := CrisDR.mul_ι_mem PD ρ (1 : K) hd
    rwa [mulVdR_one] at this
  · intro y hy
    obtain ⟨m, c, d, hd, rfl⟩ := h y hy
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c₀, hc₀⟩ := hb (c i)
    rw [← hc₀, ← ιV_mulVB]
    exact Submodule.mem_map_of_mem (mulVB_mem PD ρ c₀ (hd i))

theorem FildR_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
      (ιV PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · rintro y ⟨⟨hy, hτ⟩, hF⟩
    rw [← h] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    refine Submodule.mem_map_of_mem ⟨⟨hd, hF⟩, hd, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    apply ιV_injective PD (LL := LL)
    rw [ιV_mulVB, hτ, map_smul]
    rfl
  · rintro _ ⟨d, ⟨⟨hd, hF⟩, -, hτ⟩, rfl⟩
    refine ⟨⟨h ▸ Submodule.mem_map_of_mem hd, ?_⟩, hF⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    obtain ⟨c₀, rfl⟩ := hb c
    rw [← ιV_mulVB, hτ, map_smul]
    rfl

end Abstract

theorem map_Dcris_eq_DdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  intro l _ P AI T K LL hb V _ _ _ _ _ ρ hc
  obtain ⟨hdr, hspan⟩ := CrisDR.isDR_of_isCrys l P AI T K LL V ρ hc
  have h := map_Dcris_eq (P.PD K) ρ hb.2 hspan
  refine ⟨h, fun τ => ?_⟩
  obtain ⟨h1, -, h2⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL V ρ).1 τ
  exact ⟨h1, h2 hdr, FildR_eq (P.PD K) ρ hb.2 h τ⟩

end GlobalTheory.Per.DdREqDcris
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_Dcris_eq_DdR_crystalline_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  first | exact @GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | (intros; apply GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfEPow

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (x : Ainf l) : Per.θ l x = 0 ↔ bk.ev bk.E ∣ x := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem theta_of_natPow_mul (n : ℕ) (c : Ainf l) (h : Per.θ l ((l : Ainf l) ^ n * c) = 0) :
    Per.θ l c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : Per.OC l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hne

theorem dvd_of_dvd_natPow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  exact theta_of_natPow_mul n c h

theorem pow_dvd_of_pow_dvd_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_natPow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_pow_dvd_lpow_mul (m k : ℕ) (a : Ainf l)
    (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply pow_dvd_of_pow_dvd_l_mul bk m
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem pow_dvd_of_ev_pow_dvd (m : ℕ) : ∀ s : bk.S,
    bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    have h1 : bk.ev bk.E ∣ bk.ev s := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    have hE : bk.E ∣ s := by
      set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr
      have hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r := by
        rw [hr, RingEquiv.apply_symm_apply]
      have hθ := bk.θ_ev r s hmk
      rw [(theta_eq_zero_iff bk _).mpr h1] at hθ
      have hr0 : r = 0 := intToOC_injective K (by rw [← hθ, map_zero])
      rw [hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
      exact hmk
    obtain ⟨s', rfl⟩ := hE
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', map_mul] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem theta_eq_zero_of_forall (y : Per.OC l) (h : ∀ n : ℕ, ∃ z : Per.OC l, y = (l : Per.OC l) ^ n * z) :
    y = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem pow_dvd_of_forall_approx (m : ℕ) : ∀ a : Ainf l,
    (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) →
      bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have hθ : Per.θ l a = 0 := by
      apply theta_eq_zero_of_forall
      intro n
      obtain ⟨b, c, hbc⟩ := h n
      refine ⟨Per.θ l c, ?_⟩
      have hE : Per.θ l (bk.ev bk.E) = 0 := (theta_eq_zero_iff bk _).mpr dvd_rfl
      rw [hbc, map_add (f := _), map_mul, map_mul, map_pow, map_pow, hE, map_natCast]
      simp
    obtain ⟨a', rfl⟩ := (theta_eq_zero_iff bk a).mp hθ
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro n
    obtain ⟨b, c, hbc⟩ := h n
    have hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c :=
      ⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩
    obtain ⟨c', rfl⟩ := dvd_of_dvd_natPow_mul bk n c hc
    refine ⟨b, c', ?_⟩
    apply mul_left_cancel₀ (evE_ne_zero bk)
    rw [hbc]; ring

theorem ker_localizedTheta_eq_span_eisenstein (bk : BK K) : Per.kerP l = Ideal.span {(algebraMap (Per.Ainf l) (Per.AinfP l)) (bk.ev bk.E)} :=
  GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)

theorem mem_filtration_iff_eisenstein_pow_dvd (m : ℕ) (a : Ainf l) :
    aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a := by
  have key : aDp l a ∈ Per.FilP l m ↔
      (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    unfold aDp
    rw [RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
  constructor
  · rintro ⟨y, hy⟩
    haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) :=
      inferInstance
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y
    obtain ⟨k, hk⟩ := s.2
    simp only at hs hk
    rw [← hk] at hs
    have hl0 : (l : Per.Ainf l) ≠ 0 := fun h => by
      have h' := congrArg (Per.θ l) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hl.out.ne_zero) h'
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
    have heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b := by
      apply hinj
      rw [map_mul, map_mul, ← hs, hy]
      ring
    exact pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩
  · exact fun h => map_dvd _ h

theorem ePow_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  intro l _ K bk m
  exact ⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m,
    pow_dvd_of_forall_approx bk m⟩

end GlobalTheory.AinfEPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  first | exact @GlobalTheory.AinfEPow.ePow_facts | exact GlobalTheory.AinfEPow.ePow_facts | (intros; apply GlobalTheory.AinfEPow.ePow_facts; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BcrisInv

theorem map_smul_matrix {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (a : R)
    (M : Matrix (Fin d) (Fin d) R) : (a • M).map f = f a • M.map f := by
  ext i j; simp

theorem invariant_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  intro l _ K bk τ hτ N d k ρ Y Y' ε Q Q' hYY hgal hQQ hε
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf
  set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg
  obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
  have hne : e ≠ 1 := by
    rintro rfl; apply he2; simp
  have hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1)) :=
    GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
  have hw : IsUnit (f τ) := by
    have : f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  obtain ⟨W, hW⟩ := hw.pow N

  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ?_, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)

    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG

    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    have e2 : (⇑alg ∘ fun a => (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) = ⇑f := by
      funext a; simp only [Function.comp_apply, hFφ, hf, halg, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
    rw [e2] at hE

    have eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) =
        (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]

end GlobalTheory.BcrisInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrameStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U := by
  first | (exact @GlobalTheory.BcrisInv.invariant_unit) | (exact GlobalTheory.BcrisInv.invariant_unit) | (intros; apply GlobalTheory.BcrisInv.invariant_unit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineTied

theorem fontCore_all_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) :=
  fun l _ P AI hT K => GlobalTheory.Per.FontaineAll.fontCore_of_tied l P AI hT K

end GlobalTheory.Per.FontaineTied
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  first | exact @GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | exact GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | (intros; apply GlobalTheory.Per.FontaineTied.fontCore_all_of_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.HerrFull

theorem herr_part_a_every_record :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
      Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F :=
  fun D HW F => herr_a_and_natural D HW F

end GlobalTheory.HerrFull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.HerrComplexH1

theorem herr_H1_description : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2a D HW F := by
  intro D HW F l _ K s LL h T _
  have H := GlobalTheory.HerrFull.herr_a_and_natural D HW F l K s LL h
  refine ⟨H.2.1 T, fun _ hp => ?_⟩
  have H1 := H.1 (fun e => absurd e hp) T
  exact ⟨H1.1, H1.2.1⟩

end GlobalTheory.NL.HerrComplexH1
end
