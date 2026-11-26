module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ClozelConjCOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DifferentiableAtOm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SandMemCone
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}


variable (E a) in
def HV : Submodule ℝ (Lie E a) where
  carrier := {x | IsSelfAdjoint (Matrix.of x)}
  add_mem' h h' := IsSelfAdjoint.add h h'
  zero_mem' := IsSelfAdjoint.zero (Matrix (Fin a) (Fin a) (Cinf E))
  smul_mem' c x h := (Herm E a).smul_mem c (x := Matrix.of x) h

def hv : Herm E a ≃ₗ[ℝ] HV E a where
  toFun X := ⟨toL X.1, X.2⟩
  invFun x := ⟨Matrix.of x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl



variable (E a) in
def hOne : HV E a := hv ⟨1, IsSelfAdjoint.one _⟩

omit [NumberField E] in
theorem hOne_val : Matrix.of (hOne E a).1 = 1 := rfl

def sand : GL (Fin a) (Cinf E) →* (HV E a →L[ℝ] HV E a) where
  toFun g := LinearMap.toContinuousLinearMap
    { toFun := fun p => ⟨toL (g.val * Matrix.of p.1 * star g.val), IsSelfAdjoint.conjugate p.2 g.val⟩
      map_add' := fun p p' => Subtype.ext (by
        change g.val * (Matrix.of p.1 + Matrix.of p'.1) * star g.val =
          g.val * Matrix.of p.1 * star g.val + g.val * Matrix.of p'.1 * star g.val
        rw [mul_add, add_mul])
      map_smul' := fun c p => Subtype.ext (by
        change g.val * (c • Matrix.of p.1) * star g.val = c • (g.val * Matrix.of p.1 * star g.val)
        rw [mul_smul_comm, smul_mul_assoc]) }
  map_one' := ContinuousLinearMap.ext fun p => Subtype.ext (by
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of p.1 * star 1 = Matrix.of p.1
    simp)
  map_mul' g h := ContinuousLinearMap.ext fun p => Subtype.ext (by
    change (g.val * h.val) * Matrix.of p.1 * star (g.val * h.val) =
      g.val * (h.val * Matrix.of p.1 * star h.val) * star g.val
    simp only [star_mul, mul_assoc])

theorem sand_val (g : GL (Fin a) (Cinf E)) (p : HV E a) :
    Matrix.of (sand g p).1 = g.val * Matrix.of p.1 * star g.val := rfl


variable (E a) in
def cone : Set (HV E a) := {p | ∃ g : GL (Fin a) (Cinf E), sand g (hOne E a) = p}

theorem hOne_mem_cone : hOne E a ∈ cone E a := ⟨1, by rw [map_one]; rfl⟩

theorem sand_mem_cone (g : GL (Fin a) (Cinf E)) {p : HV E a} (hp : p ∈ cone E a) : sand g p ∈ cone E a := by
  obtain ⟨h, rfl⟩ := hp
  exact ⟨g * h, by rw [map_mul]; rfl⟩

variable [_root_.NumberField.IsTotallyComplex E]

def ev {d : ℕ} : Sm E a ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] (GA E a → Fin d → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ v g => φ.1 g • v) (fun φ ψ v => by ext g i; simp [add_mul])
    (fun c φ v => by ext g i; simp [mul_assoc]) (fun φ v w => by ext g i; simp [mul_add])
    (fun c φ v => by ext g i; simp [mul_left_comm]))

@[simp] theorem ev_tmul {d : ℕ} (φ : Sm E a) (v : Fin d → ℂ) (g : GA E a) : ev (φ ⊗ₜ[ℂ] v) g = φ.1 g • v := rfl

def geo (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) :
    Geo (⊤ : Subgroup (GL (Fin a) E)) (HV E a) (GL (Fin a) (Af E) ⧸ U) Ξ.d where
  ρ := sand.comp (((GeneralLinearGroup.map (pInf E)).comp (ratGL E a)).comp (Subgroup.subtype ⊤))
  σ := (MulAction.toPermHom (GL (Fin a) (Af E)) _).comp
    ((GeneralLinearGroup.map (algebraMap E (Af E))).comp (Subgroup.subtype ⊤))
  ξ := (ratC Ξ).comp (Subgroup.subtype ⊤)
  Y := cone E a
  isOpen := ho
  maps _ _ hp := sand_mem_cone _ hp

section

variable (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

theorem geo_ρ (γ : (⊤ : Subgroup (GL (Fin a) E))) :
    (geo ho U Ξ).ρ γ = sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)) := rfl

theorem geo_σ (γ : (⊤ : Subgroup (GL (Fin a) E))) (s : GL (Fin a) (Af E) ⧸ U) :
    (geo ho U Ξ).σ γ s = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • s := rfl

theorem geo_ξ (γ : (⊤ : Subgroup (GL (Fin a) E))) :
    (geo ho U Ξ).ξ γ = Ξ.mat (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)) := rfl

theorem geo_lev : (geo ho U Ξ).lev = levelRep ⊤ U (ratC Ξ) := by
  ext γ f s i
  rw [Geo.lev_apply, geo_σ]
  simp only [Subgroup.coe_inv, map_inv]
  rfl

def Corr {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)))
    (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (X : Fin q → Herm E a),
    w (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) (fun i => (2 : ℝ) • sand g (hv (X i))) =
      Ξ.mat g *ᵥ ev (ω X) (infGL E a g * finGL E a x)

end

def LeftInv {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ γ g, ev m (ratGL E a γ * g) = ev m g

def RightInv (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop :=
  ∀ u ∈ U, ∀ g, ev m (g * finGL E a u) = ev m g

end UpperTheory.V.Lit.Dr
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

def LocSec : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ p₀ ∈ cone E a, ∃ τ : HV E a → GL (Fin a) (Cinf E),
    ContDiffAt ℝ ∞ (fun p => toL (τ p).val) p₀ ∧ ∀ᶠ p in nhds p₀, sand (τ p) (hOne E a) = p

def ConePos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (p : HV E a), p ∈ cone E a ↔ ∀ w : InfinitePlace E, (Matrix.of fun i j => p.1 i j w).PosDef

def ConeConvex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), Convex ℝ (cone E a) ∧ IsCone (cone E a)

def BoundInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ K ⊆ cone E a, IsCompact K → ∃ C : ℝ, ∀ g : GL (Fin a) (Cinf E), ∀ p ∈ K, sand g p ∈ K → ‖toL g.val‖ ≤ C

def FinField : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : ℝ) (T : Set (Af E)), IsCompact T →
    {x : E | (∀ w : InfinitePlace E, w x ≤ C) ∧ algebraMap E (Af E) x ∈ T}.Finite

def GeoProper : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a), IsCompact (U : Set (GL (Fin a) (Af E))) → (geo ho U Ξ).Proper

def NormFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∃ f : GL (Fin a) (Af E) ⧸ U → ℝ, (∀ s, 0 < f s) ∧ ∀ (γ : GL (Fin a) E) (s : GL (Fin a) (Af E) ⧸ U),
      f (GeneralLinearGroup.map (algebraMap E (Af E)) γ • s) = |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)|⁻¹ * f s

def NormInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ δ : HV E a → ℝ, ContDiff ℝ ∞ δ ∧ (∀ p ∈ cone E a, 0 < δ p) ∧
    (∀ (t : ℝ) p, δ (t • p) = t ^ (a * Fintype.card (InfinitePlace E)) * δ p) ∧ ∀ (γ : GL (Fin a) E) p,
      δ (sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ)) p) = |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| * δ p

def Gauge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a), IsCompact (U : Set (GL (Fin a) (Af E))) → ∃ l, (geo ho U Ξ).IsInvGauge l

def EvFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (d : ℕ), Function.Injective (ev (E := E) (a := a) (d := d)) ∧
    (∀ (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d), (fun g => ev m g j) ∈ Sm E a) ∧
    ∀ f : GA E a → Fin d → ℂ, (∀ j, (fun g => f g j) ∈ Sm E a) → ∃ m : Sm E a ⊗[ℂ] (Fin d → ℂ), ev m = f

def LevelVal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))),
    (m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v} → LeftInv m ∧ RightInv U m) ∧
    (LeftInv m → RightInv U m → smLie Ξ (oneL E a) m = 0 → m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v})

def CentralOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (η : Herm E a [⋀^Fin q]→ₗ[ℝ] M),
    (∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → η X = 0) →
    (∀ (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)), (X i).1 = 1 → dCo L η X = 0) → ∀ X, L (oneL E a) (η X) = 0

def MatSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (Ξ : AlgRep E a) (i j : Fin Ξ.d), ContDiffOn ℝ ∞ (extGL fun y => Ξ.mat y i j) (invSet E a) ∧
    ContDiffOn ℝ ∞ (extGL fun y => Ξ.mat y⁻¹ i j) (invSet E a)

def CorrFwd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), IsCochain (smK Ξ) α → (∀ X, RightInv U (α X)) →
    ∃ w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ), Corr U Ξ α w ∧ ∀ s, ∀ p ∉ cone E a, w s p = 0

def CorrSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)), Corr U Ξ α w → ∀ s, ContDiffOn ℝ ∞ (w s) (cone E a)

def CorrBwd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (w : (geo ho U Ξ).Om q), ∃ α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Corr U Ξ α w.1

def CorrCochain : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)), Corr U Ξ α w →
    IsCochain (smK Ξ) α ∧ ∀ X, RightInv U (α X)

def CorrUniq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ),
    (∀ (α α' : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)), Corr U Ξ α w → Corr U Ξ α' w → α = α') ∧
    ∀ (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w w' : (geo ho U Ξ).Om q), Corr U Ξ α w.1 → Corr U Ξ α w'.1 → w = w'

def CorrInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (geo ho U Ξ).Om q), Corr U Ξ α w.1 →
    ((∀ X, LeftInv (α X)) ↔ ∀ γ, (geo ho U Ξ).act q γ w = w)

def CorrBasic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)), Corr U Ξ α w →
    ((∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → α X = 0) ↔ ∀ s, RadBasic (cone E a) (w s))

def EvDeriv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (m : (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E))
    (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a), c 0 = 1 → HasDerivAt (fun t => toL (c t).val) X 0 →
    HasDerivAt (fun t => Ξ.mat (g * c t) *ᵥ ev m (infGL E a (g * c t) * finGL E a x))
      (Ξ.mat g *ᵥ ev (smLie Ξ X m) (infGL E a g * finGL E a x)) 0

def CorrD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (geo ho U Ξ).Om q), Corr U Ξ α w.1 →
    Corr U Ξ (dCo (smLie Ξ) α) ((geo ho U Ξ).dOm q w).1

def EvK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (k : Kinf E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a),
    ev (smK Ξ k m) g = Ξ.mat (Unitary.toUnits k) *ᵥ ev m (g * infGL E a (Unitary.toUnits k))

def BwdSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (w : (geo ho U Ξ).Om q) (X : Fin q → Herm E a) (j : Fin Ξ.d),
    (fun g : GA E a => (Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ
      w.1 (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U) (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a))
        fun i => (2 : ℝ) • sand (GeneralLinearGroup.map (pInf E) g) (hv (X i))) j) ∈ Sm E a

end UpperTheory.V.Lit.Dr
