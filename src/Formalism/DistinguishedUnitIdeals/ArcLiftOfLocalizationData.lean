module

public import Formalism.DistinguishedUnitIdeals.CoprimeProd

@[expose] public section

section -- merged from Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData
noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

section
variable {O : Type} [CommRing O]

def polyAct {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] (P : Polynomial O)
    (γ : V →+ V) (w : V) : V :=
  P.sum fun k a => C a • (⇑γ)^[k] w

def extL {r₁ r₂ : ℕ} (f : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) :
    (Fin r₁ → PowerSeries O) →ₗ[PowerSeries O] (Fin r₂ → PowerSeries O) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (fun a : O => (C a : PowerSeries O)))

def InSum {E : Type} [AddCommGroup E] [Module (PowerSeries O) E] (D : AddSubgroup E)
    (S : Submodule (PowerSeries O) E) (e : E) : Prop :=
  ∃ d ∈ D, e - d ∈ S

def Base.Th (B : Base O) (ell g : ℕ) : PowerSeries O := ∏ s ∈ Finset.range ell, B.p s ^ g

def Base.GamX (B : Base O) : Prop := B.γ X ∈ Ideal.span {(X : PowerSeries O)}

end

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.W (L : Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) :
    Submodule (PowerSeries O) V :=
  dv Λ (L.pull (c - (ell : ZMod n)) ell)

def Lat.GamN (L : Lat B n V) (c : ZMod n) : Prop :=
  ∀ v ∈ L.N c, L.γ c v - v ∈ sm X (L.N c)

def Lat.GammaCongruentArc (L : Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) : Prop :=
  ∀ w ∈ L.W c ell Λ, L.γ c w - w ∈ sm X (L.W c ell Λ)

structure LevelData (L : Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ) where
  Lv : Type
  [acg : AddCommGroup Lv]
  [mod : Module (PowerSeries O) Lv]
  gE : ℕ → Lv →+ Lv
  gE_semi : ∀ s (a : PowerSeries O) (e : Lv), gE s (a • e) = B.γ a • gE s e
  loc : ℕ → ↥(L.W c ell Λ) →ₗ[PowerSeries O] Lv
  locL : ℕ → (Fin r → PowerSeries O) →ₗ[PowerSeries O] Lv
  Nl : ℕ → Submodule (PowerSeries O) Lv
  Nb : ℕ → Submodule (PowerSeries O) Lv
  Fl : ℕ → Submodule (PowerSeries O) Lv
  Dc : ℕ → AddSubgroup Lv

attribute [instance] LevelData.acg LevelData.mod

variable {L : Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}

def LevelData.Equiv (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, ∀ (w : V) (hw : w ∈ L.W c ell Λ) (hγ : L.γ c w ∈ L.W c ell Λ),
    S.loc s ⟨L.γ c w, hγ⟩ = S.gE s (S.loc s ⟨w, hw⟩)

def LevelData.K2iii (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, ∀ w : ↥(L.W c ell Λ), S.gE s (S.loc s w) - S.loc s w ∈ S.Nl s →
    InSum (S.Dc s) (S.Nl s) (S.loc s w)

def LevelData.RD (S : LevelData L c ell Λ r) (g : ℕ) : Prop :=
  ∀ s < ell, S.Nb s ≤ dv (B.p s ^ g) (S.Nl s) ∧ S.Nl s ≤ dv (B.p s ^ g) (S.Nb s)

def LevelData.K3a2 (S : LevelData L c ell Λ r) (g : ℕ) (PP : Polynomial O) : Prop :=
  ∀ s < ell, ∀ e : S.Lv, InSum (S.Dc s) (dv (B.p s ^ g) (S.Nb s)) e →
    InSum (S.Dc s) (S.Nb s) (polyAct PP (S.gE s) e)

def LevelData.K3a4 (S : LevelData L c ell Λ r) (g : ℕ) (PP' : Polynomial O) : Prop :=
  ∀ s < ell, ∀ e : S.Lv, InSum (S.Dc s) (dv (B.p s ^ g) (S.Nl s)) e →
    InSum (S.Dc s) (S.Nl s) (polyAct PP' (S.gE s) e)

def LevelData.DcFix (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, (∀ d ∈ S.Dc s, S.gE s d = d) ∧ (∀ e ∈ S.Nl s, S.gE s e ∈ S.Nl s)

def LevelData.Partner (S : LevelData L c ell Λ r) (sig : ℕ) : Prop :=
  (∀ w : ↥(L.W c ell Λ), ∃ y : Fin r → PowerSeries O, ∀ s < ell,
    S.locL s y - B.lc ^ sig • S.loc s w ∈ S.Fl s) ∧
  (∀ y : Fin r → PowerSeries O, ∃ w : ↥(L.W c ell Λ), ∀ s < ell,
    S.loc s w - B.lc ^ sig • S.locL s y ∈ S.Fl s)

def LevelData.P3 (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, S.Fl s ≤ S.Nl s ∧ S.Fl s ≤ S.Nb s

def LevelData.DivisibleIff (S : LevelData L c ell Λ r) (g : ℕ) : Prop :=
  dv (B.Th ell g) (L.N c) ≤ L.W c ell Λ ∧
  ∀ x : ↥(L.W c ell Λ), (x : V) ∈ dv (B.Th ell g) (L.N c) ↔
    ∀ s < ell, S.loc s x ∈ dv (B.p s ^ g) (S.Nl s)

def LevelData.XMulIff (S : LevelData L c ell Λ r) : Prop :=
  ∀ x : ↥(L.W c ell Λ), (x : V) ∈ sm X (L.N c) ↔
    ((x : V) ∈ sm X (L.W c ell Λ) ∧ ∀ s < ell, S.loc s x ∈ S.Nl s)

def LevelData.Bridge (S : LevelData L c ell Λ r) (ϖ : O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U : ℕ → Submodule O (Fin r → O)) : Prop :=
  (∀ y : Fin r → PowerSeries O, (∀ s < ell, S.locL s y ∈ S.Nb s) ↔ NN ϖ B.p H b kind U ell y) ∧
  (∀ y : Fin r → PowerSeries O, (∀ s < ell, InSum (S.Dc s) (S.Nb s) (S.locL s y)) ↔
    II ϖ B.p H b kind U ell y)

end

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

structure LevelMap (h : LatHom L₁ L₂) {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r₁ r₂ : ℕ}
    (S₁ : LevelData L₁ c ell Λ r₁) (S₂ : LevelData L₂ c ell Λ r₂) where
  prE : S₁.Lv →ₗ[PowerSeries O] S₂.Lv
  prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)
  loc_comm : ∀ s < ell, ∀ (w : V₁) (hw : w ∈ L₁.W c ell Λ) (hw' : h.f w ∈ L₂.W c ell Λ),
    prE (S₁.loc s ⟨w, hw⟩) = S₂.loc s ⟨h.f w, hw'⟩
  locL_comm : ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
    prE (S₁.locL s y) = S₂.locL s (extL prL y)

def LevelMap.MapFl {h : LatHom L₁ L₂} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r₁ r₂ : ℕ}
    {S₁ : LevelData L₁ c ell Λ r₁} {S₂ : LevelData L₂ c ell Λ r₂} (m : LevelMap h S₁ S₂) : Prop :=
  ∀ s < ell, ∀ e ∈ S₁.Fl s, m.prE e ∈ S₂.Fl s

def LatHom.LiftsDivisible (h : LatHom L₁ L₂) (c : ZMod n) (ell g rr : ℕ) : Prop :=
  ∀ x ∈ dv (B.Th ell g) (L₂.N c), ∃ x₁ ∈ dv (B.Th ell g) (L₁.N c), h.f x₁ = B.lc ^ rr • x

end

def ConstLift {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ϖ : O) (ℓ : ℕ) (p : ℕ → PowerSeries O)
    (H b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (ell a₀ : ℕ)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  ∀ y : Fin r₂ → PowerSeries O, II ϖ p H b kind U₂ ell y →
    ∃ (y₁ : Fin r₁ → PowerSeries O) (ν : Fin r₂ → PowerSeries O),
      II ϖ p H b kind U₁ ell y₁ ∧ NN ϖ p H b kind U₂ ell ν ∧
      C ((ℓ : O) ^ (2 * a₀)) • y = extL prL y₁ + C ((ℓ : O) ^ (2 * a₀)) • ν

def PPval {O : Type} [CommRing O] (ℓ kap : ℕ) (PP PP' : Polynomial O) : Prop :=
  ∃ (k : ℕ) (ε : Oˣ), k ≤ 2 * kap ∧ PP.eval 1 * PP'.eval 1 = (ε : O) * (ℓ : O) ^ k

def ArcLiftOfLocalizationData : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (Cu : Cuts n)
    (abelian₂ : ZMod n → PowerSeries O) (g sig rr a₀ kap : ℕ)
    (V₁ V₂ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (h : LatHom L₁ L₂)
    (c : ZMod n) (r₁ r₂ : ℕ)
    (S₁ : LevelData L₁ c (Cu.ell c) (abelian₂ c) r₁) (S₂ : LevelData L₂ c (Cu.ell c) (abelian₂ c) r₂)
    (m : LevelMap h S₁ S₂) (ϖ : O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
    (PP PP' : Polynomial O),
    abelian₂ c = Formalism.ExponentWindows.abelian₂ B.p H (Cu.ell c) →
    B.GamX → L₂.GamN c →
    L₁.GammaCongruentArc c (Cu.ell c) (abelian₂ c) → L₂.GammaCongruentArc c (Cu.ell c) (abelian₂ c) →
    S₁.Equiv → S₂.Equiv → S₂.K2iii → S₁.RD g → S₂.RD g → S₂.K3a2 g PP → S₁.K3a4 g PP' →
    S₁.DcFix → S₁.Partner sig → S₂.Partner sig → S₁.P3 → S₂.P3 →
    S₁.DivisibleIff g → S₂.DivisibleIff g → S₁.XMulIff → S₂.XMulIff →
    S₁.Bridge ϖ H b kind U₁ → S₂.Bridge ϖ H b kind U₂ →
    m.MapFl → h.LiftsDivisible c (Cu.ell c) g rr →
    ConstLift ϖ B.ℓ B.p H b kind U₁ U₂ (Cu.ell c) a₀ m.prL →
    PPval B.ℓ kap PP PP' →
    ∀ w, L₂.Wc Cu abelian₂ c w → ∃ (w' : V₁) (k : ℕ) (ε : Oˣ), k ≤ 2 * kap ∧
      L₁.Wc Cu abelian₂ c w' ∧
      h.f w' - C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k)) • w ∈ sm X (L₂.N c)

def LevelModelSetting {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ϖ : O) (ℓ ell : ℕ) (p : ℕ → PowerSeries O)
    (H b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) : Prop :=
  2 ≤ ℓ ∧ DistinguishedFamily ϖ ℓ ell p ∧ (∀ s < ell, Saturated ϖ (U₁ s)) ∧ (∀ s < ell, Saturated ϖ (U₂ s)) ∧
    (∀ s < ell, kind s = Kind.up → b s ≤ H s)

def LLift {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ℓ rr : ℕ)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  ∀ v : Fin r₂ → O, ∃ v₁ : Fin r₁ → O, prL v₁ = (ℓ : O) ^ rr • v

def CLift {O : Type} [CommRing O] {r₁ r₂ : ℕ} (ℓ a₀ : ℕ) (C₁ : Submodule O (Fin r₁ → O))
    (C₂ : Submodule O (Fin r₂ → O)) (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop :=
  ∀ v ∈ C₂, ∃ v₁ ∈ C₁, prL v₁ = (ℓ : O) ^ (2 * a₀) • v

def ConstLiftNone : Prop :=
  MNone → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (ℓ ell r₁ r₂ a₀ : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
      (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)),
      LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂ → (∀ s < ell, kind s ≠ Kind.down) →
      ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL

def ConstLiftD : Prop :=
  MD → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (ℓ ell r₁ r₂ a₀ rr : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
      (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)),
      LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂ → LLift ℓ rr prL → rr ≤ 2 * a₀ →
      ∀ s₁ : ℕ, s₁ < ell → kind s₁ = Kind.down → (∀ s < ell, s ≠ s₁ → kind s = Kind.thin) →
      ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL

def ConstLiftDU : Prop :=
  MDU → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (ℓ ell r₁ r₂ a₀ rr : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
      (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)),
      LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂ → LLift ℓ rr prL → rr ≤ 2 * a₀ →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.down → kind s₀ = Kind.up →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) → b s₀ < ℓ * b s₁ →
      ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL

def ConstLiftDD : Prop :=
  MDD → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (ℓ ell r₁ r₂ a₀ rr : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
      (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)),
      LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂ → LLift ℓ rr prL → rr ≤ 2 * a₀ →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.down → kind s₀ = Kind.down →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) →
      ∀ (ρ : ℕ) (fρ : PowerSeries O),
      C (ϖ ^ ρ) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} →
      (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p s₁ ^ b s₁, p s₀ ^ b s₀} → ρ ≤ k) →
      fρ ∈ Ideal.span {p s₁ ^ b s₁} → fρ - C (ϖ ^ ρ) ∈ Ideal.span {p s₀ ^ b s₀} →
      ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL

def ConstLiftUD : Prop :=
  MUD → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
    Irreducible ϖ → ∀ (ℓ ell r₁ r₂ a₀ rr : ℕ) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ)
      (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O))
      (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)),
      LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂ → LLift ℓ rr prL → rr ≤ 2 * a₀ →
      ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell → kind s₁ = Kind.up → kind s₀ = Kind.down →
      (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) →
      CLift ℓ a₀ (U₁ s₁) (U₂ s₁) prL →
      ∀ (c : ℕ) (α β : PowerSeries O),
      p s₁ ^ b s₁ = C (ϖ ^ c) * α + p s₀ ^ b s₀ * β →
      p s₁ ^ b s₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p s₀ ^ b s₀} →
      ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL

def ConstLiftOf : Prop :=
  ConstLiftNone ∧ ConstLiftD ∧ ConstLiftDU ∧ ConstLiftDD ∧ ConstLiftUD

end Formalism.ExponentWindows.E
end
end

section -- merged from Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

section ring
variable {O : Type} [CommRing O]

def Base.E3 (B : Base O) : Prop :=
  ∃ u : (PowerSeries O)ˣ, B.φ X = (u : PowerSeries O) * X * B.q ^ (B.ℓ - 1)

def Base.E4 (B : Base O) : Prop :=
  ∃ e : (PowerSeries O)ˣ, B.γ X = X * (1 + (e : PowerSeries O) * B.q)

def Base.GammaXUnitShape (B : Base O) (u₁ : O) : Prop :=
  (∃ a : PowerSeries O, B.γ X = X * (C u₁ + X * a)) ∧
    ∀ r : ℕ, 1 ≤ r → ∃ ε : Oˣ, u₁ ^ r - 1 = (ε : O) * (B.ℓ : O) ^ (1 + padicValNat B.ℓ r)

def Base.mm (B : Base O) : Ideal (PowerSeries O) := Ideal.span {B.lc, X}

end ring

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.P5M (L : Lat B n V) (i : ZMod n) (m : ℕ) : Prop :=
  ∀ v ∈ L.N (i - 1), B.q ^ m • L.φ i v ∈ L.N i

def Lat.FrobeniusCobounded (L : Lat B n V) (i : ZMod n) (h : ℕ) : Prop :=
  ∀ v ∈ L.N i, B.q ^ h • v ∈ Submodule.span (PowerSeries O) (L.φ i '' (L.N (i - 1) : Set V))

def Lat.P9 (L : Lat B n V) : Prop := ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i)

def Lat.PullFree (L : Lat B n V) (c : ZMod n) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (e : Fin r → V), Submodule.span (PowerSeries O) (Set.range e) = L.N c ∧
    LinearIndependent (PowerSeries O) (fun a => L.phiIt c k (e a))

def Lat.Free (L : Lat B n V) (i : ZMod n) : Prop :=
  ∃ (r : ℕ) (e : Fin r → V), LinearIndependent (PowerSeries O) e ∧
    Submodule.span (PowerSeries O) (Set.range e) = L.N i

def Lat.Complete (L : Lat B n V) : Prop := ∀ i, IsAdicComplete B.mm (L.N i)

def Lat.XReg (L : Lat B n V) : Prop := ∀ i, ∀ v ∈ L.N i, (X : PowerSeries O) • v = 0 → v = 0

def Lat.LTors (_L : Lat B n V) : Prop := ∀ v : V, B.lc • v = 0 → v = 0

end lat

section ext
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₂ V₀ : Type} [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
  {L₂ : Lat B n V₂} {L₀ : Lat B n V₀}

def Ext.P6 (Y : Ext L₂ L₀) : Prop := ∀ i (u : V₂), Y.ι.f u ∈ Y.LY.N i → u ∈ L₂.N i

def Ext.Lift (Y : Ext L₂ L₀) (e₀ : V₀) (c : ZMod n) (rr : ℕ) : Prop :=
  ∃ x ∈ Y.LY.N c, Y.π.f x = B.lc ^ rr • e₀

def Lat.PhiFree (L₀ : Lat B n V₀) (i : ZMod n) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → PowerSeries O),
    (∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t)) ∧
    ∀ m : Fin r → V₀, (∀ t, m t ∈ L₀.N i) → ∑ t, b t • L₀.phiIt i k (m t) = 0 → ∀ t, m t = 0

end ext

section ring2
variable {O : Type} [CommRing O]

def Base.E3it (B : Base O) (j : ℕ) : Prop :=
  ∃ u : (PowerSeries O)ˣ,
    (⇑B.φ)^[j] X = (u : PowerSeries O) * X * ∏ k ∈ Finset.range j, B.p k ^ (B.ℓ - 1)

def Base.E2 (B : Base O) (s : ℕ) : Prop :=
  B.p s ∈ Ideal.span {B.lc, (X : PowerSeries O) ^ (B.ℓ ^ s)}

def Base.Sat (B : Base O) (f : PowerSeries O) : Prop :=
  ∀ (K : ℕ) (a : PowerSeries O), B.lc ^ K * a ∈ Ideal.span {f} → a ∈ Ideal.span {f}

def SigOK (ℓ j M g sig : ℕ) : Prop :=
  (3 * g * ℓ ^ (j - 1) + M) * ℓ ≤ sig * (ℓ ^ (j - 1) * (ℓ - 1) ^ 2)

def Base.Trunc (B : Base O) (j M g sig : ℕ) : Prop :=
  ∀ r a : ℕ, (B.ℓ - 1) * a ≤ B.ℓ * r → ∃ x : PowerSeries O,
    B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a * x ∈ Ideal.span {B.ff j M g}

end ring2

section lat2
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.H (L : Lat B n V) (c : ZMod n) (M : ℕ) : Prop :=
  ∀ z ∈ sm X (L.N c), ∃ (K : ℕ) (a b : ℕ → ℕ) (d : ℕ → V),
    (∀ r, 1 ≤ r → r < M → a r + b r = K ∧ (B.ℓ - 1) * a r ≤ B.ℓ * r ∧ d r ∈ L.N c) ∧
    (L.γ c (∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r) -
      ∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r) - B.lc ^ K • z ∈ sm (X ^ M) (L.N c)

def Lat.FrobeniusMapsXPow (L : Lat B n V) (M : ℕ) : Prop :=
  ∀ i, ∀ v ∈ sm (X ^ M) (L.N (i - 1)), L.φ i v ∈ sm (X ^ M * B.q) (L.N i)

end lat2

def E3itOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O), B.E3 → ∀ j, B.E3it j

def BaseGoodOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (j M g : ℕ), B.E3 → B.E4 → 3 * g ≤ (B.ℓ - 1) * M →
    B.Good j M g

def ExistsGammaXUnitShape : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → B.ℓ.Prime → 3 ≤ B.ℓ → B.E4 → ∃ u₁ : O, B.GammaXUnitShape u₁

def SatAOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (j M g : ℕ), Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.E3 → B.Sat (B.ff j M g)

def TruncOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (j M g sig : ℕ), 3 ≤ B.ℓ → 1 ≤ j → B.E3 →
    SigOK B.ℓ j M g sig → B.Trunc j M g sig

def TruncSpanLe : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j M g G : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    G ≤ 3 * g → (∀ k : ℕ, 1 ≤ k → k ≤ j → L.P5M (c + (k : ZMod n)) G) →
    sm (B.ff j M g) (L.pull c j) ≤ sm (X ^ M) (L.N (c + (j : ZMod n)))

def FrobeniusMapsXPowOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (Mi : ZMod n → ℕ),
    B.E3 → (∀ i, L.P5M i (Mi i)) → (∀ i, Mi i < (B.ℓ - 1) * M) →
    L.FrobeniusMapsXPow M ∧ ∀ i, ∀ v ∈ sm (X ^ M) (L.N (i - 1)), L.φ i v ∈ sm (X ^ M) (L.N i)

def FrobeniusDiffBijective : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    B.E3 → L.FrobeniusMapsXPow M → L.Complete → L.XReg →
    ∀ t : ZMod n → V, (∀ i, t i ∈ sm (X ^ M) (L.N i)) →
      ∃! z : ZMod n → V, (∀ i, z i ∈ sm (X ^ M) (L.N i)) ∧ L.dφ z = t

def CompleteOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    IsAdicComplete (Ideal.span {(B.ℓ : O)}) O → (∀ i, L.Free i) → L.Complete

def XRegOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    (∀ i, L.Free i) → L.XReg

def SatOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j : ℕ) (f : PowerSeries O)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.Sat f → L.PullFree c j →
    ∀ (K : ℕ), ∀ v ∈ L.pull c j, B.lc ^ K • v ∈ sm f (L.pull c j) → v ∈ sm f (L.pull c j)

def GamInjOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (u₁ : O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.GammaXUnitShape u₁ → L.P9 → ∀ v ∈ sm X (L.N c), L.γ c v - v ∈ sm (X ^ M) (L.N c) →
      ∃ K : ℕ, B.lc ^ K • v ∈ sm (X ^ M) (L.N c)

def HOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (u₁ : O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.ℓ.Prime → B.GammaXUnitShape u₁ → L.P9 → L.H c M

def ExistsTransport : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j M g sig : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.Trunc j M g sig → L.H c M → ∀ z ∈ sm X (L.N c), ∃ τ, L.IsTr c j M g sig z τ

def LatticeLeArcSpan : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (hh H : ℕ → ℕ), (∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)) →
    (∀ s < ell, hh s ≤ H s) →
    L.N c ≤ dv (∏ s ∈ Finset.range ell, B.p s ^ H s) (L.pull (c - (ell : ZMod n)) ell)

def ExtCOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (Y : Ext L₂ L₀),
    Y.P6 → L₀.XReg → ∀ i (k : ℕ) (u : V₂), Y.ι.f u ∈ sm (X ^ k) (Y.LY.N i) →
      u ∈ sm (X ^ k) (L₂.N i)

def ExtGOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (Y : Ext L₂ L₀)
    (i : ZMod n) (k : ℕ) (lam : PowerSeries O), Y.P6 → L₀.PhiFree i k →
    ∀ u : V₂, Y.ι.f u ∈ dv lam (Y.LY.pull i k) → u ∈ dv lam (L₂.pull i k)

def LatGoodOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (u₁ : O) (n : ℕ) [NeZero n] (Cu : Cuts n) (j M g G sig : ℕ) (Mi : ZMod n → ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.ℓ.Prime → 3 ≤ B.ℓ → 1 ≤ j →
    B.E3 → B.GammaXUnitShape u₁ → G ≤ g → SigOK B.ℓ j M g sig →
    L.P9 → (∀ i, L.P5M i (Mi i)) → (∀ i, Mi i < (B.ℓ - 1) * M) →
    (∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → Mi (c + (k : ZMod n)) ≤ G) →
    (∀ c ∈ Cu.cuts, L.PullFree c j) → L.Complete → L.XReg → L.LTors →
    L.Good Cu j M g sig

end Formalism.ExponentWindows.E
end
end
