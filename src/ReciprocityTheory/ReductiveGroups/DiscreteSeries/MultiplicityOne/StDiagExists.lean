module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StDiagExists : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    IsCRepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → ContinuousOn π (UWset k r z) →
    Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    ∃ D : RealPlaceData k r Wp Wp, D.z = z ∧ D.π = π ∧ IsDiag D

def StSchurG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∃ d : ℝ, IsFdegG D X d

def StPairs : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ d : ℝ, IsFdegG D X d → ∀ a₁ a₂ : ℝ, ∀ u ∈ VflA X a₁, ∀ v ∈ VflA X a₂,
      ∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-(min a₁ a₂ - AG k r - 1))

def StBeConv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ (b : ℝ), AS k r + 1 ≤ b → ∀ u v : X.Hs,
      (∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u v x‖ ≤ C * gN x ^ (-b)) →
      Integrable (beInt D X u v) (D.μW.prod D.μN)

def StBeEquiv : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u u' : X.Hs, Integrable (beInt D X u u') (D.μW.prod D.μN) →
      ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u') ∧
        beOp D X u (X.σ (m * h) u') = star (psiD D m) • (beOp D X u u').comp (D.π h⁻¹)

def StRepro : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ d : ℝ, IsFdegG D X d → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X,
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG ∧
      beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG

def StSmooth : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ φ φ' : Mat k r → ℂ, IsTestG φ → IsTestG φ' → ∀ m : ℕ,
      InCC (X.a - AG k r - 1) m (mc X (sigInt D X φ X.w) (sigInt D X φ' X.w))

def StFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → 0 < Tz k r z →
    ∃ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r z γ

def StInvGroup : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ g ∈ GV k r, gbar k r γ g ∈ GV k r) ∧ (∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r) ∧
    (∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z) ∧ (∀ u ∈ UUset k r D.z γ, gbar k r γ u ∈ UUset k r D.z γ) ∧
    (∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g) ∧
    (∀ g ∈ GV k r, th k r γ (th k r γ g) = g) ∧
    D.μG.map (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = D.μG ∧
    D.μN.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μN ∧
    D.μW.map (fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) = D.μW

def StInvChar : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m ∧ psiD D (th k r γ m) = psiD D m

def StInvCC : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∃ C : ℝ, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g) ∧
    ∀ (A : ℝ) (m : ℕ) (F : Mat k r → ℂ), InCC A m F → InCC A m (F ∘ th k r γ)

def StReps : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (c : Fin r → ℂ) (d : ℂ), (∀ a, c a ≠ 0) → 1 < ‖d‖ →
      (γ * mud k d * γ⁻¹)ᴴ * Hb k * (γ * mud k d * γ⁻¹) = Hb k ∧
      herm (Hpk k r) (embWb k r (γ * mud k d * γ⁻¹) *ᵥ D.z) D.z = -((Tz k r D.z : ℝ) : ℂ) * d ∧
      g0 k r γ c d ∈ GV k r ∧ th k r γ (g0 k r γ c d) = g0 k r γ c d ∧
      ∃ h ∈ UWset k r D.z, ∃ h' ∈ UWset k r D.z, gq D (c, -((Tz k r D.z : ℝ) : ℂ) * d) = h⁻¹ * g0 k r γ c d * h'

def StTransM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹

def StSym : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ (f : Mat k r → ℂ) (q : (Fin r → ℂ) × ℂ), Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG →
      q ∈ Qset D → Tz k r D.z * Tz k r D.z < Complex.normSq q.2 → Ef D (scalF Wp f) q ≠ ∞ →
      JF D (scalF Wp (f ∘ th k r γ)) (gq D q) = JF D (scalF Wp f) (gq D q)

def StSymBeta : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    ∀ A : ℝ, AB k r ≤ A → JCont D A → ∀ (f : Mat k r → ℂ) (F' : Mat k r → (Wp →L[ℂ] Wp)),
      InCC A 5 f → InCC A 5 F' → beta D (scalF Wp (f ∘ th k r γ)) F' = beta D (scalF Wp f) F'

def StBetaInf : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ),
    XiExists → AB k r ≤ A → ∀ F F' : Mat k r → (Wq →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      Integrable (Ph D F F') D.μSS → betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS

def StDichoG : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) ∨
    ∃ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs, (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) ∧
      ∀ h ∈ GV k r, ∀ v : X.Hs, C (X.σ h v) = X.σ (th k r γ h)⁻¹ (C v)

def StDichoW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : Wp,
      ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ * star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) ∨
    ∃ C : Wp ≃ₗᵢ⋆[ℂ] Wp, (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C x, D.π h (C y)⟫_ℂ) ∧
      ∀ h ∈ UWset k r D.z, ∀ v : Wp, C (D.π h v) = D.π (th k r γ h)⁻¹ (C v)

def StMixed : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    aM k r ≤ X.a → ∀ C : X.Hs ≃ₗᵢ⋆[ℂ] X.Hs,
      (∀ g ∈ GV k r, ∀ x y : X.Hs, ⟪y, X.σ (th k r γ g) x⟫_ℂ = ⟪C x, X.σ g (C y)⟫_ℂ) →
      ∀ u ∈ Vfl X, C u ∈ VflA X (X.a - AG k r - 1)

def ThmM : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∃ l : X.Hs → Wp, IsMultOneMap D X l

def StMFix : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d →
      ∀ W' : Mat k r → Wp, AEStronglyMeasurable (fun y : Mt k r => W' (Matrix.of y)) D.μG →
        (∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, W' (m * h * x) = psiD D m • D.π h (W' x)) →
        (∀ x ∈ GV k r, Integrable (fun y : Mt k r => gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) D.μG) →
        ∃ c : ℂ, ∀ x ∈ GV k r,
          ∫ y : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of y))) • W' (x * Matrix.of y) ∂D.μG = c • l (X.σ x X.w)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA
noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

def Cj (H : Type*) := H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def toCj (x : H) : Cj H := x

def ofCj (x : Cj H) : H := x

instance : NormedAddCommGroup (Cj H) := inferInstanceAs (NormedAddCommGroup H)

instance instModuleCj : Module ℂ (Cj H) := Module.compHom H (starRingEnd ℂ)

theorem smul_def (c : ℂ) (x : Cj H) : c • x = toCj (conj c • ofCj x) := rfl

instance : NormedSpace ℂ (Cj H) where
  norm_smul_le c x := by
    show ‖(conj c • ofCj x : H)‖ ≤ ‖c‖ * ‖(ofCj x : H)‖
    rw [norm_smul, Complex.norm_conj]

instance : Inner ℂ (Cj H) := ⟨fun x y => ⟪(ofCj y : H), ofCj x⟫_ℂ⟩

theorem inner_def (x y : Cj H) : ⟪x, y⟫_ℂ = ⟪(ofCj y : H), ofCj x⟫_ℂ := rfl

instance : InnerProductSpace ℂ (Cj H) where
  norm_sq_eq_re_inner x := by
    show ‖(ofCj x : H)‖ ^ 2 = RCLike.re ⟪(ofCj x : H), ofCj x⟫_ℂ
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (ofCj x : H)).symm
  conj_inner_symm x y := by
    show conj ⟪(ofCj x : H), ofCj y⟫_ℂ = ⟪(ofCj y : H), ofCj x⟫_ℂ
    exact inner_conj_symm _ _
  add_left x y z := by
    show ⟪(ofCj z : H), ofCj x + ofCj y⟫_ℂ = ⟪(ofCj z : H), ofCj x⟫_ℂ + ⟪(ofCj z : H), ofCj y⟫_ℂ
    exact inner_add_right _ _ _
  smul_left x y r := by
    show ⟪(ofCj y : H), conj r • ofCj x⟫_ℂ = conj r * ⟪(ofCj y : H), ofCj x⟫_ℂ
    exact inner_smul_right _ _ _

instance [CompleteSpace H] : CompleteSpace (Cj H) := inferInstanceAs (CompleteSpace H)

def opCj (A : H →L[ℂ] H) : Cj H →L[ℂ] Cj H where
  toFun x := toCj (A (ofCj x))
  map_add' x y := A.map_add (ofCj x) (ofCj y)
  map_smul' c x := A.map_smul (conj c) (ofCj x)
  cont := A.continuous

theorem opCj_apply (A : H →L[ℂ] H) (x : Cj H) : opCj A x = toCj (A (ofCj x)) := rfl

def eCj : Cj H ≃ₗᵢ⋆[ℂ] H where
  toFun := ofCj
  invFun := toCj
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace
end
end
