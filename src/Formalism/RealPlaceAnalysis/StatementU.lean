module

public import Formalism.RealPlaceAnalysis.StatementE

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.StatementU
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

def LamOf {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε

def cvalR {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ := nsq lam - nsq (rhoC ε + rhoN ε)

def KindA {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) : Prop :=
  KHighest ε E (LamOf ε lam) u ∧ Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u ∧
    FiniteDimensional ℂ (kSpan ε E u)

def Regime {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) : Prop :=
  (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧
    (n : ℝ) ^ 3 + 2 < 2 * g ∧ 2 * (n : ℝ) < g

def pfil {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ w : List (Fin n × Fin n), w.length ≤ j ∧ (∀ p ∈ w, ε p.1 ≠ ε p.2) ∧
    ∃ y ∈ kSpan ε E u, x = ew E w y}

abbrev Arr (V : Type*) (n j : ℕ) : Type _ := PiLp 2 (fun _ : Fin j → Fin n × Fin n => V)

def arrOf (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    Arr V n j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → V) :=
  (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).toLinearMap

def arrTo (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    ((Fin j → Fin n × Fin n) → V) →ₗ[ℂ] Arr V n j :=
  (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).symm.toLinearMap

def factorAction {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (i : Fin j) (c d : Fin n) :
    Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    (if (α i).1 = c then LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V)
        (Function.update α i (d, (α i).2)) else 0) -
    (if (α i).2 = d then LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V)
        (Function.update α i ((α i).1, c)) else 0)) ∘ₗ arrOf V n j

def ptE {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (c d : Fin n) : Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    E c d ∘ₗ LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α) ∘ₗ arrOf V n j

def arrE {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (j : ℕ) : Fin n → Fin n → Module.End ℂ (Arr V n j) :=
  fun c d => (∑ i : Fin j, factorAction i c d) + ptE E c d

def positionsE (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) :
    Fin n → Fin n → Module.End ℂ (Arr V n j) :=
  fun c d => ∑ i : Fin j, factorAction i c d

def OmS {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) : Module.End ℂ (Arr V n j) :=
  ∑ c, ∑ d, if ε c = ε d then factorAction i c d * ptE E d c else 0

def thetaA {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (j : ℕ) : Arr V n j →ₗ[ℂ] V :=
  ∑ α : Fin j → Fin n × Fin n,
    ew E (List.ofFn α).reverse ∘ₗ LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ
      arrOf V n j

def permArr (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) {j : ℕ} (σ : Equiv.Perm (Fin j)) :
    Module.End ℂ (Arr V n j) :=
  arrTo V n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) (fun i => α (σ i))) ∘ₗ arrOf V n j

def symSub (V : Type*) [AddCommGroup V] [Module ℂ V] (n j : ℕ) : Submodule ℂ (Arr V n j) :=
  ⨅ σ : Equiv.Perm (Fin j), LinearMap.ker (permArr V n σ - 1)

def arrV0 {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : ℕ) : Submodule ℂ (Arr V n j) :=
  ⨅ α : Fin j → Fin n × Fin n,
    (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥).comap
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α ∘ₗ arrOf V n j)

def sliceLin (V : Type*) [AddCommGroup V] [Module ℂ V] (n : ℕ) {j : ℕ} (α' : Fin j → Fin n × Fin n) :
    Arr V n (j + 1) →ₗ[ℂ] Arr V n 1 :=
  arrTo V n 1 ∘ₗ (LinearMap.pi fun β : Fin 1 → Fin n × Fin n =>
    LinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) → Fin n × Fin n => V)
      (Fin.cons (β 0) α' : Fin (j + 1) → Fin n × Fin n)) ∘ₗ arrOf V n (j + 1)

def Vplus {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) : Submodule ℂ (Arr V n 1) :=
  isoPart ε (arrE E 1) {μ | ∃ a b, a < b ∧ ε a ≠ ε b ∧ μ = Λ + root a b} (arrV0 ε E u 1)

def Vminus {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) : Submodule ℂ (Arr V n 1) :=
  isoPart ε (arrE E 1) {μ | ∃ a b, b < a ∧ ε a ≠ ε b ∧ μ = Λ + root a b} (arrV0 ε E u 1)

def Nset {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ) :
    Submodule ℂ (Arr V n (j + 1)) :=
  arrV0 ε E u (j + 1) ⊓ symSub V n (j + 1) ⊓
    ⨅ α' : Fin j → Fin n × Fin n, (Vplus ε E Λ u).comap (sliceLin V n α')

def CasOnCyc : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ) (u : V),
    GlRel E → Cas E u = c • u → ∀ x ∈ cyc E u, Cas E x = c • x

def PfilFacts : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V),
    GlRel E →
    pfil ε E u 0 = kSpan ε E u ∧
    (∀ j, pfil ε E u j ≤ pfil ε E u (j + 1)) ∧
    (∀ j, KStable ε E (pfil ε E u j)) ∧
    (∀ j (a b : Fin n), ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1)) ∧
    (∀ j, pfil ε E u j ≤ cyc E u) ∧
    (∀ x ∈ cyc E u, ∃ j, x ∈ pfil ε E u j) ∧
    (FiniteDimensional ℂ (kSpan ε E u) → ∀ j, FiniteDimensional ℂ (pfil ε E u j))

def ArrModule : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ),
    (GlRel E → GlRel (arrE E j) ∧
      ∀ (c d : Fin n) (F : Arr V n j), thetaA E j (arrE E j c d F) = E c d (thetaA E j F)) ∧
    (IsUnitary ε E → KUnit ε (arrE E j))

def ThetaFil : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V),
    GlRel E →
    (∀ j, ∀ F ∈ arrV0 ε E u j, thetaA E j F ∈ pfil ε E u j) ∧
    (∀ j, pfil ε E u (j + 1) ≤ (arrV0 ε E u (j + 1)).map (thetaA E (j + 1)) ⊔ pfil ε E u j) ∧
    (∀ j, ∀ F ∈ arrV0 ε E u (j + 1), ∀ σ : Equiv.Perm (Fin (j + 1)),
      thetaA E (j + 1) (permArr V n σ F) - thetaA E (j + 1) F ∈ pfil ε E u j)

def HVCoeff : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ μ : Fin n → ℝ) (u : V) (F : Arr V n 1),
    GlRel E → IsUnitary ε E → KHighest ε E Λ u →
    F ∈ arrV0 ε E u 1 → KHighest ε (arrE E 1) μ F → F ≠ 0 →
    ∃ a b, ε a ≠ ε b ∧ μ = Λ + root a b

def TypesSplit : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ F ∈ Vplus ε E Λ u, ∀ G ∈ Vminus ε E Λ u, ⟪F, G⟫_ℂ = 0) ∧
    Vplus ε E Λ u ⊔ Vminus ε E Λ u = arrV0 ε E u 1

def OmPlus : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    ∀ F ∈ Vplus ε E (LamOf ε lam) u,
      (g - 2 * (n : ℝ)) * ‖F‖ ^ 2 ≤ (⟪F, OmS ε E (0 : Fin 1) F⟫_ℂ).re

def CasArr : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ),
    (GlRel E → KHighest ε E Λ u → ∀ F ∈ arrV0 ε E u j,
      CasK ε (arrE E j) F = CasK ε (positionsE V n j) F + ((ckv ε Λ : ℝ) : ℂ) • F +
        (2 : ℂ) • ∑ i : Fin j, OmS ε E i F) ∧
    ∀ F : Arr V n j, 0 ≤ (⟪F, CasK ε (positionsE V n j) F⟫_ℂ).re

def OmSymSlice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) (F : Arr V n (j + 1)),
    (F ∈ symSub V n (j + 1) → ∀ i : Fin (j + 1), ⟪F, OmS ε E i F⟫_ℂ = ⟪F, OmS ε E 0 F⟫_ℂ) ∧
    ⟪F, OmS ε E 0 F⟫_ℂ =
      ∑ α' : Fin j → Fin n × Fin n, ⟪sliceLin V n α' F, OmS ε E (0 : Fin 1) (sliceLin V n α' F)⟫_ℂ

def NStable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : ℕ),
    KStable ε (arrE E (j + 1)) (Nset ε E Λ u j)

def NPos : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ),
    GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    ∀ F ∈ Nset ε E (LamOf ε lam) u j,
      (ckv ε (LamOf ε lam) + 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ))) * ‖F‖ ^ 2 ≤
        (⟪F, CasK ε (arrE E (j + 1)) F⟫_ℂ).re

def UGrowth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (c : ℝ) (u : V),
    GlRel E → IsUnitary ε E → KHighest ε E μ u → Cas E u = (c : ℂ) • u →
    FiniteDimensional ℂ (kSpan ε E u) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ b, ‖E a b x‖ ^ 2 ≤
        (2 * (n : ℝ) * (Real.sqrt (ckv ε μ) + j + n) ^ 2 + |c|) * ‖x‖ ^ 2

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
open MeasureTheory

noncomputable section

namespace Formalism.REAL

def hh {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.log (hs g)

def Eword {n : ℕ} (ε : Fin n → Bool) : List (Fin n × Fin n) →
    (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ)
  | [] => id
  | p :: w => fun f => Eab ε p.1 p.2 (Eword ε w f)

def CasF {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g

abbrev toM {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def HhLip : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    SmoothOnG ε (fun x => ((hh x : ℝ) : ℂ)) ∧
    ∀ (X g : Matrix (Fin n) (Fin n) ℂ), inG ε X → inUJ ε g →
      ‖Rd X (fun x => ((hh x : ℝ) : ℂ)) g‖ ≤ 2 * Real.sqrt (hs X)

def IntRdZero : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ), SmoothOnG ε φ → inG ε X → (∀ g, inUJ ε g → R < hs g → φ g = 0) →
    ∫ g : UJ ε, Rd X φ (toM g) ∂(muG ε) = 0

def SmoothVectorGrowthBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ) (a : ℝ),
    FiniteDimensional ℂ W → 0 ≤ a →
    (∀ w ∈ W, SmoothOnG ε w) →
    (∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g) →
    (∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g) →
    (∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2) (muG ε)) →
    ∀ (w₁ w₂ : List (Fin n × Fin n)) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), f ∈ W → f' ∈ W →
      SmoothOnG ε (Eword ε w₁ f) ∧
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w₁ f (toM g)‖ ^ 2) (muG ε) ∧
      ∀ i j : Fin n,
        ∫ g : UJ ε, Eab ε i j (Eword ε w₁ f) (toM g) * starRingEnd ℂ (Eword ε w₂ f' (toM g)) ∂(muG ε) =
          (sgn ε i j : ℂ) *
            ∫ g : UJ ε, Eword ε w₁ f (toM g) * starRingEnd ℂ (Eab ε j i (Eword ε w₂ f') (toM g)) ∂(muG ε)

end Formalism.REAL
end
end
