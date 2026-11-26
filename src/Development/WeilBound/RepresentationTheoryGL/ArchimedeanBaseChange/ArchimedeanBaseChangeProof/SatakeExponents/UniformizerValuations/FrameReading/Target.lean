module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.Choice
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def rh (N : ℕ) (i : ℕ) : ℤ := (N : ℤ) - 1 - 2 * (i : ℤ)

def IsStd (w : Pl E) (s : Shuf n) (sg : Fin n → ℂˣ) : Prop :=
  ∀ k, s.eps k = sg k * qU w (rh n k - Sum.elim (fun i : Fin s.a => rh s.a i) (fun j : Fin s.b => rh s.b j) (s.e.symm k))

def chiN (w : Pl E) (ξ : Fin n → ℂˣ) : Fin n → ℂˣ := fun k => ξ k * qU w (rh n k)

def TargetAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n) (sg ξ : Fin n → ℂˣ)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ), IsStd w s sg → chiOf w s ξa ξb = chiN w ξ →
    (∀ i, ξa i = ξ (s.e (.inl i)) * (sg (s.e (.inl i)))⁻¹) ∧ ∀ j, ξb j = ξ (s.e (.inr j)) * (sg (s.e (.inr j)))⁻¹

def MonoRes : Prop := ∀ (n : ℕ) (s : Shuf n) (sg ξ : Fin n → ℂˣ), N3.Mono ξ → (∀ k, ‖((sg k : ℂˣ) : ℂ)‖ = 1) →
  N3.Mono (fun i => ξ (s.e (.inl i)) * (sg (s.e (.inl i)))⁻¹) ∧ N3.Mono (fun j => ξ (s.e (.inr j)) * (sg (s.e (.inr j)))⁻¹)

def SatSph : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n) (w : Pl E) (B : Multiset ℂˣ),
  D.Sat w B → GlobalTheory.LGrp.IsSpherical (prodAt D w) (GlobalTheory.LFun.KGL w (n := n))

end PositivityTheory.Rg.BcB.F.Tail

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Tail

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def idem {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (U : Set (GLw a w × GLw b w)).indicator fun _ => ((U.relIndex (K2 a b w) : ℕ) : ℂ)

def IsLev (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) : Prop :=
  (∀ w, IsOpen (U w : Set (GLw a w × GLw b w)) ∧ U w ≤ K2 a b w) ∧ ∀ᶠ w in cofinite, U w = K2 a b w

def HasLev (G : H E a b → ℂ) : Prop :=
  ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ u ∈ U, ∀ x, G (x * finH u) = G x

def OfLev (S : Set (Pl E)) (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ) : Prop :=
  HasLev G ∧ ∀ w ∈ S, G ∈ fixed (pairRt a b w) (U₁ w) ∧ (IsSplitAt w → G ∈ fixed (pairRtT a b w) (U₂ w))

def actT (w : Pl E) (u : LF a b w) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRtT a b w m G z

def locM {k : Type} [Fintype k] (w : Pl E) (M : k → k → LF a b w) (G : k → H E a b → ℂ) : k → H E a b → ℂ :=
  fun x => ∑ y, actP w (M x y) (G y)

def DiagIdem {κ : Pl E → Type} (P : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (L : LM κ a b) : Prop :=
  ∀ w ∈ P, ∀ x y, L.m w x y = if x = y then idem (U w) else 0

def FmOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (w₀ : Pl E), IsLev U₁ → IsLev U₂ → L.Ok P → DiagIdem P U₁ L → (∀ i, OfLev S U₁ U₂ (F i)) → w₀ ∈ S →
    (w₀ ∉ P → (∀ w, w ≠ w₀ → L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actP w₀ (L.s w₀) (F i)) ∧
    (IsSplitAt w₀ → (∀ w, L.s w = idem (U₁ w)) → (∀ w, w ≠ w₀ → L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actT w₀ (L.t w₀) (F i))

def FmPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (m : ℕ), IsLev U₁ → IsLev U₂ → L.Ok P → (∀ w, L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
    (∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g) →
    (∀ i, OfLev S U₁ U₂ (F i)) → (convF B.ν (fm S P B e L))^[m] F ≠ 0 →
    ∀ w₀ : P, ∃ (α : A) (x : ∀ w : P, κ w), (locM w₀.1 (L.m w₀.1))^[m] (fun y => F (α, e.symm (Function.update x w₀ y))) ≠ 0

def ConvMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (A : Type)
  (ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (U : Subgroup (Hf E B.a B.b)) (F : A × B.κ → H E B.a B.b → ℂ), IsFinM ψ → IsFinM ψ' →
  IsOpen (U : Set (Hf E B.a B.b)) → (∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) →
    convF B.ν (mulF B.ν ψ ψ') F = convF B.ν ψ (convF B.ν ψ' F) ∧
      ((∀ x y, ∀ u ∈ U, ∀ h, ψ' x y (u * h) = ψ' x y h) → ∀ i, ∀ u ∈ U, ∀ x, convF B.ν ψ' F i (x * finH u) = convF B.ν ψ' F i x)

def LocPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (k : Type) [Fintype k]
  (U : Subgroup (GLw a w × GLw b w)) (G : k → H E a b → ℂ) (m : ℕ), IsOpen (U : Set (GLw a w × GLw b w)) →
  (∀ y, G y ∈ fixed (pairRt a b w) U) →
  (∀ (c : ℂ) (M : k → k → LF a b w), (locM w fun x y => c • M x y)^[m] G ≠ 0 → (locM w M)^[m] G ≠ 0) ∧
    ∀ q : k → LF a b w, (locM w fun x y => if x = y then q x else 0)^[m] G ≠ 0 → ∃ x, (actP w (q x))^[m] (G x) ≠ 0

def ActHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f : LF a b w) (G : H E a b → ℂ),
  HasCompactSupport f → (∀ k ∈ K2 a b w, ∀ g, f (g * k) = f g) →
  (G ∈ fixed (pairRt a b w) (K2 a b w) → actP w f G = GlobalTheory.LFun.heckeVec (pairRt a b w) (K2 a b w) f G) ∧
    (G ∈ fixed (pairRtT a b w) (K2 a b w) → actT w f G = GlobalTheory.LFun.heckeVec (pairRtT a b w) (K2 a b w) f G)

end PositivityTheory.Rg.BcB.F.Tail

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel
noncomputable section

open NumberField

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

def GelfInj : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ m, GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m) →
    Finset.univ.val.map x = Finset.univ.val.map y

def RegDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n),
    RealSym (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w)) ∧ ∀ τ, GapM (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) τ)

def Reg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n)
    (χ : InfinitePlace E → PositivityTheory.RgBcC.Inf n),
    (∀ v s m, GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (PositivityTheory.RgBcC.infOf (l v).w s) m) →
      RealSym (mOf χ) ∧ ∀ τ, GapM (mOf χ τ)

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

def genE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (y : Γ) : ChAlg g X :=
  ⟨(g y).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨y, rfl⟩)⟩

def XE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) : ChAlg g X :=
  ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩

def ConvMulSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ₁ → IsTestM Φ₂ → ∀ f : ι → H E a b → ℂ,
  (∀ i, Continuous (f i)) →
  PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f)

def FinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E)
  (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin B.a) (Af E))) → IsCompact (K₁ : Set (GL (Fin B.a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin B.b) (Af E))) → IsCompact (K₂ : Set (GL (Fin B.b) (Af E))) →
  ∀ (cK : ℂ) (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)),
  cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1 →
  (∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0) →
  (∀ (A : Type) (f : A × B.κ → H E B.a B.b → ℂ), (∀ i, ∀ u ∈ K₁.prod K₂, ∀ x, f i (x * finH u) = f i x) →
    convF B.ν ψ₀ f = f ∧ ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → convF B.ν (mulF B.ν ψ ψ₀) f = convF B.ν ψ f) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ →
    ∀ x y, ∀ u ∈ K₁.prod K₂, ∀ h, mulF B.ν ψ ψ₀ x y (h * u) = mulF B.ν ψ ψ₀ x y h

def RealiseSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Γ : Type) [Countable Γ]
  (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ),
  (∀ x, (g x).Ok) → tX.Ok → X = tX.op → g a₀ = Sum.inr t₀ →
  (∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op)) →
  (∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) → IsSelfAdjoint X →
  (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) → χ (genE g X a₀) ≠ 0 →
  ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
    (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
    Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
    ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
      (∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) =
        (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
