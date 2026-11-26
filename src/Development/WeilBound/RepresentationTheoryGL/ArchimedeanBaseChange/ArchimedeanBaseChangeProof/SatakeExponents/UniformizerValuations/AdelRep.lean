module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev LF (a b : ℕ) (w : Pl E) : Type := GLw a w × GLw b w → ℂ

def lfStar {w : Pl E} (f : LF a b w) : LF a b w := fun y => starRingEnd ℂ (f y⁻¹)

structure LM (κ : Pl E → Type) (a b : ℕ) where
  m : ∀ w, κ w → κ w → LF a b w
  s : ∀ w : Pl E, LF a b w
  t : ∀ w : Pl E, LF a b w

namespace LM

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E))

def ent (L : LM κ a b) (x y : ∀ w : P, κ w) (w : Pl E) : LF a b w := if h : w ∈ P then L.m w (x ⟨w, h⟩) (y ⟨w, h⟩) else L.s w

def Ok (L : LM κ a b) : Prop := (∀ x y, IsTestP (L.ent P x y)) ∧ IsTestP L.t

def mul (L L' : LM κ a b) : LM κ a b :=
  ⟨fun w x y => ∑ z, mconv (L.m w x z) (L'.m w z y), fun w => mconv (L.s w) (L'.s w), fun w => mconv (L.t w) (L'.t w)⟩

def adj (L : LM κ a b) : LM κ a b := ⟨fun w x y => lfStar (L.m w y x), fun w => lfStar (L.s w), fun w => lfStar (L.t w)⟩

def tr (L : LM κ a b) (N : ∀ w, κ w → κ w → ℂ) (w : Pl E) : LF a b w :=
  if w ∈ P then ∑ x, ∑ y, N w y x • L.m w x y else L.s w

end LM

def Block.vol (B : Block E) : ℂ := (B.ν.real ((Kf E B.a).prod (Kf E B.b) : Subgroup (Hf E B.a B.b)) : ℝ)

section

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)

def fm (L : LM κ B.a B.b) : Matrix B.κ B.κ (Hf E B.a B.b → ℂ) := fun x y h => B.vol⁻¹ * finFn S (L.ent P (e x) (e y)) L.t h

def tenN (N : ∀ w, κ w → κ w → ℂ) : Matrix B.κ B.κ ℂ := fun x y => ∏ w : P, N w (e x w) (e y w)

end

def rt {κ : Type} (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y h => ψ x y (h * (ratF E a u₁, ratF E b u₂)⁻¹)

def PT.arch {B : Block E} (t : PT B) (Ta : Ops B.Ma) (Tb : Ops B.Mb) (v : InfinitePlace E) (y : G B.a × G B.b) : ℂ :=
  phiOf (B.Ma v) (Ta v) (t.ka v) y.1 * phiOf (B.Mb v) (Tb v) (t.kb v) y.2

def IntHint : Prop := ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure] (K U : Subgroup Γ) (f : Γ → ℂ), IsOpen (K : Set Γ) → IsCompact (K : Set Γ) →
  IsOpen (U : Set Γ) → HasCompactSupport f → (∀ u ∈ U, ∀ x, f (x * u) = f x) → ν.IsMulRightInvariant →
  ∫ x, f x ∂ν = (ν.real K : ℂ) * hint K f

def HintProd : Prop := ∀ (ι Γ : Type) [Group Γ] (Hl : ι → Type) [∀ i, Group (Hl i)] [∀ i, TopologicalSpace (Hl i)]
  [∀ i, IsTopologicalGroup (Hl i)] (p : ∀ i, Γ →* Hl i) (K : Subgroup Γ) (KH U : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ),
  (∀ x y : Γ, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, Hl i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : Γ, ∀ i, p i x = y i) →
  (∀ x : Γ, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : Γ, x ∈ K ↔ ∀ i, p i x ∈ KH i) →
  (∀ i, IsCompact (KH i : Set (Hl i)) ∧ IsOpen (KH i : Set (Hl i)) ∧ IsOpen (U i : Set (Hl i)) ∧ HasCompactSupport (f i) ∧
    ∀ u ∈ U i, ∀ x, f i (x * u) = f i x) →
  (∀ᶠ i in cofinite, f i = (KH i : Set (Hl i)).indicator 1) →
  hint K (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, hint (KH i) (f i)

abbrev Slot (S : Set (Pl E)) : Type := {w // w ∈ S} ⊕ {w // w ∈ S ∧ IsSplitAt w}

def Slot.pl {S : Set (Pl E)} : Slot S → Pl E := Sum.elim Subtype.val Subtype.val

def Slot.cp {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, Gf E a b → GLw a i.pl × GLw b i.pl
  | .inl w => atW w.1
  | .inr w => fun y => atW w.1 (thP E a b y)

def Slots : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)), IsSection S →
  (∀ (i : Slot S) x y, i.cp a b (x * y) = i.cp a b x * i.cp a b y) ∧ (∀ i : Slot S, Continuous (i.cp a b)) ∧
  (∀ x y : Gf E a b, (∀ i : Slot S, i.cp a b x = i.cp a b y) → x = y) ∧
  (∀ y : ∀ i : Slot S, GLw a i.pl × GLw b i.pl, (∀ᶠ i in cofinite, y i ∈ K2 a b i.pl) → ∃ x, ∀ i : Slot S, i.cp a b x = y i) ∧
  (∀ x, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl) ∧
  (∀ x, x ∈ (Kf E a).prod (Kf E b) ↔ ∀ i : Slot S, i.cp a b x ∈ K2 a b i.pl) ∧
  ∀ C : ∀ i : Slot S, Set (GLw a i.pl × GLw b i.pl), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = K2 a b i.pl) →
    IsCompact {x : Gf E a b | ∀ i : Slot S, i.cp a b x ∈ C i}

def FinConv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (S : Set (Pl E)), IsSection S →
  B.vol ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁ → IsTestP φ₂ →
    HasCompactSupport (finFn S φ₁ φ₂) ∧
    (∃ U : Subgroup (Hf E B.a B.b), IsOpen (U : Set (Hf E B.a B.b)) ∧
      ∀ u ∈ U, ∀ h, finFn S φ₁ φ₂ (u * h) = finFn S φ₁ φ₂ h ∧ finFn S φ₁ φ₂ (h * u) = finFn S φ₁ φ₂ h) ∧
    ∀ φ₁' φ₂' : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁' → IsTestP φ₂' →
      IsTestP (fun w => mconv (φ₁ w) (φ₁' w)) ∧ IsTestP (fun w => mconv (φ₂ w) (φ₂' w)) ∧
      ∀ g, ∫ h, finFn S φ₁ φ₂ h * finFn S φ₁' φ₂' (h⁻¹ * g) ∂B.ν =
        B.vol * finFn S (fun w => mconv (φ₁ w) (φ₁' w)) (fun w => mconv (φ₂ w) (φ₂' w)) g

def FmAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ L L' : LM κ B.a B.b, L.Ok P → L'.Ok P →
    IsFinM (fm S P B e L) ∧ (L.mul L').Ok P ∧ mulF B.ν (fm S P B e L) (fm S P B e L') = fm S P B e (L.mul L') ∧
      L.adj.Ok P ∧ adjF (fm S P B e L) = fm S P B e L.adj

def FmTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) →
  ∀ (L : LM κ B.a B.b) (N : ∀ w, κ w → κ w → ℂ), L.Ok P → IsTestP (L.tr P N) ∧
    ∀ h, ∑ x, ∑ y, fm S P B e L x y h * tenN P B e N y x = B.vol⁻¹ * finFn S (L.tr P N) L.t h

def RtAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E),
  (∀ ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), mulF B.ν ψ (rt u₁ u₂ ψ') = rt u₁ u₂ (mulF B.ν ψ ψ')) ∧
  (∀ t : PT B, t.Ok → ∃ r, PT.Ok { t with ψ := rt u₁ u₂ t.ψ, r := r }) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → ∃ r, 0 ≤ r ∧
    ∀ x y h, ψ x y h ≠ 0 → logSize (finGL E B.a h.1) ≤ r ∧ logSize (finGL E B.b h.2) ≤ r

def lmWd {κ : Pl E → Type} [∀ w, Fintype (κ w)] {B : Block E} (Lo : PT B → LM κ B.a B.b) (w : List (BGen B))
    (L₀ : LM κ B.a B.b) : LM κ B.a B.b := w.foldr (fun g L => Sum.elim (fun _ => L) (fun s => (Lo s).mul L) g) L₀

def AdelRep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) →
  ∀ (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E) (Ta : Ops B.Ma) (Tb : Ops B.Mb) (N : ∀ w, κ w → κ w → ℂ)
    (Lo : PT B → LM κ B.a B.b) (w : List (BGen B)) (t₀ : PT B) (L₀ : LM κ B.a B.b),
    (∀ s, Sum.inr s ∈ w → (Lo s).Ok P ∧ s.ψ = fm S P B e (Lo s)) → L₀.Ok P → t₀.ψ = rt u₁ u₂ (fm S P B e L₀) →
    (lmWd Lo w L₀).Ok P ∧ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e (lmWd Lo w L₀)) ∧
      trM (BGen.wd w t₀).Φ (opM Ta Tb (tenN P B e N)) =
        B.vol⁻¹ • adel S u₁ u₂ ((BGen.wd w t₀).arch Ta Tb) ((lmWd Lo w L₀).tr P N) (lmWd Lo w L₀).t

def VCAll (B : Block E) (Ta : Ops B.Ma) (Tb : Ops B.Mb) : Prop :=
  (∀ v k val T, IsMult B.μa (B.Ma v) k val T → VeryCusp (phiOf (B.Ma v) (Ta v) k)) ∧
    ∀ v k val T, IsMult B.μb (B.Mb v) k val T → VeryCusp (phiOf (B.Mb v) (Tb v) k)

def RegOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (u₁ : GL (Fin a) E)
  (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ → ∀ φ₁ φ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ →
  (∃ w ∈ S, ¬ IsSplitAt w ∧ RegAt2 a b w (φ₁ w)) →
  (∀ d x h₂, finFn S φ₁ φ₂ ((gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d) ∧
  ∀ d x h₁, finFn S φ₁ φ₂ ((h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d

def PTTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E), ∃ c : ℝ, 0 ≤ c ∧
  ∀ (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (e : B.κ ≃ ∀ w : P, κ w), IsSection S →
  (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) → ∀ (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ (Ta : Ops B.Ma) (Tb : Ops B.Mb) (N : ∀ w, κ w → κ w → ℂ) (t : PT B) (L : LM κ B.a B.b), VCAll B Ta Tb → t.Ok → L.Ok P →
    t.ψ = rt u₁ u₂ (fm S P B e L) → (∃ w ∈ S, ¬ IsSplitAt w ∧ RegAt2 B.a B.b w (L.tr P N w)) →
    D4.IsTest2J (trM t.Φ (opM Ta Tb (tenN P B e N))) (c * (1 + t.T) + t.r)

def EllLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (J : Type) (s : Finset J) (c : J → ℂ)
  (φ : J → GA E a × GA E b → ℂ) (r : ℝ), 0 ≤ r → (∀ j ∈ s, D4.IsTest2J (φ j) r) →
    ellSum2 μ₁ μ₂ (∑ j ∈ s, c j • φ j) = ∑ j ∈ s, c j * ellSum2 μ₁ μ₂ (φ j)

def GrowthAt (B : Block E) [MeasurableSpace (GA E B.a)] [MeasurableSpace (GA E B.b)] (μ₁ : Measure (GA E B.a))
    (μ₂ : Measure (GA E B.b)) : Prop :=
  ∀ (Φ₁ Φ₂ : Matrix B.I B.I (H E B.a B.b → ℂ)) (T₁ T₂ : B.Hb →L[ℂ] B.Hb) (M : Matrix B.I B.I ℂ) (r₀ r₁ : ℝ), IsTestM Φ₁ →
    IsTestM Φ₂ → IsROp B.D Φ₁ T₁ → IsROp B.D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ) (U : B.Hb →L[ℂ] B.Hb)
      (Φ : Matrix B.I B.I (H E B.a B.b → ℂ)), IsTestM Φ → IsROp B.D Φ (T₁ * U * T₂) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → ‖ellSum2 μ₁ μ₂ (trM Φ M)‖ ≤ C * (1 + k) ^ N * ‖U‖

def BlockEllipticGrowth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (B : Block E)
  [MeasurableSpace (GA E B.a)] [BorelSpace (GA E B.a)] [MeasurableSpace (GA E B.b)] [BorelSpace (GA E B.b)]
  (μ₁ : Measure (GA E B.a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E B.b)) [μ₂.IsHaarMeasure], GrowthAt B μ₁ μ₂ →
  ∀ (M : Matrix B.I B.I ℂ) (t₁ t₂ : PT B) (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (BGen B)) (c₀ : ℝ), 0 ≤ c₀ →
    t₁.Ok → t₂.Ok → (∀ j, ∀ g ∈ w j, g.Ok) →
    ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ,
      (∀ f : Fin k → J, ∀ t, t = BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂ →
        D4.IsTest2J (trM t.Φ M) (c₀ * (1 + t.T) + t.r)) →
      ‖∑ f : Fin k → J, (∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten *
          ellSum2 μ₁ μ₂ (trM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ M)‖ ≤
        C * (1 + k) ^ N * ‖(∑ j, c j • ((w j).map BGen.op).prod) ^ k‖

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

def OpNeOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E), 1 ≤ B.a + B.b → Nontrivial B.Hb →
  ∀ t : PT B, t.Ok → t.op ≠ 1

def AdjKer0 : Prop := ∀ (n : ℕ) (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : KMod n) (g : ℝ → ℝ) (T : ℝ)
  (k : Mat n → (M.V →L[ℂ] M.V)), IsBump g T → IsKer μ M [] g k →
    IsKer μ M [] g (haveI := FiniteDimensional.complete ℂ M.V; fun y => ContinuousLinearMap.adjoint (k y⁻¹))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E}

def PT.pw (t : PT B) (m : ℕ) : PT B := BGen.wd (List.replicate m (Sum.inr t)) t

def PT.adj' (t : PT B) : PT B := { t.adj with va := t.va, vb := t.vb }

def PT.sq (t : PT B) (m : ℕ) : PT B := (t.adj'.pw m).mul (t.pw m)

def SqOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B) (g : ℝ → ℝ) (m : ℕ), t.Ok →
  IsBump g t.T → (∀ v, IsKer B.μa (B.Ma v) [] g (t.ka v) ∧ ∀ χ, t.va v χ = coshT g (cas χ)) →
  (∀ v, IsKer B.μb (B.Mb v) [] g (t.kb v) ∧ ∀ χ, t.vb v χ = coshT g (cas χ)) →
  (t.pw m).Ok ∧ (t.pw m).op = t.op ^ (m + 1) ∧ (t.sq m).Ok ∧ (t.sq m).op = star (t.op ^ (m + 1)) * t.op ^ (m + 1) ∧
    (∀ χa χb, (t.sq m).val χa χb = t.val χa χb ^ (2 * (m + 1))) ∧
    (t.sq m).ψ = mulF B.ν (t.adj'.pw m).ψ (t.pw m).ψ

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Shuf (n : ℕ) where
  a : ℕ
  b : ℕ
  e : Fin a ⊕ Fin b ≃ Fin n
  monoL : StrictMono fun i : Fin a => e (Sum.inl i)
  monoR : StrictMono fun j : Fin b => e (Sum.inr j)
  eps : Fin n → ℂˣ

def resL (s : Shuf n) (x : Fin n → ℤ) : Fin s.a → ℤ := fun i => x (s.e (Sum.inl i))
def resR (s : Shuf n) (x : Fin n → ℤ) : Fin s.b → ℤ := fun j => x (s.e (Sum.inr j))

def qU (w : Pl E) (k : ℤ) : ℂˣ := if h : (qh w : ℂ) ≠ 0 then Units.mk0 _ h ^ k else 1

def chiOf (w : Pl E) (s : Shuf n) (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) : Fin n → ℂˣ :=
  fun k => s.eps k * Sum.elim (fun i => ξa i * qU w ((s.a : ℤ) - 1 - 2 * (i : ℕ)))
    (fun j => ξb j * qU w ((s.b : ℤ) - 1 - 2 * (j : ℕ))) (s.e.symm k)

def ChiEval : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) (x : Fin n → ℤ),
  ((∏ k, s.eps k ^ x k : ℂˣ) : ℂ) * ev2 w ξa ξb (resL s x) (resR s x) = ((∏ k, chiOf w s ξa ξb k ^ x k : ℂˣ) : ℂ)

def GapRes : Prop := ∀ (n : ℕ) (s : Shuf n) (x : Fin n → ℤ), x ∈ coneGL n 2 → Gap (resL s x) ∧ Gap (resR s x)

def ChoiceT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ι : Type) [Fintype ι]
  (s : ι → Shuf n) (Z : ∀ i, Set ((Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ))) (α : Fin n → ℂˣ), (∀ i, (Z i).Finite) →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) ∧ evalGL c α = 1 ∧
    ∀ i, ∀ p ∈ Z i, (c.sum fun x a => a * ((∏ k, (s i).eps k ^ x k : ℂˣ) : ℂ) *
        ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x)) ≠ 0 → chiOf w (s i) p.1 p.2 = α

def ChoiceS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (GLw n w)),
  IsOpen (K' : Set (GLw n w)) → IsCompact (K' : Set (GLw n w)) → ∀ P : SmIrr (GLw n w), (∃ v ∈ fixed P.ρ K', v ≠ 0) →
  ∀ (k : ℕ) (D : Fin k → Pre E n),
  ∃ e : GLw n w → ℂ, IsHk K' e ∧ (∃ v₀ ∈ fixed P.ρ K', ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed P.ρ K', hk P.ρ K' e v = l v • v₀) ∧
    ∀ j, ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (D j) w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0

def ChoiceTOf : Prop := PeakCone → ChiEval → GapRes → ChoiceT

end PositivityTheory.Rg.BcB.F.Choice

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure GenIn (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) where
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  B : ι → Block E
  I : Type
  [fI : Fintype I]
  d : ℕ
  blk : Fin d → I
  Γ : Type
  g : Γ → ∀ s, BGen (B s)
  c : Γ → I → ℂ
  β : ∀ s, PT (B s)
  m : ℕ
  u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)
  v : EuclideanSpace ℂ (Fin d)
  i₀ : I
  a₀ : Γ
  ok : ∀ x s, (g x s).Ok
  βok : ∀ s, (β s).Ok
  comm : ∀ x y s, Commute (g x s).op (g y s).op
  commStar : ∀ x y s, Commute (g x s).op (star (g y s).op)
  βcomm : ∀ s x, Commute (β s).op (g x s).op ∧ Commute (β s).op (star (g x s).op)
  ucomm : ∀ x, Commute u (Eig.diagOp blk (c x)) ∧ Commute u (star (Eig.diagOp blk (c x)))
  v_ne : v ≠ 0
  uv : u v = v
  vblk : ∀ x, Eig.diagOp blk (c x) v = c x i₀ • v ∧ star (Eig.diagOp blk (c x)) v = starRingEnd ℂ (c x i₀) • v
  a₀ne : c a₀ i₀ ≠ 0

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

def GBound (gen : Γ → Prod' H d) (a₀ : Γ) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
    (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ a ∈ StarAlgebra.adjoin ℂ (Set.range gen), (∃ b ∈ StarAlgebra.adjoin ℂ (Set.range gen), a = b * gen a₀) →
    ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
      ‖LinearMap.trace ℂ _ (((u * a.2) ^ k : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))‖ ≤
        C * (1 + k) ^ N * Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖)

def GRead (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (Q : Prop) : Prop :=
  ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ
      (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {star (β s ^ m) * β s ^ m})
        →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
    (∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c) →
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → Q

end Generic

namespace GenIn

variable {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (HeightOneSpectrum (𝓞 E))}
  {K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E))} {W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)}
  (G : GenIn π S T K W)

attribute [instance] GenIn.ft GenIn.ne GenIn.fI

abbrev H (s : G.ι) : Type := (G.B s).Hb

instance instNH (s : G.ι) : NormedAddCommGroup (G.H s) := inferInstanceAs (NormedAddCommGroup (G.B s).Hb)
instance instIH (s : G.ι) : InnerProductSpace ℂ (G.H s) := inferInstanceAs (InnerProductSpace ℂ (G.B s).Hb)
instance instCH (s : G.ι) : CompleteSpace (G.H s) := inferInstanceAs (CompleteSpace (G.B s).Hb)

def gen (x : G.Γ) : Prod' G.H G.d := (fun s => (G.g x s).op, Eig.diagOp G.blk (G.c x))

def βop (s : G.ι) : G.H s →L[ℂ] G.H s := (G.β s).op

def Bound : Prop := GBound (H := G.H) G.gen G.a₀ G.βop G.m G.u

def Read : Prop := GRead (H := G.H) G.gen G.βop G.m G.v (∃ D : Pre E n, TOut π S T K W D)

def DiagComm : Prop := ∀ (I : Type) (d : ℕ) (blk : Fin d → I) (c c' : I → ℂ),
  Commute (Eig.diagOp blk c) (Eig.diagOp blk c') ∧ Commute (Eig.diagOp blk c) (star (Eig.diagOp blk c'))

end GenIn

def GenToData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
  (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (G : GenIn π S T K W), GenIn.DiagComm → G.Bound → G.Read →
  Nonempty (RunData π S T K W)

def GenEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∃ G : GenIn π S T K W, G.Bound ∧ G.Read

theorem dataEx_of (h0 : GenIn.DiagComm) (h1 : GenToData) (h2 : GenEx) : DataEx := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW, hT⟩ := h2 E hE n hn π hπ S hS
  exact ⟨K, W, hK, hW, fun T => let ⟨G, hb, hr⟩ := hT T; h1 E n π S T K W G h0 hb hr⟩

end PositivityTheory.Rg.BcB.F

end
end
