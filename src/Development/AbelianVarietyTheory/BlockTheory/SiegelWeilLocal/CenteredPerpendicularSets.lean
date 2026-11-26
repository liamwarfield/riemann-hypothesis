module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def perpSet (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ w ∈ W, Formalism.UG.hform s J w y = 0}

def IsSkew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ u u' : Fin n → A, Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') = 0

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  IsSkew s J Y ∧ (∀ u, Y *ᵥ u ∈ perpSet s J W) ∧ (∀ u ∈ perpSet s J W, Y *ᵥ u ∈ W) ∧ ∀ u ∈ W, Y *ᵥ u = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ u ∈ perpSet s J W, Y *ᵥ u = 0

end Lie

variable (I : AutInst)

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set _))

def nilReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def cenInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def diagEmb (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normAt (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

end GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
open NumberField Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

open Formalism.MainNotions.S

def gLie {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Formalism.REAL.inG ε X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * a) + (bᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [Formalism.REAL.inG]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha, smul_zero]

def expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp (X : Matrix (Fin n) (Fin n) ℂ)).unit, Formalism.REAL.f1alg_exp_inUJ ε X.1 X.2⟩

@[simp] theorem uMat_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) :
    uMat (expU X) = NormedSpace.exp (X : Matrix (Fin n) (Fin n) ℂ) := rfl

def IsONBasis {n m : ℕ} {ε : Fin n → Bool} (E : Fin m → gLie ε) : Prop :=
  (∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
      if i = j then 1 else 0) ∧
    Submodule.span ℝ (Set.range E) = ⊤

variable (B : RowsAut)

abbrev gInf : Type := ∀ v : InfinitePlace B.I.F, gLie (B.I.ε v)


open Classical in
def atPlace (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) : gInf B := Pi.single v X

def orbit (E : gInf B) (w : B.Hs) (t : ℝ) : B.Hs := B.σs (fun v => expU (t • E v)) w

def dAct (E : gInf B) (w : B.Hs) : B.Hs := deriv (orbit B E w) 0

def wordAct (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (w : B.Hs) : B.Hs :=
  l.foldr (fun X y => dAct B (atPlace B X.1 X.2) y) w

def VP (P : ℕ) : Submodule ℂ B.Hs :=
  Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (u : ∀ v, B.H v),
    l.length ≤ P ∧ (∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧ y = wordAct B l (B.tens u)}

def beP (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def StepBoundAt (b : ℝ) (P : ℕ) : Prop :=
  FiniteDimensional ℂ (VP B P) ∧
  (∀ k : B.I.Ginf, (∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) → ∀ w ∈ VP B P, B.σs k w ∈ VP B P) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P, DifferentiableAt ℝ (orbit B E w) 0) ∧
  (∀ (v : InfinitePlace B.I.F) (m : ℕ) (E : Fin m → gLie (B.I.ε v)), IsONBasis E → ∀ w ∈ VP B P,
    ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ beP B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧
  (∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
    ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P,
    ‖dAct B E w‖ ≤ Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖) ∧
  ∀ (E : gInf B), ∀ w ∈ VP B P, dAct B E w ∈ VP B (P + 1)

variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.stepSpan_mono {P Q : ℕ} (h : P ≤ Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ≤ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B Q :=
  Submodule.span_mono fun _ ⟨l, u, hl, hu, hy⟩ => ⟨l, u, hl.trans h, hu, hy⟩


variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem {d : InfinitePlace B.I.F → ℝ}
    (h : _root_.GlobalTheory.Count.IsDSData B d) (P : ℕ) :
    B.tens B.w ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ∧ ‖B.tens B.w‖ = 1 := by
  have hd := h
  unfold _root_.GlobalTheory.Count.IsDSData at hd
  have hunit : ∀ v, ‖B.w v‖ = 1 ∧ B.w v ∈ _root_.Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) := fun v => by
    have hv := (hd v).2.2.1
    unfold _root_.Formalism.MainNotions.S.IsLowUnit at hv
    exact hv
  refine ⟨Submodule.subset_span ⟨[], B.w, Nat.zero_le _, fun v => (hunit v).2, rfl⟩, ?_⟩
  have hs := B.tens_spec
  unfold _root_.Formalism.MainNotions.S.AutInst.IsHilbTensor at hs
  have hinner : inner ℂ (B.tens B.w) (B.tens B.w) = 1 := by
    rw [hs.1]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (hunit v).1]
    simp
  have hsq : ‖B.tens B.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner, RCLike.one_re]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
open Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

open Formalism.MainNotions.S

section Defs

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def orbit (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : ℝ → H :=
  fun t => σ (NormedSpace.exp ((t : ℂ) • X)) v

def dAct (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (orbit σ X v) 0

def IsDiffVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∀ X, Formalism.REAL.inG ε X → DifferentiableAt ℝ (orbit σ X v) 0

def dWord (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : H :=
  l.foldr (dAct σ) v

def stepSpace (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : ℕ) :
    Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ P ∧
    (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u}

def IsONFamily (ε : Fin n → Bool) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, Formalism.REAL.inG ε (E i)) ∧ ∀ i j, (Matrix.trace (E i * (E j)ᴴ)).re = if i = j then 1 else 0

def stepConst (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 + 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) + 3 * (P : ℝ)

theorem stepSpace_zero (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    stepSpace ε lam σ 0 = lowKSub ε lam σ := by
  have : {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ 0 ∧
      (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u} = (lowKSub ε lam σ : Set H) := by
    ext v
    constructor
    · rintro ⟨l, u, hl, -, hu, rfl⟩
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this
      exact hu
    · intro hv
      exact ⟨[], v, le_rfl, by simp, hv, rfl⟩
  rw [stepSpace, this, Submodule.span_eq]

theorem stepSpace_mono (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Monotone (stepSpace ε lam σ) := by
  intro P Q h
  refine Submodule.span_mono ?_
  rintro v ⟨l, u, hl, h1, h2, h3⟩
  exact ⟨l, u, hl.trans h, h1, h2, h3⟩

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CuspidalFrames
open MeasureTheory NumberField
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames

open Formalism.MainNotions.S GlobalTheory.Count

def IsCuspidalFrame (B : RowsAut) (Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) : Prop :=
  (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
    (∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R) ∧
    (∀ i u, ‖T i u‖ = ‖u‖) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧
    Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re ∧
    (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) ∧
    (∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u) ∧
    Orthonormal ℂ (fun i => T i (B.tens B.w)) ∧
    Submodule.span ℂ (Set.range fun i => T i (B.tens B.w)) = LinearMap.range Rφ.toLinearMap

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound

open Formalism.MainNotions.S GlobalTheory.Count

def dimN (B : RowsAut) : ℕ := B.I.n ^ 2 * B.I.f

def stepBe (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def radRh (B : RowsAut) (q : ℕ) (τ : ℝ) : ℝ :=
  (B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * τ) ^ ((1 : ℝ) / q) / 4

def DeepKernelBound : Prop :=
  ∀ (Cg : ℝ) (n₀ : ℕ) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA),
    0 ≤ Cg → 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b →
    (∀ v, IsGauge (B.I.ε v) (c v)) →
    least B.I x < tauStar B q b →
    (kern B.I (phe B d) x x).re ≤
      (2 * radRh B q (least B.I x) * Real.sqrt B.I.f *
            stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ (16 * q * dimN B) *
        (6 * stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ dimN B *
        Real.exp B.I.f *
        (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * dimN B) *
        (B.D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal

end GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA := {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def nearNe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | IsNear B d (epN B) x γ ∧ γ ≠ 1}

def nearAbs (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : nearNe B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def nearBound (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) * mainTerm B d

def NearModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, nearAbs B d x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (nearBound B d)

theorem nearAbs_eq_zero (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (h : ∀ γ, IsNear B d (epN B) x γ → γ = 1) : nearAbs B d x = 0 := by
  haveI : IsEmpty (nearNe B d x) := ⟨fun γ => γ.2.2 (h γ.1 γ.2.1)⟩
  simp [nearAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RareFlags

open Formalism.MainNotions.S GlobalTheory.Count

def FlagRare : Prop :=
  ∃ n₀ : ℕ, ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → n₀ ≤ B.I.n → q ^ 2 ≤ B.I.n →
    Real.log B.I.rd ≤ Real.exp B.I.n → Real.log B.I.f ≤ Real.sqrt B.I.n →
    prob B {x | least B.I x < 1 / 2} ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n))

end GlobalTheory.IndefiniteRowSideFullHecke.RareFlags
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepSet

open Formalism.MainNotions.S GlobalTheory.Count

def deepSet (B : RowsAut) (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ least B.I x < tauStar B q b}

def DeepBound : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.DeepSet
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def farSet (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d (epN B) x γ}

def farSum (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : farSet B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def FarModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, farSum B d x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate
end
end
