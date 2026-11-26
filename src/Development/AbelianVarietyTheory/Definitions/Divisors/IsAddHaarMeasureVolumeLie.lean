module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ContDiff

namespace GlobalTheory.JSW

def schur (n : ℕ) (l : Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))

def schurAt {n : ℕ} (l : Fin n → ℕ) (α : Fin n → ℂ) : ℂ := MvPolynomial.eval₂ (Int.castRingHom ℂ) α (schur n l)

def sphW (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (l : Fin n → ℕ) : ℂ :=
  if Antitone l then
    (q : ℂ) ^ (-(∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (l i : ℂ))) / 2) * schurAt l α
  else 0

theorem schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · simp
  · intro i j h
    have h' : (j : ℕ) < i := h
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

theorem sphW_of_not_antitone (q : ℕ) {n : ℕ} (α : Fin n → ℂ) {l : Fin n → ℕ} (h : ¬ Antitone l) : sphW q α l = 0 :=
  if_neg h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open GlobalTheory.CuspRep


omit [_root_.NumberField.IsTotallyComplex E] in
instance isAddHaarMeasure_volume_lie : Measure.IsAddHaarMeasure (volume : Measure (Lie E a)) :=
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin a → Cinf E)) := Measure.pi.isAddHaarMeasure _
  Measure.pi.isAddHaarMeasure _

def smoothInf (f : Lie E a → ℂ) (φ : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, f x * chart φ g x

def IsTestInf (f : Lie E a → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E a

def smoothSpan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (f : Lie E a → ℂ) (φ : Sm E a), IsTestInf f ∧ φ ∈ π.V ∧ F = smoothInf f φ.1}



omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isTestInf {y : Lie E a} (hy : y ∈ invSet E a) {U : Set (Lie E a)} (hU : U ∈ nhds y) :
    ∃ ρ : Lie E a → ℝ, IsTestInf (fun x => (ρ x : ℂ)) ∧ tsupport ρ ⊆ U ∧ (∀ x, ρ x ∈ Set.Icc (0 : ℝ) 1) ∧ ρ y = 1 := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := invSet E a ∩ U) (x := y)
    (Filter.inter_mem (isOpen_invSet.mem_nhds hy) hU)
  refine ⟨f, ⟨Complex.ofRealCLM.contDiff.comp h3, h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp), ?_⟩,
    h1.trans Set.inter_subset_right, fun x => h4 ⟨x, rfl⟩, h5⟩
  exact (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) f).trans (h1.trans Set.inter_subset_left)

theorem smoothInf_rt_fin (f : Lie E a → ℂ) (φ : GA E a → ℂ) (k : GL (Fin a) (Af E)) (g : GA E a) :
    smoothInf f (fun x => φ (x * finGL E a k)) g = smoothInf f φ (g * finGL E a k) := by
  simp only [smoothInf, chart_rt_fin]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
noncomputable section

open WeierstrassCurve
open scoped IntermediateField

namespace GlobalTheory.CMModel

def Stable (L : PeriodPair) (F : IntermediateField ℚ ℂ) {ι : Type} (T : ι → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι, ∀ i, GlobalTheory.ConjPoint.IsConj L L σ (T i) (T (e i))

def IntV (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) : Prop :=
  W.a₁ ∈ V ∧ W.a₂ ∈ V ∧ W.a₃ ∈ V ∧ W.a₄ ∈ V ∧ W.a₆ ∈ V

def ModelAt (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (W : WeierstrassCurve ℂ) (D : ℂ) : Prop :=
  ∃ C : VariableChange ℂ, (C.u : ℂ) ∈ F ∧ C.r ∈ F ∧ C.s ∈ F ∧ C.t ∈ F ∧ IntV V (C • W) ∧
    V.valuation (C • W).Δ = V.valuation D

abbrev Sq (p : ℕ) : Type := {k : Fin p // ((k : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((k : ℕ) : ZMod p)}


open Classical in
instance (p : ℕ) : Fintype (Sq p) := Subtype.fintype _

def sqPt (p : ℕ) (t : ℂ) (k : Sq p) : ℂ := ((k.1 : ℕ) : ℂ) * t

def sqProd (p : ℕ) (L : PeriodPair) (t : ℂ) : ℂ := ∏ k : Sq p, L.derivWeierstrassP (sqPt p t k)

def shortTwist {R : Type} [CommRing R] (d a₄ a₆ : R) : WeierstrassCurve R := ⟨0, 0, 0, d ^ 2 * a₄, d ^ 3 * a₆⟩

structure Datum (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ) : Prop where

  mul : Formalism.L2.Th1.F.MulStable L (GlobalTheory.Published.sqrtNegNat p)

  g₂_mem : L.g₂ ∈ F

  g₃_mem : L.g₃ ∈ F

  notMem : t ∉ L.lattice

  ker : GlobalTheory.Published.sqrtNegNat p * t ∈ L.lattice

end GlobalTheory.CMModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical

noncomputable section

namespace GlobalTheory.Mean4

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev Wt : Type := D.what₂.Tau → Fin Y.N → ℝ

abbrev Fn : Type := Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ

structure SlopeTestRemainingChoices where

  dir : Wt Y

  w : Y.Comp → ℝ

  Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ

  ht : Y.ALB → Y.Pt → ℝ

  dense : Y.Comp → Set Y.Pt → Prop

def testI : ℝ := ∑ τ, degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)

variable {Y} (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y)


end GlobalTheory.Mean4
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField

noncomputable section

namespace GlobalTheory.MeanTop

structure Wts (ι : Type) (N : ℕ) where

  kc : ℕ

  p : ℕ

  T : ℕ

  Dd : ℕ

  c0 : ℤ

  h0 : ℤ

  S : ℝ

  eta : ℝ

  b : ℝ

  w : ι → ℝ

  u : ι → Fin N → ℤ

  u1 : ι → Fin N → ℤ

namespace Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

def u' : ι → Fin N → ℤ := fun τ i => if (i : ℕ) < W.p then W.u1 τ i else W.u1 τ i + 3 * (N : ℤ)

def g : ℝ := (W.h0 : ℝ) / (4 * W.T)

def IsDiv : Prop :=
  ∀ τ, (∀ a : Fin N, (a : ℕ) + 1 = W.kc → W.u1 τ a = 0) ∧ ∀ a b : Fin N, (b : ℕ) = a + 1 →
    W.u1 τ a - W.u1 τ b =
      (W.u τ a - W.u τ b + if (b : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) / ((W.T : ℤ) + W.Dd + 1)

structure Hyp : Prop where
  kc_pos : 1 ≤ W.kc
  kc_lt : W.kc < W.p
  p_lt : W.p < N
  small : N - W.p < W.p
  weightConst_nonneg : 0 ≤ W.c0
  anchor : ∀ τ (a : Fin N), (a : ℕ) + 1 = W.kc → W.u τ a = 0
  h1 : 4 * W.Dd + 4 ≤ W.T
  h2 : 4 * (W.c0 + 2 * N + W.T + W.Dd + 1) ≤ W.h0 ∧ 24 * (N : ℤ) * W.T ≤ W.h0
  h3node : ∀ τ (a : Fin N), W.kc ≤ (a : ℕ) → |(W.u τ a : ℝ) + W.w τ| ≤ W.eta + W.S + N
  h3cloud : ∀ τ (a : Fin N), (a : ℕ) < W.kc → 0 ≤ W.u τ a ∧ (W.u τ a : ℝ) ≤ W.S
  h3w : ∀ τ, 4 * ((W.eta + W.S + N) + W.S + W.c0 + 2 * N) + 20 * N * W.T ≤ W.w τ
  h4 : ∀ τ (a b : Fin N), (b : ℕ) = a + 1 →
    ((b : ℕ) ≠ W.p → ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) ≤ W.u τ a - W.u τ b + 2) ∧
    (W.kc ≤ (a : ℕ) → W.h0 - 1 ≤ W.u τ a - W.u τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ W.u τ a - W.u τ b)
  h5 : ∀ τ a, |(W.u τ a : ℝ)| + W.c0 + 4 * N ≤ 2 * W.b

end Wts

def l1 {ι : Type} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℤ) : ℝ := ∑ τ, ∑ i, |(v τ i : ℝ)|

def reWt {ι : Type} {N : ℕ} (v : ι → Fin N → ℤ) : ι → Fin N → ℝ := fun τ i => (v τ i : ℝ)

def vDiff (D : D7) (p : ℕ) : ℝ := (padicValNat p (WeightThresholdDefs.dE D) : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

structure Shifts where

  Pe : Finset ℕ

  e : ℕ → ℝ

  C7 : ℝ

  Pa : ℝ

  Pinf : ℝ

  PPe : ℝ

  XW : ℝ

variable {D : D7} (Y : ShimX D.what₂.Tau) {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

def bZero (W : Wts D.what₂.Tau Y.N) : ℝ := WeightThresholdDefs.bigB0 Y (reWt W.u') W.g

def totalShift (W : Wts D.what₂.Tau Y.N) (A : Shifts) : ℝ :=
  (∑ p ∈ A.Pe, A.e p * Real.log p) +
    (∑ p ∈ GlobalTheory.FlagAr.setB Y (bZero Y W), (WeightThresholdDefs.cP p + A.C7 * vDiff D p) * (l1 W.u' + A.Pa) * Real.log p) +
    (l1 W.u1 + 6 * A.Pinf) / 2

end GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Inhab

open Filter Topology

def wts (ι : Type) (N kc p T Dd c0 G V : ℕ) (b : ℝ) : Wts ι N where
  kc := kc
  p := p
  T := T
  Dd := Dd
  c0 := c0
  h0 := ((T : ℤ) + Dd + 1) * G - 1
  S := ((T : ℝ) + Dd + 1) * G * N
  eta := 2 * N + c0
  b := b
  w := fun _ => ((T : ℝ) + Dd + 1) * V
  u := fun _ i => (((T : ℤ) + Dd + 1) * G - 1) * ((kc : ℤ) - 1 - (i : ℕ)) -
    (if kc ≤ (i : ℕ) then ((T : ℤ) + Dd + 1) * V else 0) - (if p ≤ (i : ℕ) then 2 * (N : ℤ) + c0 else 0)
  u1 := fun _ i => (G : ℤ) * ((kc : ℤ) - 1 - (i : ℕ)) - (if kc ≤ (i : ℕ) then (V : ℤ) else 0)

theorem dividedWeight_unique {ι : Type} {N : ℕ} (W : Wts ι N) (v : ι → Fin N → ℤ) (hk : 1 ≤ W.kc) (hN : W.kc ≤ N) (h : W.IsDiv)
    (h' : Wts.IsDiv { W with u1 := v }) : v = W.u1 := by
  funext τ
  have step : ∀ a c : Fin N, (c : ℕ) = a + 1 → v τ a - W.u1 τ a = v τ c - W.u1 τ c := fun a c hc => by
    have e1 := (h τ).2 a c hc
    have e2 := (h' τ).2 a c hc
    simp only at e2
    omega
  have hN0 : 0 < N := by omega
  have all : ∀ n (hn : n < N), v τ ⟨n, hn⟩ - W.u1 τ ⟨n, hn⟩ = v τ ⟨0, hN0⟩ - W.u1 τ ⟨0, hN0⟩ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [← ih (by omega)]; exact (step ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl).symm
  have a1 := (h τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  have a2 := (h' τ).1 ⟨W.kc - 1, by omega⟩ (by simp only; omega)
  simp only at a2
  have a3 := all (W.kc - 1) (by omega)
  funext i
  have a4 := all i i.isLt
  simp only [Fin.eta] at a4
  omega

theorem f_pos (D : D7) : 1 ≤ D.R.f := by
  have := D.R.two_le_m
  have := D.R.m_le_f
  show 1 ≤ 2 * D.R.ord
  omega

end GlobalTheory.MeanTop.Inhab
end
end
