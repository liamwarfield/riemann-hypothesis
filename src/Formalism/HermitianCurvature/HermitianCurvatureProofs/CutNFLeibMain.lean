module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def ThChain (Ψ : ℕ → ℝ → ℝ) : Prop := ∀ (n : ℕ) (x : ℝ), 0 < x → HasDerivAt (Ψ n) (Ψ (n + 1) x / x) x

section leibterm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def LeibTerm (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq) (T' : B.DTerm k r Wp Wq) : Prop :=
  ∃ T ∈ Dop, ∃ (P : B.Mat k r → ℂ) (j : ℕ), ListSumSplittings.PolyClass ((2 * r + 2) * T.word.length) P ∧
    T'.word.Sublist T.word ∧
    ∀ g ∈ C6.domL Bs ∅, T'.coef g = (P g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ j) • T.coef g

end leibterm

def NFLeibExp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) →
    ∃ terms : List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
              ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x)).sum

def NFLeibOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq),
    B.SmoothCoef (C6.domL Bs ∅) Dop →
    ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp k r Wp Wq),
      (∀ q, B.SmoothCoef (C6.domL Bs ∅) (L q)) ∧ (∀ q, ∀ T' ∈ L q, LeibTerm Bs Dop T') ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.opApply Dop (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (L q) F x

def NFLeibBd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq) (o κ : ℕ) (Dop : B.DiffOp k r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) → C6.InDDPlus Bs fib ∅ o κ Dop →
    ∀ L : B.DiffOp k r Wp Wq, (∀ T' ∈ L, LeibTerm Bs Dop T') →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply L F g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A)

def NFVLin : Prop :=
  ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (Q : ℕ) (c : Fin (Q + 1) → ℝ → ℂ)
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (Hq : Fin (Q + 1) → B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    (∀ q, ContinuousOn (Hq q) (B.GPos Bs)) →
    (∀ q, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g → ‖Hq q g‖ ≤ C * B.gN g ^ (-A)) →
    (∀ g ∈ B.GPos Bs, H g = ∑ q, c q (Gf k r Bs.z Bs.z' g) • Hq q g) →
    ∀ γ : C.LPt, D.IsLocPt γ (r + 1) → 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ →
      D.vecV Bs ν' m₀ H γ = ∑ q, c q (D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ) • D.vecV Bs ν' m₀ (Hq q) γ

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp
namespace Formalism.FourierDecayAlt.P.CutBP.LeibExp

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Gc (z z' : Fin (2 * r + k + 1) → ℂ) : B.Mat k r → ℂ := fun g => ((Gf k r z z' g : ℝ) : ℂ)

theorem gc_poly (z z' : Fin (2 * r + k + 1) → ℂ) : ListSumSplittings.PolyClass (2 * r + 2) (Gc (k := k) (r := r) z z') := by
  apply ListSumSplittings.polyClass_of_isPolyDeg
  obtain ⟨q, hq, h⟩ := Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z'
  exact ⟨q, hq, h⟩

abbrev Tm (k r : ℕ) := ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)

def coefT (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (t : Tm k r) (y : B.Mat k r) : ℂ :=
  ((Ψ t.1 (Gf k r z z' y) : ℝ) : ℂ) * t.2.1 y * ((Gf k r z z' y : ℝ) : ℂ)⁻¹ ^ t.2.2.1

def step (z z' : Fin (2 * r + k + 1) → ℂ) (X : B.Mat k r) (t : Tm k r) : List (Tm k r) :=
  [(t.1 + 1, fun y => Formalism.REAL.RdV X (Gc z z') y * t.2.1 y, t.2.2.1 + 1, t.2.2.2),
   (t.1, Formalism.REAL.RdV X t.2.1, t.2.2.1, t.2.2.2),
   (t.1, fun y => (-(t.2.2.1 : ℂ)) * (Formalism.REAL.RdV X (Gc z z') y * t.2.1 y), t.2.2.1 + 1, t.2.2.2),
   (t.1, t.2.1, t.2.2.1, X :: t.2.2.2)]

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem term_deriv (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (hΨ : ThChain Ψ) (t : Tm k r)
    (hP : ListSumSplittings.PolyClass 0 t.2.1 ∨ B.CkOn ⊤ (B.GV k r) t.2.1)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) (hv : ∀ Y ∈ t.2.2.2, B.inLie k r Y)
    {X x : B.Mat k r} (hX : B.inLie k r X) (hxG : x ∈ B.GV k r) (hxp : 0 < Gf k r z z' x) :
    HasDerivAt (fun s : ℝ => coefT z z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
        B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
      (((step z z' X t).map fun t' => coefT z z' Ψ t' x • B.Rw t'.2.2.2 F x).sum) 0 := by
  obtain ⟨q, P, j, v⟩ := t
  simp only at hP hv ⊢
  have hPC : B.CkOn ⊤ (B.GV k r) P := by rcases hP with h | h; exact h.1; exact h
  set c : ℝ → B.Mat k r := fun s => x * NormedSpace.exp ((s : ℂ) • X) with hcdef
  have hc0 : c 0 = x := B5.curve_zero x X
  have hGc : HasDerivAt (fun s => Gc z z' (c s)) (Formalism.REAL.RdV X (Gc z z') x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (gc_poly z z').1) hxG hxG hX
  have hdiff : DifferentiableAt ℝ (fun s => Gf k r z z' (c s)) 0 := by
    have h1 : Differentiable ℝ (fun g : B.Mat k r => Gf k r z z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').differentiable (by simp)
    have h2 : Differentiable ℝ c := (B5.curve_contDiff x X).differentiable (by simp)
    exact (h1 (c 0)).comp (0 : ℝ) (h2 0)
  set dG : ℝ := deriv (fun s => Gf k r z z' (c s)) 0 with hdG
  have hGr : HasDerivAt (fun s => Gf k r z z' (c s)) dG 0 := hdiff.hasDerivAt
  have hD : Formalism.REAL.RdV X (Gc z z') x = (dG : ℂ) := by
    have h2 := hGr.ofReal_comp
    exact hGc.unique (by simpa [Gc] using h2)
  have hGx : Gf k r z z' (c 0) = Gf k r z z' x := by rw [hc0]
  have hne : Gf k r z z' (c 0) ≠ 0 := by rw [hGx]; exact hxp.ne'
  have hΨq : HasDerivAt (Ψ q) (Ψ (q + 1) (Gf k r z z' x) / Gf k r z z' x) (Gf k r z z' (c 0)) := by
    rw [hGx]; exact hΨ q _ hxp
  have hψ := (hΨq.comp (0 : ℝ) hGr).ofReal_comp
  have hPd : HasDerivAt (fun s => P (c s)) (Formalism.REAL.RdV X P x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top hPC) hxG hxG hX
  have hI := ((hGr.inv hne).pow j).ofReal_comp
  have hR : HasDerivAt (fun s => B.Rw v F (c s)) (Formalism.REAL.RdV X (B.Rw v F) x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (JFxI.ckOn_Rw_top' hF v hv)) hxG hxG hX
  have hA := ((hψ.mul hPd).mul hI).smul hR
  refine (hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [coefT, Function.comp_apply, Pi.pow_apply, Pi.inv_apply, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  simp only [step, coefT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc0,
    Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, hD]
  have hRw : B.Rw (X :: v) F x = Formalism.REAL.RdV X (B.Rw v F) x := rfl
  rw [hRw]
  rcases j with _ | j
  · push_cast
    module
  · simp only [Nat.add_sub_cancel]
    push_cast
    module

theorem exp_main (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) :
    ∃ terms : List (Tm k r),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => coefT Bs.z Bs.z' Ψ t x • B.Rw t.2.2.2 F x).sum := by
  induction w with
  | nil =>
    refine ⟨[(0, fun _ => 1, 0, [])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨le_rfl, ?_, List.Sublist.refl _⟩
      rw [List.length_nil, mul_zero]
      exact ListSumSplittings.polyClass_const 1
    · intro Ψ _ F _ x _
      simp [coefT, B.Rw]
  | cons X w ih =>
    have hwL : ∀ Y ∈ w, B.inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hXL : B.inLie k r X := hw X List.mem_cons_self
    obtain ⟨terms, hprop, hid⟩ := ih hwL
    refine ⟨terms.flatMap (step Bs.z Bs.z' X), ?_, ?_⟩
    · intro t' ht'
      rw [List.mem_flatMap] at ht'
      obtain ⟨t, ht, ht'⟩ := ht'
      obtain ⟨h1, h2, h3⟩ := hprop t ht
      have hGp := gc_poly (k := k) (r := r) Bs.z Bs.z'
      have hdeg : (2 * r + 2) * w.length ≤ (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      have hdeg2 : (2 * r + 2) + (2 * r + 2) * w.length = (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; ring
      simp only [step, List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2
      · exact ⟨by simp only [List.length_cons]; omega,
          ListSumSplittings.polyClass_mono hdeg (ListSumSplittings.polyClass_op h2 false hXL), h3.cons X⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_cmul _ (ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2)
      · exact ⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg h2, h3.cons_cons X⟩
    · intro Ψ hΨ F hF x hx
      have hVo : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
        isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
      have hloc := PositiveOrbitOpen.rdV_local (f₁ := B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y))
        (f₂ := fun y => (terms.map fun t => coefT Bs.z Bs.z' Ψ t y • B.Rw t.2.2.2 F y).sum) hVo
        (fun y hy hyG => hid Ψ hΨ F hF y ⟨hyG, hy, fun l hl => absurd hl (Finset.notMem_empty l)⟩) hXL x hx.2.1 hx.1
      change Formalism.REAL.RdV X (B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) x = _
      rw [hloc]
      have hd := JFxI.hasDerivAt_list_sum terms
        (fun t s => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
        (fun t => ((step Bs.z Bs.z' X t).map fun t' => coefT Bs.z Bs.z' Ψ t' x • B.Rw t'.2.2.2 F x).sum)
        (t := 0) (fun t ht => term_deriv Bs.z Bs.z' Ψ hΨ t (Or.inr (hprop t ht).2.1.1) F hF
          (fun Y hY => hwL Y ((hprop t ht).2.2.subset hY)) hXL hx.1 hx.2.1)
      change deriv (fun s : ℝ => (terms.map fun t => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))).sum) 0 = _
      rw [hd.deriv, sum_flatMap]

end

end Formalism.FourierDecayAlt.P.CutBP.LeibExp

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_expansion_holds : NFLeibExp := by
  unfold NFLeibExp
  intro k r Wp Wq _ _ _ _ Bs w hw
  exact LeibExp.exp_main Bs w hw

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibBd
open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibBd_term (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    (T' : B.DTerm k r Wp Wq) (hT' : LeibTerm Bs Dop T') {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖T'.coef g (B.Rw T'.word F g)‖ ≤
          K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
  obtain ⟨T, hT, Pc, j, hPc, hsub, hco'⟩ := hT'
  obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hIn.2.2 T hT
  set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef
  set c₀ : ℝ := min ε (ε ^ 2) with hc₀
  have hc₀p : 0 < c₀ := lt_min hε (by positivity)
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
      c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · simp at hl
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2
      exact (min_le_left _ _).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2
    have : ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
    exact (min_le_right _ _).trans this
  have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  set fo := (es.map fun e => e.2.length).sum with hfo
  obtain ⟨CP, hCP0, hCP⟩ := hPc.2 [] (fun x hx => by simp at hx)
  set D : ℕ := (2 * r + 2) * T.word.length with hD
  set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw
  have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
    obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
  have hεj : 0 ≤ (ε⁻¹) ^ j := by positivity
  refine ⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩
  have hgS : g ∈ S := ⟨hg, hgε⟩
  have hgp := P.BetaSesquilinearity.gN_pos hg
  have hg1 := P.BetaSesquilinearity.gN_ge_one hg
  have hGpos : 0 < Gf k r Bs.z Bs.z' g := lt_of_lt_of_le hε hgε
  have hgd : g ∈ C6.domL Bs ∅ := ⟨hg, hGpos, fun l hl => by simp at hl⟩
  have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
  have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
    have h := hUB [] hAdm0 g hgS
    have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
        (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
    rw [e] at h
    rw [hco g hgd]
    simpa using h
  have hb0 : 0 ≤ b := by
    have h := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    exact le_trans (by positivity) h
  have hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
    rw [P.BetaSesquilinearity.Rw_scale]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)
    have hl' : T'.word.length ≤ T.word.length := hsub.length_le
    have h := hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
    have e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g := rfl
    rw [e] at h
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
    exact h
  have hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D := by
    have := hCP g hg
    simpa [P.B4.W_nil] using this
  have hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j
  have hfo' : fo ≤ o := by omega
  have hwo : T.word.length ≤ o := by omega
  rw [hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]
  have hX : 0 ≤ B.gN g := hgp.le
  calc ‖Pc g‖ * ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ * ‖T.coef g (B.Rw T'.word F g)‖
      ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * (‖T.coef g‖ * ‖B.Rw T'.word F g‖) := by
        gcongr
        exact (T.coef g).le_opNorm _
    _ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j *
          ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by
        gcongr
    _ = CP * ε⁻¹ ^ j * Cc * cw * b *
          (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
        rw [Real.rpow_natCast]; ring_nf
    _ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by
        rw [← Real.rpow_add hgp, sub_eq_add_neg]
    _ ≤ CP * ε⁻¹ ^ j * Cc * cw * b *
          B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hg1
        have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
        have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ) := by
          rw [hD]; exact_mod_cast Nat.mul_le_mul_left _ hwo
        push_cast at h4 h5 ⊢
        linarith

theorem leibniz_bound_holds : NFLeibBd := by
  unfold NFLeibBd
  intro k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε
  induction L with
  | nil =>
    refine ⟨0, le_refl _, ?_⟩
    intro F A b hF g hg hεg
    simp [B.opApply]
  | cons T L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε
    obtain ⟨K₂, hK₂, h₂⟩ := ih (fun T' hT' => hL T' (by simp [hT']))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro F A b hF g hg hεg
    have e1 := h₁ F A b hF g hg hεg
    have e2 := h₂ F A b hF g hg hεg
    have hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      simp [B.opApply]
    rw [hs]
    calc _ ≤ ‖T.coef g (B.Rw T.word F g)‖ + ‖B.opApply L F g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end bd

end Formalism.FourierDecayAlt.P.CutBP
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfLeib_thChain_rpow (s : ℝ) : ThChain (fun n x => s ^ n * x ^ s) := by
  intro n x hx
  have h := (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).const_mul (s ^ n)
  have e : s ^ (n + 1) * x ^ s / x = s ^ n * (s * x ^ (s - 1)) := by
    rw [Real.rpow_sub_one hx.ne', pow_succ]
    ring
  show HasDerivAt (fun y => s ^ n * y ^ s) (s ^ (n + 1) * x ^ s / x) x
  rw [e]
  exact h

theorem nfLeib_xD_contDiff (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[n] φ) := by
  intro n
  induction n with
  | zero => simpa using hφ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold xD
    exact contDiff_id.mul (contDiff_infty_iff_deriv.1 ih).2

theorem nfLeib_thChain_xD (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ThChain (fun n => xD^[n] φ) := by
  intro n x hx
  have h := nfLeib_xD_contDiff φ hφ n
  have hd := ((contDiff_infty_iff_deriv.1 h).1 x).hasDerivAt
  have hx0 : x ≠ 0 := hx.ne'
  have e : xD^[n + 1] φ x / x = deriv (xD^[n] φ) x := by
    rw [Function.iterate_succ_apply']
    show x * deriv (xD^[n] φ) x / x = _
    field_simp
  show HasDerivAt (xD^[n] φ) (xD^[n + 1] φ x / x) x
  rw [e]
  exact hd

section cont

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeib_ckOn_contOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {UU : Set (B.Mat k r)}
    (hUU : UU ⊆ B.GV k r) {f : B.Mat k r → E} (h : B.CkOn m UU f) : ContinuousOn f UU := by
  unfold B.CkOn at h
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := h g₀ hg₀
  have hcont : ContinuousAt f' g₀ := hc.continuousOn.continuousAt (hU.mem_nhds hgU)
  have heq : f =ᶠ[𝓝[UU] g₀] f' := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgUU
    exact he g hgU' (hUU hgUU)
  exact hcont.continuousWithinAt.congr_of_eventuallyEq heq (he g₀ hgU (hUU hg₀))

theorem nfLeib_domL_eq (Bs : B.RealPlaceData k r Wp Wq) : C6.domL Bs ∅ = B.GPos Bs := by
  unfold C6.domL B.GPos
  ext g
  simp

theorem nfLeib_opApply_contOn (Bs : B.RealPlaceData k r Wp Wq) (L : B.DiffOp k r Wp Wq)
    (hL : B.SmoothCoef (C6.domL Bs ∅) L) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) :
    ContinuousOn (B.opApply L F) (B.GPos Bs) := by
  induction L with
  | nil =>
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact continuousOn_const
  | cons T L ih =>
    have e : B.opApply (T :: L) F = fun g => T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      funext g; simp [B.opApply]
    rw [e]
    refine ContinuousOn.add ?_ (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))
    have h1 : ContinuousOn T.coef (B.GPos Bs) := by
      rw [← nfLeib_domL_eq Bs]
      exact nfLeib_ckOn_contOn (fun g (hg : g ∈ C6.domL Bs ∅) => hg.1) (hL T List.mem_cons_self).1
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos Bs) :=
      (nfLeib_ckOn_contOn le_rfl (JFxI.ckOn_Rw_top' hF T.word T.word_lie)).mono fun g hg => hg.1
    exact h1.clm_apply h2

end cont

theorem nfLeib_thr (Cb c₃ R Kk W o κ A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ Kk) (hW : 0 ≤ W) (ho0 : 0 ≤ o) (hκ0 : 0 ≤ κ)
    (ho : o ≤ Cb * W * (2 * R + Kk + 1)) (hκ : κ ≤ Cb * (R + 1) * o)
    (hA : (max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0) * (R + 1) ^ 4 *
      (W * (2 * R + Kk + 1) ^ 2 + (2 * R + Kk + 1) ^ 3) ≤ A) :
    c₃ * (R + 1) ^ 2 * (R * (2 * R + Kk + 1) + 1) ≤ A - (κ + 3 * (R + 1) * o + (2 * R + 2) * o) := by
  have hM : Cb ≤ max Cb 0 := le_max_left _ _
  have hM0 : 0 ≤ max Cb 0 := le_max_right _ _
  have hc : c₃ ≤ max c₃ 0 := le_max_left _ _
  have hc0 : 0 ≤ max c₃ 0 := le_max_right _ _
  set M := max Cb 0 with hMd
  set c := max c₃ 0 with hcd
  set T := 2 * R + Kk + 1 with hTd
  clear_value M c T
  have hTR : R + 1 ≤ T := by rw [hTd]; linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hR1 : 1 ≤ R + 1 := by linarith
  have hR0 : 0 ≤ R + 1 := by linarith
  have ho' : o ≤ M * W * T := by
    have : Cb * W * T ≤ M * W * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hW) hT0
    linarith
  have hκ' : κ ≤ M * (R + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR0) ho0)
  have hR2 : R + 1 ≤ (R + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR1 hR0
    linarith
  have hR4 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := by
    have h1 : 1 ≤ (R + 1) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (R + 1))
    linarith
  have hR14 : R + 1 ≤ (R + 1) ^ 4 := hR2.trans hR4
  have hT2 : T ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT1 hT0
    linarith
  have hT3 : T ^ 2 ≤ T ^ 3 := by
    have := mul_le_mul_of_nonneg_left hT1 (sq_nonneg T)
    linarith
  have hRT : R * T + 1 ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_right hTR hT0
    linarith
  have hRT0 : 0 ≤ R * T + 1 := by
    have := mul_nonneg hR hT0
    linarith
  have hX0 : 0 ≤ (R + 1) ^ 2 * (R * T + 1) := mul_nonneg (sq_nonneg _) hRT0
  have hXY : (R + 1) ^ 2 * (R * T + 1) ≤ (R + 1) ^ 4 * T ^ 3 :=
    mul_le_mul hR4 (hRT.trans hT3) hRT0 (by positivity)
  have h1 : c₃ * (R + 1) ^ 2 * (R * T + 1) ≤ c * ((R + 1) ^ 4 * T ^ 3) := by
    have e1 := mul_le_mul_of_nonneg_right hc hX0
    have e2 := mul_le_mul_of_nonneg_left hXY hc0
    calc c₃ * (R + 1) ^ 2 * (R * T + 1) = c₃ * ((R + 1) ^ 2 * (R * T + 1)) := by ring
      _ ≤ c * ((R + 1) ^ 4 * T ^ 3) := e1.trans e2
  have hMR : 0 ≤ (M + 5) * (R + 1) := mul_nonneg (by linarith) hR0
  have h3 := mul_le_mul_of_nonneg_left ho' hMR
  have hS : 0 ≤ M ^ 2 + 5 * M := add_nonneg (sq_nonneg M) (by linarith)
  have hZ : 0 ≤ (M ^ 2 + 5 * M) * W := mul_nonneg hS hW
  have hRT4 : (R + 1) * T ≤ (R + 1) ^ 4 * T ^ 2 := mul_le_mul hR14 hT2 hT0 (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hRT4 hZ
  have h5 : 0 ≤ (M ^ 2 + 5 * M) * ((R + 1) ^ 4 * T ^ 3) :=
    mul_nonneg hS (mul_nonneg (by positivity) (pow_nonneg hT0 3))
  have h6 : 0 ≤ c * ((R + 1) ^ 4 * (W * T ^ 2)) :=
    mul_nonneg hc0 (mul_nonneg (by positivity) (mul_nonneg hW (sq_nonneg T)))
  linarith [h1, h3, h4, h5, h6, hA, hκ']

theorem nfLeibV_of (hO : NFLeibOps) (hB : NFLeibBd) (hV : NFVLin) : NFLeibV := by
  obtain ⟨c₃, hc₃⟩ := hV
  intro Cb
  refine ⟨max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p hInD w hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hInD w hw e
  obtain ⟨Q, L, hsm, hterm, hexp⟩ := hO P.k P.r Wp Wq p.T.base Dop hIn.1
  refine ⟨Q, L, hsm, ?_, ?_⟩
  · intro s F hF g hg
    have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g := hg.2.1
    have e1 : (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') =
        fun y => (((fun (n : ℕ) (x : ℝ) => s ^ n * x ^ s) 0 (Gf P.k P.r p.T.base.z p.T.base.z' y) : ℝ) : ℂ) •
          F y := by
      funext y; simp
    rw [hΘ _ g hg, e1, hexp _ (nfLeib_thChain_rpow s) F hF g hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    have hp : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g ^ s := Real.rpow_pos_of_pos hG s
    rw [Real.rpow_neg hG.le]
    field_simp
  · intro φ hφ F A hF hdec hA γ hγ hGγ
    obtain ⟨b, hb⟩ := hdec o
    set m : ℝ := (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o with hm
    have hdecq : ∀ q : Fin (Q + 1), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV P.k P.r,
        ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g → ‖B.opApply (L q) F g‖ ≤ C * B.gN g ^ (-(A - m)) := by
      intro q ε hε
      obtain ⟨K, -, hK⟩ := hB P.k P.r Wp Wq p.T.base nf fib o κ Dop hfib hIn (L q) (hterm q) ε hε
      refine ⟨K * b, fun g hg hgε => ?_⟩
      have := hK F A b hb g hg hgε
      have ee : (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o - A = -(A - m) := by rw [hm]; ring
      rwa [ee] at this
    have hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - m := by
      have h0 := nfLeib_thr Cb c₃ P.r P.k w.length o κ A (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by push_cast at ho; linarith) hκ (by linarith)
      push_cast
      rw [hm]
      linarith
    have hsplit : ∀ g ∈ B.GPos p.T.base, p.Θ.Θ w e
        (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) g =
        ∑ q : Fin (Q + 1), (fun (q : Fin (Q + 1)) (x : ℝ) => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) q
          (Gf P.k P.r p.T.base.z p.T.base.z' g) • B.opApply (L q) F g := by
      intro g hg
      have hgd : g ∈ C6.domL p.T.base ∅ := by rw [nfLeib_domL_eq]; exact hg
      rw [hΘ _ g hgd]
      exact hexp (fun n => xD^[n] φ) (nfLeib_thChain_xD φ hφ) F hF g hgd
    exact hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ Q (fun q x => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) _
      (fun q => B.opApply (L q) F) (A - m) hthr
      (fun q => nfLeib_opApply_contOn p.T.base (L q) (hsm q) F hF) hdecq hsplit γ hγ hGγ

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibOps
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibOps_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem nfLeibOps_hsInner_smul_left (c : ℂ) (A B' : Wq →L[ℂ] Wp) : B.hsInner (c • A) B' = c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_right]

theorem nfLeibOps_hsInner_smul_right (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner A (c • B') = conj c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_left]

def nfLeibOps_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (g : B.Mat k r) : ℂ :=
  t.2.1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1


open Classical in
def nfLeibOps_mk (Bs : B.RealPlaceData k r Wp Wq) (T : B.DTerm k r Wp Wq)
    (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef g := nfLeibOps_sc Bs t g • T.coef g
  coefAdj g := conj (nfLeibOps_sc Bs t g) • T.coefAdj g
  word := if ∀ X ∈ t.2.2.2, B.inLie k r X then t.2.2.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id x A B' := by
    simp only [ContinuousLinearMap.smul_apply]
    rw [nfLeibOps_hsInner_smul_left, nfLeibOps_hsInner_smul_right, T.adj_id, Complex.conj_conj]

theorem nfLeibOps_ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (B.Mat k r)}
    {c : B.Mat k r → ℂ} {f : B.Mat k r → E} (hc : B.CkOn ⊤ UU c) (hf : B.CkOn ⊤ UU f) :
    B.CkOn ⊤ UU (fun g => c g • f g) := by
  unfold B.CkOn at hc hf ⊢
  intro g₀ hg₀
  obtain ⟨U₁, c', hU₁, hg₁, hc', ec⟩ := hc g₀ hg₀
  obtain ⟨U₂, f', hU₂, hg₂, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => c' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show c g • f g = c' g • f' g
  rw [ec g hg.1 hgG, ef g hg.2 hgG]

theorem nfLeibOps_ckOn_conj {UU : Set (B.Mat k r)} {c : B.Mat k r → ℂ} (hc : B.CkOn ⊤ UU c) :
    B.CkOn ⊤ UU (fun g => conj (c g)) := by
  unfold B.CkOn at hc ⊢
  intro g₀ hg₀
  obtain ⟨U, c', hU, hg, hc', ec⟩ := hc g₀ hg₀
  refine ⟨U, fun g => conj (c' g), hU, hg, ?_, ?_⟩
  · refine (Complex.conjCLE.contDiff.comp_contDiffOn hc').congr (fun g _ => ?_)
    simp
  · intro g hgU hgG
    show conj (c g) = conj (c' g)
    rw [ec g hgU hgG]

theorem nfLeibOps_ckOn_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (D : ℕ)
    (hP : ListSumSplittings.PolyClass D t.2.1) : B.CkOn ⊤ (C6.domL Bs ∅) (nfLeibOps_sc Bs t) := by
  intro g₀ hg₀
  obtain ⟨U1, c1, hU1, hg1, hc1, he1⟩ := hP.1 g₀ hg₀.1
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z')
  have hO : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  refine ⟨U1 ∩ {g | 0 < Gf k r Bs.z Bs.z' g},
    fun g => c1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1, hU1.inter hO, ⟨hg1, hg₀.2.1⟩, ?_, ?_⟩
  · refine (hc1.mono Set.inter_subset_left).mul ?_
    refine ContDiffOn.pow ?_ _
    refine (hGc.contDiffOn.inv fun g hg => ?_).mono Set.inter_subset_right
    · exact_mod_cast (ne_of_gt hg)
  · intro g hg hgG
    simp only [nfLeibOps_sc, he1 g hg.1 hgG]

end ops

theorem nfLeibOps_sum_key {E : Type*} [AddCommGroup E] [Module ℂ E] {α : Type*} (Q : ℕ) (key : α → ℕ)
    (f : ℕ → ℂ) (a : α → E) : ∀ l : List α, (∀ t ∈ l, key t ≤ Q) →
    (l.map fun t => f (key t) • a t).sum =
      ∑ q : Fin (Q + 1), f q • ((l.filter fun t => key t = (q : ℕ)).map a).sum := by
  intro l hl
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun t' ht' => hl t' (by simp [ht']))]
    have hq : key t < Q + 1 := Nat.lt_succ_of_le (hl t (by simp))
    have hsplit : ∀ q : Fin (Q + 1), f q • (((t :: l).filter fun t' => key t' = (q : ℕ)).map a).sum =
        (if key t = (q : ℕ) then f q • a t else 0) +
          f q • ((l.filter fun t' => key t' = (q : ℕ)).map a).sum := by
      intro q
      by_cases h : key t = (q : ℕ)
      · simp [List.filter_cons, h, smul_add]
      · simp [List.filter_cons, h]
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨key t, hq⟩]
    · simp
    · intro b _ hb
      have hne : key t ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne]
    · simp

theorem nfLeibOps_of (hE : NFLeibExp) : NFLeibOps := by
  intro k r Wp Wq _ _ _ _ _ Bs Dop hsm
  classical
  let terms : B.DTerm k r Wp Wq → List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) :=
    fun T => (hE k r Wp Wq Bs T.word T.word_lie).choose
  have hspec := fun T : B.DTerm k r Wp Wq => (hE k r Wp Wq Bs T.word T.word_lie).choose_spec
  set Q : ℕ := (Dop.map fun T => T.word.length).sum with hQ
  have hQle : ∀ T ∈ Dop, T.word.length ≤ Q := fun T hT =>
    List.le_sum_of_mem (List.mem_map.2 ⟨T, hT, rfl⟩)
  let LT : B.DTerm k r Wp Wq → Fin (Q + 1) → B.DiffOp k r Wp Wq :=
    fun T q => ((terms T).filter fun t => t.1 = (q : ℕ)).map (nfLeibOps_mk Bs T)
  refine ⟨Q, fun q => Dop.flatMap fun T => LT T q, ?_, ?_, ?_⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    have hP := ((hspec T).1 t htm).2.1
    exact ⟨nfLeibOps_ckOn_smul (nfLeibOps_ckOn_sc Bs t _ hP) (hsm T hT).1,
      nfLeibOps_ckOn_smul (nfLeibOps_ckOn_conj (nfLeibOps_ckOn_sc Bs t _ hP)) (hsm T hT).2⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    obtain ⟨-, hP, hsub⟩ := (hspec T).1 t htm
    refine ⟨T, hT, t.2.1, t.2.2.1, hP, ?_, fun g _ => rfl⟩
    have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (hsub.subset hX)
    simp only [nfLeibOps_mk]
    rw [if_pos hlie]
    exact hsub
  ·
    intro Ψ hΨ F hF x hx
    have hT1 : ∀ T ∈ Dop, T.coef x (B.Rw T.word (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x) =
        ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (LT T q) F x := by
      intro T hT
      rw [(hspec T).2 Ψ hΨ F hF x hx, map_list_sum, List.map_map]
      have e1 : ((terms T).map ((T.coef x) ∘ fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
            ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x))) =
          (terms T).map fun t => (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ)) t.1 •
            (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) t := by
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, map_smul, nfLeibOps_sc, smul_smul, mul_assoc]
      rw [e1]
      refine (nfLeibOps_sum_key Q (fun t => t.1) (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ))
        (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) (terms T)
        (fun t ht => ((hspec T).1 t ht).1.trans (hQle T hT))).trans ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      unfold B.opApply
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have htm : t ∈ terms T := (List.mem_filter.1 ht).1
      have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (((hspec T).1 t htm).2.2.subset hX)
      simp only [Function.comp_apply, nfLeibOps_mk, if_pos hlie, ContinuousLinearMap.smul_apply]
    have hall : ∀ D' : B.DiffOp k r Wp Wq, (∀ T ∈ D', T ∈ Dop) →
        B.opApply D' (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
          ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (D'.flatMap fun T => LT T q) F x := by
      intro D'
      induction D' with
      | nil => intro _; simp [B.opApply]
      | cons T D' ih =>
        intro hsub
        have eA : ∀ (D'' : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (T :: D'') G x = T.coef x (B.Rw T.word G x) + B.opApply D'' G x := by
          intro D'' G; simp [B.opApply]
        have eB : ∀ (l1 l2 : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (l1 ++ l2) G x = B.opApply l1 G x + B.opApply l2 G x := by
          intro l1 l2 G; simp [B.opApply]
        rw [eA, hT1 T (hsub T List.mem_cons_self), ih fun T' hT' => hsub T' (List.mem_cons_of_mem _ hT'),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [List.flatMap_cons, eB, smul_add]
    exact hall Dop fun T hT => hT

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibVLin
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfVLin_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {ι : Type} (s : Finset ι) (a : Wp →L[ℂ] Wp) (b : Wq →L[ℂ] Wq) (c : ι → ℂ)
    (f : ι → Wq →L[ℂ] Wp) :
    a.comp ((∑ i ∈ s, c i • f i).comp b) = ∑ i ∈ s, c i • a.comp ((f i).comp b) := by
  ext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ContinuousLinearMap.sum_apply, map_sum, map_smul]

theorem vector_linearity_holds : NFVLin := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint
  unfold D.vecV
  have h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt := ⟨hpt, hGPoint⟩
  simp only [dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  · simp only [dif_pos h']
    have hγ := h'.choose_spec.1
    have hZ := h'.choose_spec.2.1
    have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
    have hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose := by
      rw [hGq]
    obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1
    have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ
    have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
    have hZm := hZ.trans hmono
    obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA
    have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
      ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
        fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
    have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG

    have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp),
        Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS →
        D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G =
          ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS := by
      intro G hi
      have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧
          Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
      unfold D.orbJ
      rw [dif_pos hex]
      exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
        hex.choose_spec.2 hi

    have hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS := by
      intro q
      obtain ⟨C, hC⟩ := hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos
      have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS :=
        Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)
      refine Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_
      refine hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_
      have hs := horb p hp
      refine (hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

    have hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS]
        fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have hs := horb p hp
      simp only [D.orbIntegrand, B.rho]
      rw [hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]
    have hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS :=
      (integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm
    have hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable
        (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS :=
      fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))
    rw [hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_smul, hEq (Hq q) (hiq q)]
  · simp only [dif_neg h', smul_zero, Finset.sum_const_zero]

end

end Formalism.FourierDecayAlt.P.CutBP
end

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_vector_estimate_holds : NFLeibV :=
  nfLeibV_of (nfLeibOps_of leibniz_expansion_holds) leibniz_bound_holds vector_linearity_holds

end Formalism.FourierDecayAlt.P.CutBP
