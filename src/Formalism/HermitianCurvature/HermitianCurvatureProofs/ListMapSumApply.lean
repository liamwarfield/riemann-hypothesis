module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtEpart

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MemStepsFull
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenBigCellSet
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def V0 (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (Mat k r) :=
  {x | 0 < Gf k r D.z D.z' x} ∩ ⋂ l ∈ L, {x | Dmin k r D.z D.z' x l ≠ 0}

lemma isOpen_big_cell_set (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : IsOpen (V0 D L) := by
  unfold V0
  refine (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter ?_
  refine isOpen_biInter_finset (fun l _ => ?_)
  exact isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const

lemma mem_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (g : Mat k r) :
    g ∈ C6.domL D L ↔ g ∈ GV k r ∧ g ∈ V0 D L := by
  simp only [C6.domL, V0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

lemma domL_gpos {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L) :
    g ∈ GPos D := by
  exact ⟨hg.1, hg.2.1⟩

lemma nz_of_domL {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L)
    {nf : ℕ} {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0) ∧
      (e.1.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) := by
  have hlast : Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG : 0 < Gf k r D.z D.z' g := hg.2.1
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' g ⟨r, by omega⟩))
    linarith
  obtain ⟨hab, -, -⟩ := he
  refine ⟨fun l hl => ?_, fun _ => ?_⟩
  · rcases hab l hl with hl | rfl
    · exact hg.2.2 l hl
    · exact hlast
  · exact_mod_cast hg.2.1.ne'

lemma shape_flatMap' (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (Lf : FS k r nf) (f : CT k r nf × List (Mat k r) → FS k r nf) (g : Mat k r) :
    shape D fib F (Lf.flatMap f) g = (Lf.map fun e => shape D fib F (f e) g).sum := by
  induction Lf with
  | nil => simp [shape]
  | cons e Lf ih =>
    simp only [shape] at ih ⊢
    simp [ih, List.sum_append]

private lemma ckOn_rw_of_ckOn_add_length {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)}
    {f : Mat k r → E} : ∀ (w : List (Mat k r)) (n : ℕ∞), (∀ X ∈ w, inLie k r X) →
      CkOn (n + w.length) UU f → CkOn n UU (Rw w f) := by
  intro w
  induction w with
  | nil => intro n _ hf; simpa [Rw] using hf
  | cons X w ih =>
    intro n hw hf
    rw [Rw_cons']
    refine CkOn_Dx (x := (false, X)) (hw X (by simp)) (ih (n + 1) (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) ?_)
    have e : n + 1 + (w.length : ℕ∞) = n + ((X :: w).length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [e]; exact hf

private lemma hasDerivAt_shape_crv_of_good (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    ∀ Lf : FS k r nf, (∀ e ∈ Lf, Good L e) → (∀ e ∈ Lf, e.2.length + 1 ≤ m) →
      HasDerivAt (fun s => shape D fib F Lf (crv (false, X) g s)) (shape D fib F (step D X Lf) g) 0 := by
  intro Lf
  induction Lf with
  | nil =>
    intro _ _
    simp only [shape, step, List.map_nil, List.sum_nil, List.flatMap_nil]
    exact hasDerivAt_const _ _
  | cons e Lf ih =>
    intro hL hm
    have he : Good L e := hL e (by simp)
    have hgp := domL_gpos hg
    have hnz := nz_of_domL hg he
    have hcv := hasDerivAt_cv D fib hfib hX hgp e.1 hnz.1 hnz.2 he.2.1
    have hRw : CkOn 1 (GV k r) (Rw e.2 F) := by
      refine ckOn_rw_of_ckOn_add_length e.2 1 he.2.2 (sCkOn_mono ?_ hF)
      have := hm e (by simp)
      rw [add_comm]; exact_mod_cast this
    have hR : HasDerivAt (fun s => Rw e.2 F (crv (false, X) g s)) (Rw (X :: e.2) F g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX hRw hgp.1 hgp.1
    have hcv' := ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) hcv
    have h1 := hcv'.clm_apply hR
    have h2 := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.add h2
    show HasDerivAt (fun s => cv D fib e.1 (crv (false, X) g s) (Rw e.2 F (crv (false, X) g s)) +
      shape D fib F Lf (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    rw [crv_zero]
    have hs : shape D fib F (step D X (e :: Lf)) g =
        shape D fib F (stepOne D X e) g + shape D fib F (step D X Lf) g := by
      simp only [step, shape_flatMap', List.map_cons, List.sum_cons]
    rw [hs]
    congr 1
    simp only [shape, stepOne, List.map_append, List.map_map, List.sum_append, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← list_sum_apply, crv_zero]
    try rfl

theorem step_eq (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {X : Mat k r} (hX : inLie k r X) {Lf : FS k r nf}
    (hL : ∀ e ∈ Lf, Good L e) (hm : ∀ e ∈ Lf, e.2.length + 1 ≤ m) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    RdV X (shape D fib F Lf) g = shape D fib F (step D X Lf) g := by
  have hd := hasDerivAt_shape_crv_of_good D fib hfib L hF hX hg Lf hL hm
  rw [← hd.deriv]
  exact Dx_eq (false, X) (shape D fib F Lf) g

theorem expand (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), (∀ X ∈ w, inLie k r X) → (∀ e ∈ Lf, Good L e) →
      (∀ e ∈ Lf, e.2.length + w.length ≤ m) → ∀ g ∈ C6.domL D L,
        Rw w (shape D fib F Lf) g = shape D fib F (steps D w Lf) g := by
  intro w
  induction w with
  | nil => intro Lf _ _ _ g _; rfl
  | cons X w ih =>
    intro Lf hw hL hm g hg
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hm' : ∀ e ∈ Lf, e.2.length + w.length ≤ m := fun e he => by
      have := hm e he; simp only [List.length_cons] at this; omega
    have hev : (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) =ᶠ[𝓝 0]
        (fun t => shape D fib F (steps D w Lf) (crv (false, X) g t)) := by
      have hV : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
      filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV] with t ht
      exact ih Lf hw' hL hm' _ ((mem_domL D L _).2 ⟨crv_mem (x := (false, X)) hX hg.1 t, ht⟩)
    have hgood := good_steps D w hw' Lf hL
    have hstep := step_eq D fib hfib L hF hX (Lf := steps D w Lf) (fun e he => (hgood e he).1)
      (fun e he => by
        obtain ⟨-, e0, he0, hle⟩ := hgood e he
        have := hm e0 he0
        simp only [List.length_cons] at this
        omega) hg
    calc Rw (X :: w) (shape D fib F Lf) g
        = deriv (fun t : ℝ => Rw w (shape D fib F Lf) (crv (false, X) g t)) 0 := by
          rw [Rw_cons']; exact Dx_eq (false, X) _ g
      _ = deriv (fun t : ℝ => shape D fib F (steps D w Lf) (crv (false, X) g t)) 0 := hev.deriv_eq
      _ = RdV X (shape D fib F (steps D w Lf)) g := (Dx_eq (false, X) _ g).symm
      _ = shape D fib F (steps D (X :: w) Lf) g := hstep

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma cd_eval (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => eval (vars g) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)
  next p q hp hq =>
    simpa using hp.add hq
  next p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases n with ⟨i, j⟩ | ⟨i, j⟩
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl]
      fun_prop
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]
      have h : ContDiff ℝ ∞ fun g : Mat k r => g i j := by fun_prop
      exact Complex.conjCLE.contDiff.comp h

lemma cd_dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ∞ (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, -, hq⟩ := dminPoly (k := k) z z' l
  have h : (fun g : Mat k r => Dmin k r z z' g l) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cd_gf (z z' : Fin (2 * r + k + 1) → ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  obtain ⟨q, -, hq⟩ := gfPoly (k := k) z z'
  have h : (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g => eval (vars g) q := funext hq
  rw [h]
  exact cd_eval q

lemma cda_invpow {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) {x : Mat k r} (a : ℕ) (h : a = 0 ∨ f x ≠ 0) :
    ContDiffAt ℝ ∞ (fun g => (f g)⁻¹ ^ a) x := by
  rcases h with rfl | h
  · simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  · exact (hf.contDiffAt.inv h).pow a

lemma cda_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Mat k r => (1 : ℂ)) x)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma cda_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) {x : Mat k r} (hx : x ∈ V0 D L) : ContDiffAt ℝ ∞ (cvs D e.1) x := by
  obtain ⟨hab, -, -⟩ := he
  have hx0 : 0 < Gf k r D.z D.z' x := hx.1
  have hxL : ∀ l ∈ L, Dmin k r D.z D.z' x l ≠ 0 := fun l hl => Set.mem_iInter₂.1 hx.2 l hl
  have hlast : Dmin k r D.z D.z' x (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG := hx0
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' x ⟨r, by omega⟩))
    linarith
  have hnz : ∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' x l ≠ 0 := fun l hl => by
    rcases hab l hl with hl | rfl
    · exact hxL l hl
    · exact hlast
  have hA : ∀ l, e.1.a l = 0 ∨ Dmin k r D.z D.z' x l ≠ 0 := fun l => by
    by_cases h : e.1.a l = 0
    · exact Or.inl h
    · exact Or.inr (hnz l (Or.inl h))
  have hB : ∀ l, e.1.b l = 0 ∨ Complex.conjCLE (Dmin k r D.z D.z' x l) ≠ 0 := fun l => by
    by_cases h : e.1.b l = 0
    · exact Or.inl h
    · right
      simpa using hnz l (Or.inr h)
  show ContDiffAt ℝ ∞ (fun g => eval (vars g) e.1.q * C6.monoM D e.1.a e.1.b e.1.c g) x
  refine (cd_eval _).contDiffAt.mul ?_
  refine (cda_prod (f := fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ e.1.a l *
      (star (Dmin k r D.z D.z' g l))⁻¹ ^ e.1.b l) Finset.univ (fun l _ => ?_)).mul ?_
  · exact (cda_invpow (cd_dmin D.z D.z' l) _ (hA l)).mul
      (cda_invpow (Complex.conjCLE.contDiff.comp (cd_dmin (k := k) D.z D.z' l)) _ (hB l))
  · exact cda_invpow (cd_gf D.z D.z') _ (Or.inr (by exact_mod_cast hx0.ne'))

lemma ckOn_mul {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hA g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hfe'⟩ := hB g₀ hg₀
  refine ⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩
  · exact (hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)
  · intro g hg hgG
    simp only [hfe g hg.1 hgG, hfe' g hg.2 hgG]

lemma ckOn_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) → CkOn ⊤ (GPos D) (C6.Epart fib es) := by
  intro es
  induction es with
  | nil =>
    intro _ g₀ _
    refine ⟨univ, fun _ => 1, isOpen_univ, mem_univ _, contDiffOn_const, ?_⟩
    intro g _ _
    simp [C6.Epart]
  | cons e es ih =>
    intro hes
    have h1 := ckOn_Rw_top (hfib e.1) (hes e (by simp))
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    exact ckOn_mul h1 h2

lemma ckOn_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) : CkOn ⊤ (C6.domL D L) (cv D fib e.1) := by
  intro g₀ hg₀
  have hgpos : g₀ ∈ GPos D := domL_gpos hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos
  have hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L) :=
    (isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)
  refine ⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩
  · exact (hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)
  · intro g hg hgG
    simp only [cv, hfe g hg.1 hgG]

def mulCT {nf : ℕ} (t₁ t₂ : CT k r nf) : CT k r nf :=
  ⟨t₁.q * t₂.q, t₁.a + t₂.a, t₁.b + t₂.b, t₁.c + t₂.c, t₁.es ++ t₂.es⟩

lemma cv_mul (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t₁ t₂ : CT k r nf)
    (g : Mat k r) : cv D fib (mulCT t₁ t₂) g = cv D fib t₁ g * cv D fib t₂ g := by
  simp only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply,
    pow_add, Finset.prod_mul_distrib]
  rw [smul_mul_smul_comm]
  congr 1
  ring

def fo {nf : ℕ} (es : List (Fin nf × List (Mat k r))) : ℕ := (es.map fun e => e.2.length).sum

lemma fo_set {nf : ℕ} (X : Mat k r) :
    ∀ (es : List (Fin nf × List (Mat k r))) (i : Fin es.length),
      fo (es.set i ((es.get i).1, X :: (es.get i).2)) = fo es + 1 := by
  intro es
  induction es with
  | nil => intro i; exact i.elim0
  | cons e es ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · simp [fo]
      omega
    · have hj' : j < es.length := by simpa using hj
      have := ih ⟨j, hj'⟩
      have e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) =
          e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2) := rfl
      show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) =
        fo (e :: es) + 1
      rw [e2]
      simp only [fo, List.map_cons, List.sum_cons] at this ⊢
      omega

lemma bound_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) :
    ∀ e' ∈ stepOne D X e, e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + 1 := by
  intro e' he'
  simp only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · rcases ht' with ht' | ht'
    · have hes := dscal_es D X e.1 t' ht'
      refine ⟨?_, by simp [hes]⟩
      simp only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'
      rcases ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl
      · exact (PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)
    · simp only [dfib, List.mem_ofFn] at ht'
      obtain ⟨i, rfl⟩ := ht'
      refine ⟨Nat.le_add_right _ _, ?_⟩
      simp only
      rw [fo_set]; omega
  · refine ⟨Nat.le_add_right _ _, by simp; omega⟩

lemma bound_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by
  intro w
  induction w with
  | nil =>
    intro Lf e' he'
    exact ⟨e', he', by simp, by simp⟩
  | cons X w ih =>
    intro Lf e' he'
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨e, he, hd, ho⟩ := ih Lf e'' he''
    obtain ⟨hd', ho'⟩ := bound_step D X e'' e' he'
    refine ⟨e, he, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      omega

lemma mem_steps_full (D : RealPlaceData k r Wp Wq) {nf : ℕ} (e : CT k r nf × List (Mat k r)) :
    ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w [e] := by
  intro w
  induction w with
  | nil => simp [steps]
  | cons X w ih =>
    simp only [steps, List.foldr_cons, step, List.mem_flatMap, List.cons_append]
    exact ⟨_, ih, by simp [stepOne]⟩

lemma steps_append (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L₁ L₂ : FS k r nf) :
    steps D w (L₁ ++ L₂) = steps D w L₁ ++ steps D w L₂ := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)
    rw [ih]
    simp [step, List.flatMap_append]

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def TermClause (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ (P : Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) ∧
      ∀ g ∈ C6.domL D L, T.coef g = (P g * C6.monoM D a b c g) • C6.Epart fib es g

theorem toFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) {o κ : ℕ} :
    ∀ Θ : DiffOp k r Wp Wq, TermClause D fib L o κ Θ →
      ∃ Lf : FS k r nf, (∀ e ∈ Lf, Good L e ∧ e.1.q.totalDegree ≤ κ ∧ e.2.length + fo e.1.es ≤ o) ∧
        (∀ T ∈ Θ, ∃ e ∈ Lf, e.2 = T.word) ∧
        ∀ (H : Mat k r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL D L, opApply Θ H g = shape D fib H Lf g := by
  intro Θ hΘ
  induction Θ with
  | nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨Lf, h1, h2, h3⟩ := ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩ := hΘ T (by simp)
    refine ⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, hqdeg, hlen⟩
        unfold Good
        refine ⟨?_, hes, T.word_lie⟩
        intro l hl
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hab l hcon.1 hcon.2
        rcases hl with hl | hl
        · exact hl ha
        · exact hl hb
      · exact h1 e' he'
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨e', he', h⟩ := h2 T' hT'
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · intro H g hg
      have h3' := h3 H g hg
      simp only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢
      rw [h3', hcoef g hg]
      congr 1
      simp only [cv, cvs]
      rw [hq g]
      rfl

section mk

variable [FiniteDimensional ℂ Wp]


open Classical in
def mkTerm (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (e : CT k r nf × List (Mat k r)) : DTerm k r Wp Wq where
  coef := cv D fib e.1
  coefAdj := fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 x)
  word := if ∀ X ∈ e.2, inLie k r X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec _ A B

lemma mkTerm_word (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    {e : CT k r nf × List (Mat k r)} (h : ∀ X ∈ e.2, inLie k r X) : (mkTerm D fib e).word = e.2 := by
  dsimp only [mkTerm]
  rw [if_pos h]

lemma opApply_mk (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  simp only [Function.comp_apply]
  rw [mkTerm_word D fib (hL e he)]
  rfl

end mk

def compFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (L₁ L₂ : FS k r nf) : FS k r nf :=
  L₁.flatMap fun e₁ => (steps D e₁.2 L₂).map fun e => (mulCT e₁.1 e.1, e.2)

lemma compFS_bound (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by
  intro e he
  simp only [compFS, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e₁, he₁, e', he', rfl⟩ := he
  obtain ⟨hG₁, hq₁, ho₁⟩ := h₁ e₁ he₁
  obtain ⟨hG₁a, hG₁b, hG₁c⟩ := hG₁
  have hG' := (good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1
  obtain ⟨hG'a, hG'b, hG'c⟩ := hG'
  obtain ⟨e₂, he₂, hdeg, hlen⟩ := bound_steps D e₁.2 L₂ e' he'
  obtain ⟨-, hq₂, ho₂⟩ := h₂ e₂ he₂
  have hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂ := by
    intro l₁ l₂
    simp [fo, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold Good
    refine ⟨?_, ?_, hG'c⟩
    · intro l hl
      simp only [mulCT, Pi.add_apply] at hl
      by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
      · exact hG₁a l h1
      · apply hG'a l
        push_neg at h1
        rcases hl with hl | hl
        · left; omega
        · right; omega
    · intro x hx Y hY
      simp only [mulCT, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hG₁b x hx Y hY
      · exact hG'b x hx Y hY
  · simp only [mulCT]
    have hmul := MvPolynomial.totalDegree_mul e₁.1.q e'.1.q
    have hw : e₁.2.length ≤ o₁ := by omega
    have := Nat.mul_le_mul_left (2 * r + 2) hw
    omega
  · simp only [mulCT]
    rw [hfo]
    omega

lemma list_map_sum_apply {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by
  rw [map_list_sum, List.map_map]
  rfl

private lemma rw_congr_on_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ {H H' : Mat k r → (Wq →L[ℂ] Wp)},
      (∀ g ∈ C6.domL D L, H g = H' g) → ∀ g ∈ C6.domL D L, Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ H H' hH g hg; exact hH g hg
  | cons X w ih =>
    intro hw H H' hH g hg
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH
    rw [Rw_cons', Rw_cons', Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hGV : g ∈ GV k r := ((mem_domL D L g).1 hg).1
    have hV0 : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
    filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht
    apply ih'
    rw [mem_domL]
    exact ⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩

theorem comp_identity (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by
  show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _
  unfold compFS
  rw [shape_flatMap']
  congr 1
  refine List.map_congr_left fun e₁ he₁ => ?_
  obtain ⟨-, -, hw⟩ := hg₁ e₁ he₁
  rw [rw_congr_on_domL D L e₁.2 hw hH g hg]
  rw [expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]
  unfold shape
  rw [list_map_sum_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]

end Formalism.FourierDecayAlt.P.MinorPolynomials
