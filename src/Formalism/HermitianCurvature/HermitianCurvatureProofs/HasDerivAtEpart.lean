module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtCvs
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtInvpow
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private lemma exists_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = Zhat k r z z' g a b := by
  refine ⟨fun a b => ∑ i, ∑ j, C (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b) *
    MvPolynomial.X (Sum.inl (i, j)), ?_, ?_⟩
  · intro a b
    exact MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      MvPolynomial.totalDegree_finsetSum_le fun j _ => deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_star_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = star (Zhat k r z z' g a b) := by
  refine ⟨fun a b => ∑ i, ∑ j, C (star (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b)) *
    MvPolynomial.X (Sum.inr (i, j)), ?_, ?_⟩
  · intro a b
    exact MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      MvPolynomial.totalDegree_finsetSum_le fun j _ => deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul,
      star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_det_submatrix_poly_deg_le_of_entries_deg_le_one {m : ℕ} (f : Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (P : Fin m → Fin m → MvPolynomial (Vr (2 * r + k + 1)) ℂ) (hP : ∀ a b, (P a b).totalDegree ≤ 1)
    (hf : ∀ g a b, eval (vars g) (P a b) = f g a b) (n : ℕ) (e : Fin n → Fin m) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ n ∧
      ∀ g, ((f g).submatrix e e).det = eval (vars g) q := by
  refine ⟨(Matrix.of fun a b => P (e a) (e b)).det, deg_det _ (fun a b => hP _ _), fun g => ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, hf]

private lemma exists_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => Zhat k r z z' g) P hP hPe l.val
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  exact ⟨q, hq, fun g => by rw [Dmin]; exact hqe g⟩

private lemma exists_star_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_star_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => (Zhat k r z z' g).map (starRingEnd ℂ)) P hP
    (fun g a b => by simp [hPe]) l.val (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  refine ⟨q, hq, fun g => ?_⟩
  rw [← hqe g, Dmin, ← starRingEnd_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

lemma dminPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma dminStarPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma gfPoly (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, ((Gf k r z z' g : ℝ) : ℂ) = eval (vars g) q := by
  obtain ⟨qa, ha, hae⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qab, hab, habe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qb, hb, hbe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  obtain ⟨qbb, hbb, hbbe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  simp only [Fin.val_last] at ha hab hb hbb
  refine ⟨qa * qab - C ((Tz k r z * Tz k r z' : ℝ) : ℂ) * qb * qbb, ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (deg_cmul _ _ _).trans (by omega)
  · simp only [map_sub, map_mul, eval_C]
    rw [← hae g, ← habe g, ← hbe g, ← hbbe g, Gf]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring

def qDl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminPoly (k := k) z z' l)

def qDbl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminStarPoly (k := k) z z' l)

def qGf (z z' : Fin (2 * r + k + 1) → ℂ) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (gfPoly (k := k) z z')

lemma qDl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminPoly (k := k) z z' l)).1
lemma qDl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDl z z' l) = Dmin k r z z' g l :=
  ((Classical.choose_spec (dminPoly (k := k) z z' l)).2 g).symm
lemma qDbl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDbl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminStarPoly (k := k) z z' l)).1
lemma qDbl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDbl z z' l) = star (Dmin k r z z' g l) :=
  ((Classical.choose_spec (dminStarPoly (k := k) z z' l)).2 g).symm
lemma qGf_deg (z z' : Fin (2 * r + k + 1) → ℂ) : (qGf (k := k) z z').totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (gfPoly (k := k) z z')).1
lemma qGf_eval (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    eval (vars g) (qGf z z') = ((Gf k r z z' g : ℝ) : ℂ) :=
  ((Classical.choose_spec (gfPoly (k := k) z z')).2 g).symm

structure CT (k r nf : ℕ) where
  q : MvPolynomial (Vr (2 * r + k + 1)) ℂ
  a : Fin (r + 2) → ℕ
  b : Fin (r + 2) → ℕ
  c : ℕ
  es : List (Fin nf × List (Mat k r))

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (t : CT k r nf) (g : Mat k r) : ℂ :=
  eval (vars g) t.q * C6.monoM D t.a t.b t.c g

def cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t : CT k r nf) (g : Mat k r) :
    C6.EndH Wp Wq :=
  cvs D t g • C6.Epart fib t.es g

def dscal (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  [{ t with q := dP X t.q }] ++
  List.ofFn (fun l : Fin (r + 2) => if t.a l = 0 then { t with q := 0 } else
    { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) ++
  List.ofFn (fun l : Fin (r + 2) => if t.b l = 0 then { t with q := 0 } else
    { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) ++
  [if t.c = 0 then { t with q := 0 } else { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }]

def dfib {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  List.ofFn (fun i : Fin t.es.length => { t with es := t.es.set i ((t.es.get i).1, X :: (t.es.get i).2) })

def dco (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  dscal D X t ++ dfib X t

end vals

lemma hasDerivAt_invpow' {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) {a : ℕ} (h0 : a = 0 ∨ c 0 ≠ 0) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  cases a with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | succ n =>
    have hc0 : c 0 ≠ 0 := h0.resolve_left (Nat.succ_ne_zero n)
    have h2 := ((hasDerivAt_inv hc0).pow (n + 1)).comp (0 : ℝ) hc
    have h3 : HasDerivAt (fun t => (c t)⁻¹ ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (c 0)⁻¹ ^ (n + 1 - 1) * -(c 0 ^ 2)⁻¹ * c') 0 := h2
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

lemma hasDerivAt_polyD (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => Dmin k r z z' (crv (false, X) g t) l) (eval (vars g) (dP X (qDl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDl (k := k) z z' l)
  simp only [qDl_eval] at h
  exact h

lemma hasDerivAt_polyDb (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => star (Dmin k r z z' (crv (false, X) g t) l)) (eval (vars g) (dP X (qDbl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDbl (k := k) z z' l)
  simp only [qDbl_eval] at h
  exact h

lemma hasDerivAt_polyG (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t => ((Gf k r z z' (crv (false, X) g t) : ℝ) : ℂ)) (eval (vars g) (dP X (qGf z z'))) 0 := by
  have h := hasDerivAt_poly X g (qGf (k := k) z z')
  simp only [qGf_eval] at h
  exact h

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def fct (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) : ℂ :=
  (Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ b l

lemma monoM_eq (D : RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : Mat k r) :
    C6.monoM D a b c g = (∏ l, fct D.z D.z' a b g l) * ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c := rfl

lemma prod_update_a (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ (a l + 1) * (star (Dmin k r z z' g l))⁻¹ ^ b l) =
      ∏ j, fct z z' (a + Pi.single l 1) b g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

lemma prod_update_b (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ (b l + 1)) =
      ∏ j, fct z z' a (b + Pi.single l 1) g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

theorem hasDerivAt_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X g : Mat k r) (t : CT k r nf)
    (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) :
    HasDerivAt (fun s => cvs D t (crv (false, X) g s)) (((dscal D X t).map fun t' => cvs D t' g).sum) 0 := by

  have hF : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))), HasDerivAt (fun s => fct D.z D.z' t.a t.b (crv (false, X) g s) l)
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1)))
      0 := by
    intro l _
    have ha : t.a l = 0 ∨ Dmin k r D.z D.z' (crv (false, X) g 0) l ≠ 0 := by
      rw [crv_zero]; by_cases h : t.a l = 0
      · exact Or.inl h
      · exact Or.inr (hnz l (Or.inl h))
    have hb : t.b l = 0 ∨ star (Dmin k r D.z D.z' (crv (false, X) g 0) l) ≠ 0 := by
      rw [crv_zero]; by_cases h : t.b l = 0
      · exact Or.inl h
      · exact Or.inr (star_ne_zero.2 (hnz l (Or.inr h)))
    have h1 := hasDerivAt_invpow' (hasDerivAt_polyD X g D.z D.z' l) ha
    have h2 := hasDerivAt_invpow' (hasDerivAt_polyDb X g D.z D.z' l) hb
    have := h1.fun_mul h2
    simpa only [fct, crv_zero] using this
  have hprod := HasDerivAt.fun_finsetProd hF
  have hGd := hasDerivAt_invpow' (hasDerivAt_polyG X g D.z D.z') (a := t.c) (by
    rw [crv_zero]; by_cases h : t.c = 0
    · exact Or.inl h
    · exact Or.inr (hG h))
  have hP := hasDerivAt_poly X g t.q
  have hall := hP.fun_mul (hprod.fun_mul hGd)
  have hfun : (fun s => cvs D t (crv (false, X) g s)) = fun s => eval (vars (crv (false, X) g s)) t.q *
      ((∏ l ∈ Finset.univ, fct D.z D.z' t.a t.b (crv (false, X) g s) l) * ((Gf k r D.z D.z' (crv (false, X) g s) : ℝ) : ℂ)⁻¹ ^ t.c) := by
    funext s; simp [cvs, monoM_eq]
  rw [hfun]
  refine hall.congr_deriv ?_

  simp only [crv_zero]
  set P0 := eval (vars g) t.q
  set G0 := ((Gf k r D.z D.z' g : ℝ) : ℂ)
  set dG := eval (vars g) (dP X (qGf D.z D.z'))
  have hsum : ∑ l ∈ (Finset.univ : Finset (Fin (r + 2))), (∏ j ∈ Finset.univ.erase l, fct D.z D.z' t.a t.b g j) •
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1))) =
      ∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) +
      ∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← prod_update_a, ← prod_update_b, smul_eq_mul]
    ring
  have hcq : cvs D { t with q := dP X t.q } g =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) := by
    simp [cvs, monoM_eq, G0]
  have hca : ∀ l, cvs D (if t.a l = 0 then { t with q := 0 } else
      { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) g =
      -(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcb : ∀ l, cvs D (if t.b l = 0 then { t with q := 0 } else
      { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) g =
      -(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcc : cvs D (if t.c = 0 then { t with q := 0 } else
      { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }) g =
      -(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1)) := by
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0, dG]; try ring
  have hlist : ((dscal D X t).map fun t' => cvs D t' g).sum =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) +
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) +
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) +
      (-(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1))) := by
    simp only [dscal, List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
      List.sum_cons, List.sum_nil, List.sum_ofFn, add_zero, Function.comp_def, hcq, hca, hcb, hcc]
    try ring
  rw [hlist, hsum]
  have eA : P0 * (∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) *
      ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  have eB : P0 * (∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) *
      ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  linear_combination eA + eB

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma Rw_cons' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Mat k r) (w : List (Mat k r))
    (f : Mat k r → E) : Rw (X :: w) f = Dx (false, X) (Rw w f) := by
  rfl

lemma ckOn_Rw_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)} {f : Mat k r → E}
    (hf : CkOn ⊤ UU f) {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) : CkOn ⊤ UU (Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    rw [Rw_cons']
    have h := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    exact CkOn_Dx (x := (false, X)) (hw X (by simp)) (by simpa using h)

theorem hasDerivAt_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) →
      HasDerivAt (fun s => C6.Epart fib es (crv (false, X) g s))
        (∑ i : Fin es.length, C6.Epart fib (es.set i ((es.get i).1, X :: (es.get i).2)) g) 0 := by
  intro es
  induction es with
  | nil =>
    intro _
    simp only [C6.Epart, List.map_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  | cons e es ih =>
    intro hes
    have h1 : HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s)) (Rw (X :: e.2) (fib e.1) g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX
        (sCkOn_mono le_top (ckOn_Rw_top (hfib e.1) (hes e (by simp)))) hg hg.1
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.mul h2
    show HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s) * C6.Epart fib es (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    have key : ∀ f : Fin (e :: es).length → C6.EndH Wp Wq,
        ∑ i, f i = f ⟨0, by simp⟩ + ∑ i : Fin es.length, f i.succ := fun f => Fin.sum_univ_succ f
    rw [key, crv_zero]
    simp [C6.Epart, Finset.mul_sum]

lemma list_sum_apply {α : Type*} (L : List α) (f : α → C6.EndH Wp Wq) (x : Wq →L[ℂ] Wp) :
    (L.map f).sum x = (L.map fun t => f t x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma list_sum_smul {α : Type*} (L : List α) (f : α → ℂ) (E : C6.EndH Wp Wq) :
    (L.map fun t => f t • E).sum = (L.map f).sum • E := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, add_smul]

lemma dscal_es (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) :
    ∀ t' ∈ dscal D X t, t'.es = t.es := by
  intro t' ht'
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h <;> (try split_ifs) <;> rfl

theorem hasDerivAt_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D)
    (t : CT k r nf) (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) (hes : ∀ e ∈ t.es, ∀ Y ∈ e.2, inLie k r Y) :
    HasDerivAt (fun s => cv D fib t (crv (false, X) g s)) (((dco D X t).map fun t' => cv D fib t' g).sum) 0 := by
  have h1 := hasDerivAt_cvs D X g t hnz hG
  have h2 := hasDerivAt_epart D fib hfib hX hg t.es hes
  have h3 := h1.smul h2
  show HasDerivAt (fun s => cvs D t (crv (false, X) g s) • C6.Epart fib t.es (crv (false, X) g s)) _ 0
  refine h3.congr_deriv ?_
  rw [crv_zero, dco, List.map_append, List.sum_append, add_comm]
  symm
  congr 1
  · rw [← list_sum_smul]
    exact congrArg List.sum (List.map_congr_left (fun t' ht' => by simp only [cv, dscal_es D X t t' ht']))
  · simp only [dfib, List.map_ofFn, List.sum_ofFn, Function.comp_def, cv, cvs, Finset.smul_sum]

abbrev FS (k r nf : ℕ) : Type := List (CT k r nf × List (Mat k r))

def shape (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (L : FS k r nf) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (L.map fun e => cv D fib e.1 g (Rw e.2 F g)).sum

def stepOne (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) : FS k r nf :=
  (dco D X e.1).map (fun t' => (t', e.2)) ++ [(e.1, X :: e.2)]

def step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (L : FS k r nf) : FS k r nf := L.flatMap (stepOne D X)

def steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L : FS k r nf) : FS k r nf := w.foldr (step D) L

def Good {nf : ℕ} (L : Finset (Fin (r + 2))) (e : CT k r nf × List (Mat k r)) : Prop :=
  (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → l ∈ L ∨ l = Fin.last (r + 1)) ∧
  (∀ x ∈ e.1.es, ∀ Y ∈ x.2, inLie k r Y) ∧ (∀ Y ∈ e.2, inLie k r Y)

private lemma dscal_support_prop_of_support_prop (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf)
    (P : Fin (r + 2) → Prop) (hP : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → P l) :
    ∀ t' ∈ dscal D X t, ∀ l, (t'.a l ≠ 0 ∨ t'.b l ≠ 0) → P l := by
  intro t' ht' l hl
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h
  · exact hP l hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inl hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inr hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl <;> exact hP l hl

lemma good_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {X : Mat k r} (hX : inLie k r X)
    {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    ∀ e' ∈ stepOne D X e, Good L e' ∧ e'.2.length ≤ e.2.length + 1 := by
  unfold Good at he ⊢
  obtain ⟨hab, hes, hw⟩ := he
  intro e' he'
  simp only [stepOne, List.mem_append, List.mem_map, List.mem_singleton] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · refine ⟨⟨?_, ?_, hw⟩, by simp⟩
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · exact dscal_support_prop_of_support_prop D X e.1 _ hab t' ht'
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        exact hab
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · rw [dscal_es D X e.1 t' ht']; exact hes
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        intro x hx Y hY
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hes x hx Y hY
        · rcases List.mem_cons.1 hY with rfl | hY
          · exact hX
          · exact hes _ (by simp) Y hY
  · refine ⟨⟨hab, hes, ?_⟩, by simp⟩
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact hX
    · exact hw Y hY

lemma good_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ (Lf : FS k r nf), (∀ e ∈ Lf, Good L e) →
      ∀ e' ∈ steps D w Lf, Good L e' ∧ ∃ e ∈ Lf, e'.2.length ≤ e.2.length + w.length := by
  intro w
  induction w with
  | nil =>
    intro _ Lf hLf e' he'
    exact ⟨hLf e' he', e', he', by simp⟩
  | cons X w ih =>
    intro hw Lf hLf e' he'
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨hg, e, he, hlen⟩ := ih hw' Lf hLf e'' he''
    obtain ⟨hg', hlen'⟩ := good_step D hX hg e' he'
    refine ⟨hg', e, he, ?_⟩
    simp only [List.length_cons]
    omega

end Formalism.FourierDecayAlt.P.MinorPolynomials
