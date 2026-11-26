module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlochKatoDuality

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellInversePair

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨WeylGroupFacts.uh_inv hh.1, fun a => ⟨key _ (hh.2.1 a).1, key _ (hh.2.1 a).2⟩, key _ hh.2.2⟩

def invP (p : SS k r) : SS k r :=
  ((((Matrix.of p.1.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * (Matrix.of p.1.1 : Mat k r) : Mat k r)),
    (((Matrix.of p.2.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ * (Matrix.of p.2.1 : Mat k r) : Mat k r)))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem invP_inSS (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : D.inSS (invP p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  refine ⟨uw_inv h1, ?_, uw_inv h3, ?_⟩
  · have := (uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu1] at this
  · have := (uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu3] at this

theorem sgs_invP (p : SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : Mat k r).det) (hp2 : IsUnit (Matrix.of p.1.2 : Mat k r).det)
    (hp3 : IsUnit (Matrix.of p.2.1 : Mat k r).det) (hp4 : IsUnit (Matrix.of p.2.2 : Mat k r).det) (x : Mat k r) :
    sgs (invP p) (sgs p x) = x := by
  show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ *
      Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x *
      Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ *
      Matrix.of p.2.1) * (Matrix.of p.2.1 : Mat k r)⁻¹ = x
  generalize (Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢
  generalize (Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢
  generalize (Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢
  generalize (Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1,
    Matrix.nonsing_inv_nonsing_inv B hp2]
  simp only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
    Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]

end Formalism.FourierDecayAlt.P.BigCellInversePair

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x5

variable {k r : ℕ}

lemma herm_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : ι → ℂ)
    (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ c, x c • v c) w = ∑ c, x c * herm H (v c) w := by
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma hzz_real (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]; linarith

lemma hzz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  rw [hzz_real]; exact_mod_cast (neg_ne_zero.mpr hz.ne')

lemma herm_f_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    herm (Hpk k r) (fvec k r z c) (bvec (esI k r a)) = if c.val = a.val then 1 else 0 := by
  rw [bvec, ggHerm_bvec_right]
  have hlt : r + k < (esI k r a).val := by simp [esI]; omega
  rw [gn_Hpk_mulVec, dite_eq_left (Or.inr hlt)]
  have e : (⟨2 * r + k - (esI k r a).val, by omega⟩ : Fin (2 * r + k + 1)) = ⟨a.val, by omega⟩ := by
    apply Fin.ext; simp [esI]; omega
  rw [e, fvec_apply_lt z hz c _ (by simp)]

lemma herm_e_alt {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Fin (2 * r + k + 1))
    (hx : x.val < r ∨ r + k < x.val) : herm (Hpk k r) (bvec x) z = 0 := by
  rw [ggHerm_swap (Hpk k r) (GBasic.Hpk_herm k r), bvec, ggHerm_bvec_right, ggHpk_mulVec_Wb k r z hz,
    hz x hx, mul_zero, star_zero]

lemma hermitian_form_flag_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c.val = r then herm (Hpk k r) z z else 0 := by
  unfold fvec
  split_ifs with h1 h2 h2
  · omega
  · exact herm_e_alt hz _ (Or.inl (by simp [eI, h1]))
  · rfl
  · omega

lemma uMap_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (s : B.Mat k r)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c) :
    C2.uMap k r z s = U := by
  ext a b
  unfold C2.uMap
  rw [h b]
  split_ifs with ha
  · rw [herm_sum_smul]
    simp only [herm_f_es hz.1]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (fun e => hc (Fin.ext e)), mul_zero]
    · simp
  · rw [herm_sum_smul]
    simp only [hermitian_form_flag_vector hz.1]
    rw [Finset.sum_eq_single a]
    · rw [if_pos (by have := a.isLt; omega)]
      field_simp [hzz_ne hz.2]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro e; apply hc; apply Fin.ext; have := a.isLt; omega
    · simp

lemma colEq {z : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r} {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : s * Fm k r z = Fm k r z * U) (b : Fin (r + 1)) :
    s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c := by
  funext i
  have := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply] at this
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

end C2x5

open C2x5

theorem unipotent_map_frame : C2.UMapFrame := by
  intro k r z hz
  refine ⟨fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    have hu := uMap_eq hz s U (colEq hsF)
    refine ⟨by rw [hu]; exact colEq hsF, by rw [hu]; exact ⟨fun i j h => hU1 i j h, hU2⟩, fun t ht => ?_⟩
    obtain ⟨Ut, _, _, htF⟩ := S_F hz.1 ht
    have hut := uMap_eq hz t Ut (colEq htF)
    have hst : s * t * Fm k r z = Fm k r z * (U * Ut) := by
      rw [Matrix.mul_assoc, htF, ← Matrix.mul_assoc, hsF, Matrix.mul_assoc]
    rw [uMap_eq hz (s * t) (U * Ut) (colEq hst), hu, hut]
  · have h1 : h * Fm k r z = Fm k r z * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
      rw [UW_F hh, Matrix.mul_one]
    exact uMap_eq hz h 1 (colEq h1)

theorem zhat_equivalence : C2.ZhatEquiv := by
  intro k r z z' hz hz' s hs s' hs' g
  obtain ⟨U, _, _, hsF⟩ := S_F hz.1 hs
  obtain ⟨U', _, _, hs'F⟩ := S_F hz'.1 hs'
  rw [uMap_eq hz s U (colEq hsF), uMap_eq hz' s' U' (colEq hs'F), Zhat_eq, Zhat_eq]
  have hsU : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hu : IsUnit s.det := WeylGroupFacts.isUnit_of_uh hsU
  have hHs : Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
    calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hsU]
      _ = sᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc (Fm k r z)ᴴ * Hpk k r * (s⁻¹ * g * s') * Fm k r z'
      = (Fm k r z)ᴴ * (Hpk k r * s⁻¹) * g * (s' * Fm k r z') := by simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r) * g * (Fm k r z' * U') := by rw [hHs, hs'F]
    _ = (s * Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z * U)ᴴ * Hpk k r * g * Fm k r z' * U' := by rw [hsF]
    _ = Uᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z') * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SandwichRhoAction

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma deriv_comp_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (M : F →L[ℝ] E) (hML : ∀ x, M (L x) = x) (φ : ℝ → E) (t : ℝ) :
    deriv (fun s => L (φ s)) t = L (deriv φ t) := by
  by_cases h : DifferentiableAt ℝ φ t
  · exact (L.hasFDerivAt.comp_hasDerivAt t h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L (φ s)) t := by
      intro hd
      apply h
      have hφ : (fun s => M (L (φ s))) = φ := funext fun s => hML (φ s)
      rw [← hφ]
      exact M.differentiableAt.comp t hd
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (((ContinuousLinearMap.compL ℂ Wq Wp Wp P).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip Q)).restrictScalars ℝ)

lemma sandw_apply (P : Wp →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (A : Wq →L[ℂ] Wp) : sandw P Q A = P.comp (A.comp Q) := rfl

lemma rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (φ : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    rho D p φ x = sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) (φ (sgs p x)) := rfl

lemma sandw_leftInv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (A : Wq →L[ℂ] Wp) :
    sandw (D.π (Matrix.of p.1.1)⁻¹) (D.π' (Matrix.of p.2.1))
      (sandw (D.π (Matrix.of p.1.1)) (D.π' (Matrix.of p.2.1)⁻¹) A) = A := by
  have h1 := hp.1
  have h3 := hp.2.2.1
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have e1 : (D.π (Matrix.of p.1.1)⁻¹).comp (D.π (Matrix.of p.1.1)) = 1 := by
    rw [← D.π_rep.2 _ (WeylGroupFacts.uw_inv h1) _ h1, Matrix.nonsing_inv_mul _ u1, D.π_rep.1]
  have e3 : (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p.2.1)) = 1 := by
    rw [← D.π'_rep.2 _ (WeylGroupFacts.uw_inv h3) _ h3, Matrix.nonsing_inv_mul _ u3, D.π'_rep.1]
  have re : ∀ (P1 P2 : Wp →L[ℂ] Wp) (Q1 Q2 : Wq →L[ℂ] Wq) (B : Wq →L[ℂ] Wp),
      P1.comp ((P2.comp (B.comp Q2)).comp Q1) = (P1.comp P2).comp (B.comp (Q2.comp Q1)) := by
    intros; ext; rfl
  simp only [sandw_apply]
  rw [re, e1, e3]
  ext; rfl

lemma sgs_eq' (p : SS k r) (x : Mat k r) : sgs p x = (sL p)⁻¹ * x * sR p := by
  unfold sgs sL sR
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

lemma isUnit_sL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sL p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1)

lemma isUnit_sR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : IsUnit (sR p).det :=
  WeylGroupFacts.isUnit_of_uh (WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1)

lemma sgs_curveR (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (g * NormedSpace.exp ((t : ℂ) • X)) = sgs p g * NormedSpace.exp ((t : ℂ) • AdR p X) := by
  have hu : IsUnit (sR p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sR D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdR
  have hc : ((t : ℂ) • ((sR p)⁻¹ * X * sR p)) = (sR p)⁻¹ * ((t : ℂ) • X) * sR p := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sR D hp)]

lemma sgs_curveL (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X g : Mat k r) (t : ℝ) :
    sgs p (NormedSpace.exp (-((t : ℂ) • X)) * g) = NormedSpace.exp (-((t : ℂ) • AdL p X)) * sgs p g := by
  have hu : IsUnit (sL p) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_sL D hp)
  rw [sgs_eq', sgs_eq']
  unfold AdL
  have hc : -((t : ℂ) • ((sL p)⁻¹ * X * sL p)) = (sL p)⁻¹ * (-((t : ℂ) • X)) * sL p := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hc]
  first
    | rw [Matrix.exp_conj' _ _ hu]
    | rw [Matrix.exp_conj' ℂ _ _ hu]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_sL D hp)]

lemma rdV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : RdV X (rho D p φ) g = rho D p (RdV (AdR p X) φ) g := by
  unfold RdV
  simp only [rho_eq, sgs_curveR D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma ldV_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Mat k r) (φ : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (rho D p φ) g = rho D p (LdV (AdL p X) φ) g := by
  unfold LdV
  simp only [rho_eq, sgs_curveL D hp]
  exact deriv_comp_of_leftInv _ _ (sandw_leftInv D hp) _ 0

lemma rw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (v : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)), Rw v (rho D p φ) = rho D p (Rw (v.map (AdR p)) φ)
  | [], _ => rfl
  | X :: v, φ => by
    funext g
    show RdV X (Rw v (rho D p φ)) g = rho D p (RdV (AdR p X) (Rw (v.map (AdR p)) φ)) g
    rw [rw_rho D hp v φ, rdV_rho D hp]

lemma lw_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    ∀ (u : List (Mat k r)) (φ : Mat k r → (Wq →L[ℂ] Wp)),
      u.foldr LdV (rho D p φ) = rho D p ((u.map (AdL p)).foldr LdV φ)
  | [], _ => rfl
  | X :: u, φ => by
    funext g
    show LdV X (u.foldr LdV (rho D p φ)) g = rho D p (LdV (AdL p X) ((u.map (AdL p)).foldr LdV φ)) g
    rw [lw_rho D hp u φ, ldV_rho D hp]

theorem dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (u v : List (Mat k r))
    (f : Mat k r → (Wq →L[ℂ] Wp)) : dLR u v (rho D p f) = rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) f) := by
  show u.foldr LdV (Rw v (rho D p f)) = rho D p ((u.map (AdL p)).foldr LdV (Rw (v.map (AdR p)) f))
  rw [rw_rho D hp v f, lw_rho D hp u]

theorem _root_.Formalism.FourierDecayAlt.P.rewrite_rho_action : RwRho := by
  intro k r Wp Wq _ _ _ _ D m f p hp _ u v _ _ _ g _
  exact congrFun (dLR_rho D hp u v f) g

end Formalism.FourierDecayAlt.P.SandwichRhoAction
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
open scoped ComplexConjugate ContDiff
open Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem fsv_mul_fsv_neg (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by
  rw [fsv, fsv, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_neg]
  ring

theorem fsv_neg_mul_fsv (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by
  rw [mul_comm]
  exact fsv_mul_fsv_neg s t

theorem hasFDerivAt_fsv {m : ℕ} (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      D (Pi.single l 1) = (t - conj t) * fsv t (c l) ∧
      D (Pi.single l Complex.I) = Complex.I * (t + conj t) * fsv t (c l) := by
  classical
  let L : (Fin m → ℂ) →L[ℝ] ℂ := t • (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ) -
    (conj t) • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ))
  have hL : ∀ c' : Fin m → ℂ, L c' = t * c' l - conj t * conj (c' l) := by
    intro c'
    simp [L]
  refine ⟨fsv t (c l) • L, ?_, ?_, ?_⟩
  · have h2 := (L.hasFDerivAt (x := c)).cexp
    have he : (fun c' : Fin m → ℂ => fsv t (c' l)) = fun c' => Complex.exp (L c') := by
      funext c'
      rw [hL]
      rfl
    have hc : Complex.exp (L c) = fsv t (c l) := by
      rw [hL]
      rfl
    rw [he, ← hc]
    exact h2
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, map_one, smul_eq_mul]
    ring
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, Complex.conj_I, smul_eq_mul]
    ring

section Leibniz

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l φ c + (t * fsv t (c l)) • φ c ∧
    wirtBar l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • wirtBar l φ c + (-(conj t) * fsv t (c l)) • φ c := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_fsv t l c
  have hP : HasFDerivAt (fun c' => fsv t (c' l) • φ c') (fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c)) c :=
    hD.smul hφ.hasFDerivAt
  unfold wirt wirtBar
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, hI, smul_add, smul_sub, smul_smul, ← mul_assoc, Complex.I_mul_I]
  constructor <;> module

theorem pOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pOp l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • pOp l φ c + t • fsv t (c l) • (c l • φ c) := by
  unfold pOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul t l φ c (hd h)).1]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

theorem pbOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pbOp l (fun c' => fsv (-t) (c' l) • φ c') c =
      fsv (-t) (c l) • pbOp l φ c + conj t • fsv (-t) (c l) • (star (c l) • φ c) := by
  unfold pbOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul (-t) l φ c (hd h)).2]
    simp only [map_neg, neg_neg, Complex.star_def]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

end Leibniz

section Reg

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_regular (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, -⟩ := hΦm
  refine ⟨fun hc => ?_, fun hc => h0 (c, g) (fun hx => hc (by
    simp only [DomR, Set.mem_setOf_eq] at hx
    exact hx.1))⟩
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g) (by
      simp only [DomR, Set.mem_setOf_eq]
      exact ⟨hc, hg.1, hg.2⟩)
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := by fun_prop
    have hev : ∀ᶠ c' in nhds c, (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = F (c', g) := by
      have hU' : ∀ᶠ c' in nhds c, (c', g) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
      filter_upwards [hU'] with c' hc'
      exact hΦ (c', g) hc' hg.1
    have hFd : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (c', g)) c := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun c' => F (c', g)) c := hFd.comp c hpair
    exact hcomp.congr_of_eventuallyEq hev
  · have hz : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      refine h0 (c', g) (fun hx => hg ?_)
      simp only [DomR, Set.mem_setOf_eq] at hx
      exact ⟨hx.2.1, hx.2.2⟩
    rw [hz]
    exact differentiableAt_const 0

end Reg

section PairLemmas

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_ext {a b : Pr V} (h1 : a.1 = b.1) (h2 : a.2.unop = b.2.unop) : a = b :=
  Prod.ext h1 (MulOpposite.unop_injective h2)

@[simp] theorem pr_alg_fst (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
@[simp] theorem pr_alg_snd (w : ℂ) :
    (algebraMap ℂ (Pr V) w).2.unop = algebraMap ℂ (Module.End ℂ V) (conj w) := rfl

end PairLemmas

theorem waveSiteAll : WaveSiteAll := by
  intro Wp Wq _ _ _ _ P z z' π π' X L hL l s Wv Wv' hW hW'
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun i Φ => X.op_apply l i Φ
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]

  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → W * X.op l i = X.op l i * W := by
    intro W u hWu i hi
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hsite : ∀ f : Pr (RadSp P.k P.r z z' π π'), (site L l).p = L.p l ∧ (site L l).c = L.c l ∧
      (site L l).ci = L.ci l := fun _ => ⟨rfl, rfl, rfl⟩
  obtain ⟨hsp, hsc, hsci⟩ := hsite 0
  rw [hsp, hsc, hsci, hp l, hc l, hci l]
  refine ⟨⟨pr_ext ?_ ?_, pr_ext ?_ ?_, rfl⟩, pr_ext ?_ ?_, pr_ext ?_ ?_, pr_ext ?_ ?_⟩
  · exact hWW'
  · exact hWW'
  · exact hW'W
  · exact hW'W
  · exact hcomm Wv _ hW1 1 (by decide)
  · exact (hcomm Wv' _ hW2 4 (by decide)).symm
  · exact hcomm Wv _ hW1 2 (by decide)
  · exact (hcomm Wv' _ hW2 5 (by decide)).symm
  · change X.op l 0 * Wv = Wv * X.op l 0 + algebraMap ℂ _ s * Wv * X.op l 1
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hop, crd, hW1, opL]
    rw [pOp_fsv_smul s l _ c hd h0]
    simp only [cOp]
  · change Wv' * (-X.op l 3) = (-X.op l 3) * Wv' + X.op l 4 * (Wv' * algebraMap ℂ _ (conj s))
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
      Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hop,
      crd, hW2, opL]
    rw [pbOp_fsv_smul s l _ c hd h0]
    simp only [cbOp]
    module

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have heI : ∀ (a : Fin r) (h : (a : ℕ) + 1 < r), eI k r a ≠ eI k r ⟨a + 1, h⟩ := by
    intro a h he
    have := congrArg Fin.val he
    simp [eI] at this
  have hz' : ∀ a : Fin r, z (eI k r a) = 0 := fun a => hz _ (Or.inl (by simp [eI]))
  simp [psi, ell, Matrix.one_apply_ne, heI, hz']

end Formalism.FourierDecayAlt.P.BesselCapelliCommutation

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordIntegralScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (L : ι → E →L[ℂ] E) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => L i (φ i p)).sum) μ ∧
      ∫ p, (l.map fun i => L i (φ i p)).sum ∂μ = (l.map fun i => L i (∫ p, φ i p ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hLi : Integrable (fun p => L i (φ i p)) μ := (L i).integrable_comp hi
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hLi.add hl1, ?_⟩
    rw [integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]

theorem smul_list {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (L : ι → E →L[ℂ] E)
    (x : ι → E) : c • (l.map fun i => L i (x i)).sum = (l.map fun i => L i (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]

variable {k r : ℕ}

theorem lr_nrm (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]

theorem rw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h

end Formalism.FourierDecayAlt.P.WordIntegralScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    calc ‖F (Matrix.of g)‖ * gN (Matrix.of g) ^ A = gN (Matrix.of g) ^ A * ‖F (Matrix.of g)‖ := mul_comm _ _
      _ ≤ c := h1
      _ ≤ |c| := le_abs_self c
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
end
end
