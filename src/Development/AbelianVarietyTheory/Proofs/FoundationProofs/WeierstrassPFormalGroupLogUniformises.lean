module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * PowerSeries.derivative q - 2 * q = PowerSeries.derivative (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : PowerSeries.derivative l = m + X * PowerSeries.derivative m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : PowerSeries.derivative l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (PowerSeries.derivative Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m)) =
        (subst l (PowerSeries.derivative Q) : PowerSeries K) * PowerSeries.derivative l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add (f := _), map_mul, substAlgHom_X, map_add (f := _), map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      change subst l ((X * PowerSeries.derivative Q - 2 * Q) ^ 2) = _
      rw [← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = PowerSeries.derivative f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.derivative (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * PowerSeries.derivative wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * PowerSeries.derivative wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * PowerSeries.derivative e + e * PowerSeries.derivative wq = 0 := by
    have := congrArg (PowerSeries.derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : PowerSeries.derivative (e + C r * X ^ 2) = PowerSeries.derivative e + C r * (2 * X) := by
    rw [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add (f := _), map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * PowerSeries.derivative e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformisesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_formalGroupLog_uniformises : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  first | exact @GlobalTheory.WpForm.wp_flog | exact GlobalTheory.WpForm.wp_flog | (intros; apply GlobalTheory.WpForm.wp_flog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LocalComponent

theorem exists_idem_away (D : D7) {q : ℕ} (hq : q.Prime) :
    ∃ f ∈ OhE D, f * f = f ∧ sgA D f = f ∧ (∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w) ∧
      ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl q hq.pos
  have h2 : ∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((q : AE D) ^ k * v) * ((q : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have h4 : ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := fun n hn =>
    h3 n (Nat.pos_of_ne_zero (by rintro rfl; exact hq.ne_one (by simpa using hn))) hn.symm
  refine ⟨f, hf, hff, ?_, h2, h4⟩
  have key : f * (1 - sgA D f) = 0 := by
    refine hsep _ fun N hN => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one
    obtain ⟨u, hu, e1⟩ := h2 a
    obtain ⟨v, hv, e2⟩ := h4 n' ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm
    have e3 := congrArg (sgA D) e2
    rw [map_sub, map_one, map_mul, map_natCast] at e3
    refine ⟨u * sgA D v, mul_mem hu (VacMove.sgA_mem D hv), ?_⟩
    rw [e3]
    push_cast
    linear_combination ((n' : AE D) * sgA D v) * e1
  have key' := congrArg (sgA D) key
  rw [map_mul, map_sub, map_one, VacMove.sgA_sgA, map_zero] at key'
  linear_combination key' - key

theorem exists_common_denom (D : D7) {q : ℕ} (hq : q.Prime) {n : ℕ} (y : Fin n → AE D) :
    ∃ a m : ℕ, m.Coprime q ∧ ∀ i, (q : AE D) ^ a * (m : AE D) * y i ∈ OhE D := by
  choose N hN hy using fun i => VacMove.exists_nat_denom D (y i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hN i).ne'
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hP q hq.ne_one
  refine ⟨a, m, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm, fun i => ?_⟩
  obtain ⟨c, hc⟩ : N i ∣ ∏ i, N i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e' : (q : AE D) ^ a * (m : AE D) = (c : AE D) * (N i : AE D) := by
    have := congrArg (Nat.cast : ℕ → AE D) (e.symm.trans hc)
    push_cast at this
    rw [this, mul_comm]
  rw [e', mul_assoc]
  exact mul_mem (natCast_mem _ c) (hy i)

theorem glue_mul {A : Type} [CommRing A] {n : ℕ} {f : A} (hf : f * f = f) {σ τ : Matrix (Fin n) (Fin n) A}
    (h : σ * τ = 1) : ((1 - f) • σ + f • (1 : Matrix (Fin n) (Fin n) A)) * ((1 - f) • τ + f • 1) = 1 := by
  have h1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : f * (1 - f) = 0 := by linear_combination -hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, h1, h2, h3, hf, zero_smul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem mulVec_inc_smul (D : D7) {n : ℕ} (H : Matrix (Fin n) (Fin n) (AE D)) (c : ℕ) (x : Fin n → D.host.E)
    (i : Fin n) : H.mulVec (fun j => inc D (((c : D.host.E) • x) j)) i =
      (c : AE D) * H.mulVec (fun j => inc D (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring


set_option maxHeartbeats 1000000 in
theorem exists_local_component : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  intro D n q hq s hs
  obtain ⟨f, hf, hff, hsg, h2, h3⟩ := exists_idem_away D hq
  have hs' : cT D s * s = 1 := mul_eq_one_comm.1 hs
  have a : s.map (inc D) * (cT D s).map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : (cT D s).map (inc D) * s.map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs', Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AE D) := ⟨_, _, glue_mul hff a, glue_mul hff b⟩
  have hg : g ∈ GA D n := by
    rw [PtsMem.mem_GA]
    have e : ((g : Matrix (Fin n) (Fin n) (AE D)).map (sgA D)).transpose =
        (1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
      ext i j
      change sgA D ((1 - f) * inc D (s j i) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) j i) =
        (1 - f) * inc D (D.host.conj (s j i)) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hsg, PtsMem.sgA_inc]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e]
    exact glue_mul hff b
  refine ⟨⟨g, hg⟩, fun p hp hpq i j => ?_, ?_⟩
  · have hz : ZeroAt D p (1 - f) := fun k => by
      obtain ⟨w, hw, e⟩ := h3 (p ^ k) (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hq).2 hpq))
      exact ⟨1, one_pos, by simp, w, hw, by rw [e]; push_cast; ring⟩
    have := VacMove.zeroAt_mul D hp hz (inc D (s i j) - (1 : Matrix (Fin n) (Fin n) (AE D)) i j)
    convert this using 1
    change (1 - f) * inc D (s i j) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j - _ = _
    ring
  · rintro h B C hB ⟨k, hBC, hCB⟩ ⟨m, hm, hsB, hsC⟩ x
    set H : Matrix (Fin n) (Fin n) (AE D) :=
      (((h : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) with hH
    have hB' : ∀ (c : ℕ) (y : Fin n → D.host.E), (c : D.host.E) • y ∈ B ↔
        ∀ i, (c : AE D) * H.mulVec (fun j => inc D (y j)) i ∈ OhE D := fun c y => by
      rw [hB]
      exact forall_congr' fun i => by rw [mulVec_inc_smul]
    have e : ∀ i, ((((((⟨g, hg⟩ : GA D n) * h : GA D n) : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) :
        Matrix (Fin n) (Fin n) (AE D)).mulVec (fun j => inc D (x j))) i =
        (1 - f) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i + f * H.mulVec (fun j => inc D (x j)) i := by
      intro i
      rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      change H.mulVec (((1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D))).mulVec _) i = _
      have e1 : ((cT D s).map (inc D)).mulVec (fun j => inc D (x j)) = fun j => inc D ((cT D s).mulVec x j) :=
        funext fun j => (RingHom.map_mulVec (inc D) (cT D s) x j).symm
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, e1, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul]
      rfl
    simp only [e]
    constructor
    · intro hx i
      obtain ⟨w, hw, e1⟩ := h3 m hm
      obtain ⟨v, hv, e2⟩ := h2 k
      have m1 := (hB' m _).1 (hsC x hx) i
      have m2 := (hB' (q ^ k) x).1 (by simpa using hCB x hx) i
      have := add_mem (mul_mem hw m1) (mul_mem hv m2)
      convert this using 1
      push_cast
      rw [e1]
      linear_combination H.mulVec (fun j => inc D (x j)) i * e2
    · intro hx
      obtain ⟨a1, n1, hn1, d1⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D ((cT D s).mulVec x j)))
      obtain ⟨a2, n2, hn2, d2⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D (x j)))
      have m1 : (n1 : D.host.E) • (cT D s).mulVec x ∈ B := (hB' n1 _).2 fun i => by
        obtain ⟨v, hv, e2⟩ := h2 a1
        have := add_mem (mul_mem (mul_mem (natCast_mem _ n1) (sub_mem (one_mem _) hf)) (hx i)) (mul_mem hv (d1 i))
        convert this using 1
        linear_combination ((n1 : AE D) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i) * e2 -
          (n1 : AE D) * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have m2 : ((q ^ a2 : ℕ) : D.host.E) • x ∈ B := (hB' (q ^ a2) _).2 fun i => by
        obtain ⟨w, hw, e1⟩ := h3 n2 hn2
        have := add_mem (mul_mem (mul_mem (pow_mem (natCast_mem _ q) a2) hf) (hx i)) (mul_mem hw (d2 i))
        convert this using 1
        push_cast
        linear_combination ((q : AE D) ^ a2 * H.mulVec (fun j => inc D (x j)) i) * e1 +
          (q : AE D) ^ a2 * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have c1 := hsB _ m1
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul] at c1
      have c2 := hBC _ m2
      rw [smul_smul] at c2
      have hcop : IsCoprime ((m * n1 : ℕ) : ℤ) ((q ^ (k + a2) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hm hn1))
      obtain ⟨u, v, huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv' c2
      have := add_mem (zsmul_mem c1 u) (zsmul_mem c2 v)
      convert this using 1
      ext j
      simp only [← Int.cast_smul_eq_zsmul D.host.E, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-x j) * huv'

end GlobalTheory.LocalComponent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrixStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_component_unitary_matrix : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  first | exact @GlobalTheory.LocalComponent.exists_local_component | exact GlobalTheory.LocalComponent.exists_local_component | (intros; apply GlobalTheory.LocalComponent.exists_local_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertResidue

theorem card_of_involution {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q] (s : k →+* k)
    (hs : ∀ x, s (s x) = x) {r : k} {m : ℤ} (hr : r ^ 2 = m) (hsr : s r = -r) (hne : -r ≠ r) :
    (∃ f, Odd f ∧ Nat.card k = q ^ (2 * f)) ∧ ¬ IsSquare (m : ZMod q) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI := Fintype.ofFinite k
  let σ : k ≃ₐ[ZMod q] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s,
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod q) k)) _) c }
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  constructor
  · obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
    set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k with hφ
    change φ ^ j = σ at e
    have ho : orderOf φ = Module.finrank (ZMod q) k := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
    have h2 : φ ^ (2 * j) = 1 := by
      rw [two_mul, pow_add, e]; ext x; exact hs x
    have hsq : (φ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, map_intCast]
    have hev : ∀ i, (φ ^ (2 * i)) r = r := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [mul_add, pow_add, AlgEquiv.mul_apply, mul_one, sq, AlgEquiv.mul_apply]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · rw [h, h, ih]
        · rw [h, map_neg, h, neg_neg, ih]
    have hodd : Odd j := by
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact absurd (by rw [← hsr, ← hσ, ← e, hev]) hne
      · exact ⟨i, rfl⟩
    refine ⟨j, hodd, ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at hd
    have hn : Module.finrank (ZMod q) k = 2 * j := by
      obtain ⟨c, hc⟩ := hd
      have hj0 := hodd.pos
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [Nat.zero_le (Module.finrank (ZMod q) k * c)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), hn, Nat.card_zmod]
  · rintro ⟨c, hc⟩
    have h1 : r ^ 2 = (algebraMap (ZMod q) k c) ^ 2 := by rw [hr, sq, ← map_mul, ← hc, map_intCast]
    apply hne
    rw [← hsr, ← hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp

theorem exists_root (D : D7) (n : ℕ) (b : D.host.E) (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ r : 𝓞 D.host.E, r ^ 2 = ((-(n : ℤ) : ℤ) : 𝓞 D.host.E) ∧ D.host.conj • r = -r := by
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hb]
    exact (isIntegral_natCast n).neg
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  refine ⟨⟨b, hint⟩, RingOfIntegers.ext ?_, RingOfIntegers.ext hconj⟩
  have : (((-(n : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) = ((-(n : ℤ) : ℤ) : D.host.E) :=
    map_intCast (algebraMap (𝓞 D.host.E) D.host.E) _
  rw [this]
  push_cast
  exact hb

theorem two_not_mem (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsPrime) (hsP : ∀ x ∈ P, D.host.conj • x ∈ P) :
    (2 : 𝓞 D.host.E) ∉ P := by
  intro h2
  have hw : D.host.conj • (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := by
    rw [← Formalism.L2.Pj.conj_w0E D]
    exact RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D (Formalism.L2.Pj.w0E D)).symm
  have hsq := Formalism.L2.Pj.w0E_sq D
  obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
    have h1 := D.host.hyp.2.2.2.1
    have h3 := Formalism.L2.Pj.mE_spec D
    exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
  rw [hk] at hsq
  push_cast at hsq
  set w := Formalism.L2.Pj.w0E D
  have hm : w * (1 - w) ∈ P := by
    have : w * (1 - w) = k * 2 := by linear_combination -hsq
    rw [this]; exact P.mul_mem_left _ h2
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hP.mem_or_mem hm with h | h
  · have h' := hsP _ h
    rw [hw] at h'
    simpa using P.add_mem h h'
  · have h' := hsP _ h
    rw [smul_sub, smul_one, hw] at h'
    simpa using P.add_mem h h'

theorem card_of_root (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hfix : D.host.conj • P = P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 D.host.E) ∈ P) (n : ℕ) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    (∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f)) ∧ ¬ IsSquare (-(n : ZMod q)) := by
  have hsP : ∀ x ∈ P, D.host.conj • x ∈ P := fun x hx => by
    rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  obtain ⟨r, hr, hsr⟩ := exists_root D n b hb
  haveI := Fact.mk hq
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI : CharP (𝓞 D.host.E ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hqP)
  let c := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj
  let s : 𝓞 D.host.E ⧸ P →+* 𝓞 D.host.E ⧸ P := Ideal.quotientMap P c hsP
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (D.host.conj • x) := fun _ => rfl
  have h := card_of_involution (q := q) s (r := Ideal.Quotient.mk P r) (m := -(n : ℤ))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, smul_smul, VacInt.conj_mul_self, one_smul])
    (by rw [← map_pow, hr, map_intCast]) (by rw [hs, hsr, map_neg])
    (fun h => by
      rw [← map_neg, Ideal.Quotient.eq] at h
      have h2 : 2 * r ∈ P := by
        have := P.neg_mem h
        convert this using 1
        ring
      have h3 := (hP.isPrime.mem_or_mem h2).resolve_left (two_not_mem D hP.isPrime hsP)
      have hnP : (n : 𝓞 D.host.E) ∈ P := by
        have := P.neg_mem (hr ▸ P.pow_mem_of_mem h3 2 two_pos)
        simpa using this
      obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2
        (huv ▸ P.add_mem (P.mul_mem_left u hqP) (P.mul_mem_left v hnP))))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast at h
  exact h

theorem exists_prime (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    ∃ q n : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ Ideal.absNorm P = q ^ n := by
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ P)
  obtain ⟨q, hc, n, hq, hn⟩ := FiniteField.card' (𝓞 D.host.E ⧸ P)
  refine ⟨q, n, hq, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]

theorem norm_prime : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  intro D P hP
  obtain ⟨q, n, hq, hqP, hn⟩ := exists_prime D hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  by_cases hfix : D.host.conj • P = P
  · have hin : InertQ D q := by
      by_contra h
      exact VacInt.conj_smul_ne D hq h P hP.isPrime hqP hfix
    obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
    have hd' : q ≠ D.host.d → _ := fun h => card_of_root D hP hfix hq hqP D.host.d
      ((Nat.coprime_primes hq hd).2 h) (D.host.sqd)
      (D.host.sqd_sq)
    obtain ⟨f, hf, hN⟩ : ∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f) := by
      by_cases h : q = D.host.d
      · exfalso
        haveI := hP.isPrime
        haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := by
          refine ⟨Ideal.IsMaximal.eq_of_le
            (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible)
            (Ideal.IsPrime.ne_top inferInstance) ?_⟩
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
          exact hqP
        exact D.host.der.decompConj q hq (h ▸ Dvd.intro_left _ rfl) P (MulAction.mem_stabilizer_iff.2 hfix)
      · exact (hd' h).1
    refine ⟨?_, fun _ => ⟨?_, q, f, hq, hin, ?_, hqP, hf, hN, fun h => (hd' h).2⟩, fun h => absurd hfix h⟩
    · intro p _ _
      rw [hN, Nat.factorization_pow]
      simp [Nat.even_mul]
    · have hf0 : 2 * f ≠ 0 := by have := hf.pos; omega
      rw [hN, sgn, hlf, Nat.primeFactors_prime_pow hf0 hq, Finset.filter_singleton, if_pos hin,
        Finset.sum_singleton, Nat.factorization_pow_self hq, Nat.mul_div_cancel_left _ two_pos, hf.neg_one_pow]
    · rintro rfl
      exact two_not_mem D hP.isPrime
        (fun x hx => by rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx) (by exact_mod_cast hqP)
  · have hall : ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ P → ¬ InertQ D p := fun p hp h => hfix (h P hP.isPrime hP0 hp)
    have h0 : ∀ p : ℕ, InertQ D p → (Ideal.absNorm P).factorization p = 0 := fun p hp => by
      rw [hn, hq.factorization_pow, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hall _ hqP hp
    refine ⟨fun p _ hp => by rw [h0 p hp]; exact Even.zero, fun h => absurd h hfix, fun _ => ⟨?_, fun p _ hp => hall p hp⟩⟩
    rw [← sgn_one (D := D)]
    exact sgn_congr fun p _ hp => by rw [h0 p hp]; simp

end GlobalTheory.InertResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSignStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_cmPrime_inertPrime_sign : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  first | exact @GlobalTheory.InertResidue.norm_prime | exact GlobalTheory.InertResidue.norm_prime | (intros; apply GlobalTheory.InertResidue.norm_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem relIndex_ne_zero_of_denom {A ι κ : Type} [CommRing A] [Finite ι] [Finite κ] (S : Subring A) (I : AddSubgroup A) (k n : ℕ)
    (hk : IsUnit (k : A)) (hfin : Finite (S ⧸ Ideal.span {((k * n : ℕ) : S)})) (hn : ∀ s ∈ S, (n : A) * s ∈ I)
    (L T : AddSubgroup (Matrix ι κ A)) (hL : ∀ ζ : Matrix ι κ A, (∀ i j, ζ i j ∈ I) → ζ ∈ L)
    (hT : ∀ ζ ∈ T, ∀ i j, (k : A) * ζ i j ∈ S) : L.relIndex T ≠ 0 := by
  let φ : T →+ (ι → κ → S ⧸ Ideal.span {((k * n : ℕ) : S)}) :=
    AddMonoidHom.mk' (fun ζ i j => Ideal.Quotient.mk _ ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩) (fun x y => by
      funext i j
      rw [Pi.add_apply, Pi.add_apply, ← map_add (f := _)]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
  have hle : φ.ker ≤ L.addSubgroupOf T := by
    intro ζ hζ
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hL _ fun i j => ?_
    have h0 : Ideal.Quotient.mk (Ideal.span {((k * n : ℕ) : S)}) ⟨(k : A) * ζ.1 i j, hT _ ζ.2 i j⟩ = 0 :=
      congrFun (congrFun ((AddMonoidHom.mem_ker).1 hζ) i) j
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : (s : A) * (((k * n : ℕ) : S) : A) = (k : A) * ζ.1 i j := congrArg Subtype.val hs
    have h2 : ζ.1 i j = (n : A) * s := by
      apply hk.mul_left_cancel
      rw [← h1]
      push_cast
      ring
    rw [h2]
    exact hn _ s.2
  have : φ.ker.FiniteIndex := AddSubgroup.finiteIndex_ker φ
  exact (AddSubgroup.finiteIndex_of_le hle).index_ne_zero

theorem idx_latA_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  intro D hD cc δ hc N N' m hm T hT
  obtain ⟨-, -, -, -, ⟨m₁, hm₁, h₁⟩, m₂, hm₂, h₂⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have hk : 0 < m₁ * m := Nat.mul_pos hm₁ hm
  have hu : IsUnit ((m₁ * m : ℕ) : AE D) := by
    have := (IsUnit.mk0 ((m₁ * m : ℕ) : D.host.E) (Nat.cast_ne_zero.2 hk.ne')).map (inc D)
    rwa [map_natCast] at this
  refine relIndex_ne_zero_of_denom (OhE D) (IhE D cc) (m₁ * m) m₂ hu
    (GlobalTheory.HeckeVal.finite_quot D _ (Nat.mul_pos hk hm₂)) h₂ _ _ (fun ζ h => mem_latA.2 h) fun ζ hζ i j => ?_
  have h := h₁ _ (mem_latA.1 (hT ζ hζ) i j)
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc] at h
  rwa [Nat.cast_mul]

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexCompletedStandardNeZeroStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  first | exact @GlobalTheory.FinWeil.idx_latA_ne_zero | exact GlobalTheory.FinWeil.idx_latA_ne_zero | (intros; apply GlobalTheory.FinWeil.idx_latA_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.SplitCharacter

open GlobalTheory.NormSum.VacMove

theorem mem_of_local {G : Type} [AddCommGroup G] (T : AddSubgroup G) (x : G)
    (h : ∀ q : ℕ, q.Prime → ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ T) : x ∈ T := by
  by_contra hx
  have h1 : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ≠ 1 := by
    intro h1
    rw [AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff] at h1
    exact hx h1
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, hm, hT⟩ := h q hq
  have : addOrderOf (QuotientAddGroup.mk x : G ⧸ T) ∣ m := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hT
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm (hd.trans this)

variable {D : D7}

def vanish (D : D7) (q : ℕ) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  zero_mem' := fun k => ⟨1, one_pos, by simp, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨m, hm, hc, s, hs, h⟩ := hx k
    obtain ⟨m', hm', hc', s', hs', h'⟩ := hy k
    refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hc hc', m' * s + m * s',
      add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
    push_cast
    linear_combination (m' : AE D) * h + (m : AE D) * h'
  smul_mem' := fun c x hx => by
    have := zeroAt_mul D hq hx c
    rwa [mul_comm] at this

theorem eq_zero_of_zeroAt (x : AE D) (h : ∀ q : ℕ, q.Prime → ZeroAt D q x) : x = 0 := by
  refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 x fun n hn => ?_
  have : x ∈ (OhE D).toAddSubgroup.map (AddMonoidHom.mulLeft (n : AE D)) := by
    refine mem_of_local _ x fun q hq => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    obtain ⟨m, -, hc, s, hs, h⟩ := h q hq a
    refine ⟨m * n', Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, s, hs, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
    push_cast
    linear_combination -(n' : AE D) * h
  obtain ⟨w, hw, h⟩ := this
  exact ⟨w, hw, h.symm⟩

theorem zeroAt_det {N q : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (h : TrivAt D q g) :
    ZeroAt D q (((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) - 1) := by
  have h1 : (Ideal.Quotient.mk (vanish D q hq)).mapMatrix (g : Matrix (Fin N) (Fin N) (AE D)) =
      (Ideal.Quotient.mk (vanish D q hq)).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

def cutHom {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem exists_split_character : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  intro D N₀ χ N
  obtain ⟨ε, -, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  refine ⟨χ.f.comp ((Units.map (cutHom ε h1)).comp
    ((Matrix.GeneralLinearGroup.det (n := Fin N) (R := AE D)).comp (GA D N).subtype)), fun k hk => ?_, fun g x hx hg => ?_⟩
  · have h0 : ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · have := zeroAt_mul D hq ((h3 q hq).1 hi)
          (ε * (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1))
        convert this using 1
        linear_combination (-(((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1)) * (h1 + h2)
      · rw [mul_comm]
        exact zeroAt_mul D hq (zeroAt_det hq (hk q hq hi)) ε
    have h4 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D))) = 1 := by
      ext
      change (1 - ε) + ε * ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1
      linear_combination h0
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)))) = 1
    rw [h4, map_one]
  · have h0 : (1 - (ε + sgA D ε)) * ((x : AE D) - 1) = 0 := by
      refine eq_zero_of_zeroAt _ fun q hq => ?_
      by_cases hi : InertQ D q
      · rw [mul_comm]
        exact zeroAt_mul D hq (hx q hq hi) _
      · exact zeroAt_mul D hq ((h3 q hq).2 hi) _
    have hs : sgU D (Units.map (cutHom (sgA D ε) h1') x) = Units.map (cutHom ε h1) (sgU D x) := by
      ext
      change sgA D ((1 - sgA D ε) + sgA D ε * x) = (1 - ε) + ε * sgA D x
      rw [map_add (f := _), map_mul, map_sub, map_one, sgA_sgA]
    have h5 : Units.map (cutHom ε h1) x * Units.map (cutHom (sgA D ε) h1') x = x := by
      ext
      change ((1 - ε) + ε * x) * ((1 - sgA D ε) + sgA D ε * x) = (x : AE D)
      linear_combination (1 - (x : AE D)) ^ 2 * h2 - h0
    have h6 : Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) *
        (Units.map (cutHom (sgA D ε) h1') x * sgU D (Units.map (cutHom (sgA D ε) h1') x)) = x := by
      rw [hs, mul_comm (Units.map (cutHom (sgA D ε) h1') x), ← mul_assoc, ← map_mul, ← hg, h5]
    change χ.f (Units.map (cutHom ε h1) (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)))) = χ.f x
    conv_rhs => rw [← h6]
    rw [map_mul, χ.norm, mul_one]

end GlobalTheory.SplitCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroupStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_character_unitary_group : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  first | exact @GlobalTheory.SplitCharacter.exists_split_character | exact GlobalTheory.SplitCharacter.exists_split_character | (intros; apply GlobalTheory.SplitCharacter.exists_split_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCentralCircleDistinctGradedEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCentralCircleDistinctGradedEigen
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedCentralCircle

open GlobalTheory.RealPar

variable {p q : ℕ}

theorem flow_eq {T : GrpData p q} (σ : URep T) {X : Mat p q} (hX : X ∈ upq p q) {w : σ.H} {c : ℂ}
    (h0 : HasDerivAt (fun t : ℝ => σ.π (T.expt (t • X)) w) (c • w) 0) :
    σ.π (T.expt X) w = Complex.exp c • w := by
  set f : ℝ → σ.H := fun t => σ.π (T.expt (t • X)) w with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • w) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • w) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem exp_injective (c : ℂ) : Function.Injective fun m : ℕ => Complex.exp (Complex.I * (c + m)) := by
  intro m n h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h1 : ((m : ℝ) : ℂ) - (n : ℝ) = ((k : ℝ) * 2 * Real.pi : ℝ) := by
    push_cast
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination hk
  have h2 : (m : ℝ) - n = (k : ℝ) * 2 * Real.pi := by exact_mod_cast h1
  by_cases hk0 : k = 0
  · subst hk0
    have : (m : ℝ) = n := by simpa [sub_eq_zero] using h2
    exact_mod_cast this
  · exfalso
    have hi : Irrational (((k * 2 : ℤ) : ℝ) * Real.pi) :=
      irrational_pi.intCast_mul (by omega)
    have : ((k * 2 : ℤ) : ℝ) * Real.pi = ((m - n : ℤ) : ℝ) := by push_cast; linarith
    rw [this] at hi
    exact Int.not_irrational _ hi

theorem exists_central_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  intro p q T σ M j hj N c hN
  set θ : Ix p q → ℝ := Sum.elim (fun _ => 1) (fun _ => 0) with hθ
  have hX := TorusWt.torX_mem θ
  have hK : IsKC (TorusWt.torX θ) := by
    intro a b hab
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [sameBlock] at hab
    simp [TorusWt.torX, this]
  have hk := KStabLie.expt_mem T hX hK 1
  rw [one_smul] at hk
  refine ⟨_, hk, _, exp_injective (c : ℂ), fun m x hx => ?_⟩
  apply flow_eq σ hX
  have h0 := hj _ hX x
  have h1 : M.act (TorusWt.torX θ) x = (Complex.I * ((c : ℂ) + m)) • x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [TorusWt.torX_eq_sum, map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, mul_smul, ← hN m x hx,
      Finset.smul_sum]
    simp [hθ]
  rw [h1, map_smul] at h0
  exact h0

end GlobalTheory.GradedCentralCircle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCentralCircleDistinctGradedEigenStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_circle_distinct_graded_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  first | exact @GlobalTheory.GradedCentralCircle.exists_central_eigen | exact GlobalTheory.GradedCentralCircle.exists_central_eigen | (intros; apply GlobalTheory.GradedCentralCircle.exists_central_eigen <;> assumption)
end
end
