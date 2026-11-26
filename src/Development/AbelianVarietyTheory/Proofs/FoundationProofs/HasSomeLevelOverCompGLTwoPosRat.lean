module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangular
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNQ

theorem qAll_affine : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  intro E N a d b f hE hN ha hd hf
  obtain ⟨c, hc, hcE⟩ := hf
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (((k : ℚ) * b / (N * d) : ℚ) : ℂ))
  refine ⟨fun m => if a ∣ m then c (m / a) * e (m / a) else 0, ?_, ?_⟩
  · intro τ
    have hz : 0 < (((a : ℂ) * τ + b) / d).im := by
      have : (((a : ℂ) * τ + b) / d).im = a * τ.im / d := by
        simp [Complex.div_ofReal_im]
      rw [this]; have := τ.im_pos; positivity
    have hτ := hc (UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hτ
    have hinj : Function.Injective (fun k : ℕ => a * k) := fun x y h => by
      simpa [ha.ne'] using h
    rw [← hinj.hasSum_iff]
    · show HasSum (fun k => _) (f _)
      convert hτ using 1
      funext k
      simp only [Function.comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ ha, e]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
      exact congrArg f (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    · intro m hm
      have : ¬ a ∣ m := by
        rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩
      simp [this]
  · intro m
    by_cases h : a ∣ m
    · simp only [h, if_true]
      exact E.mul_mem (hcE _) (hE _)
    · simp only [h, if_false]; exact E.zero_mem

end GlobalTheory.FNQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangularStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNQ.qAll_affine | exact GlobalTheory.FNQ.qAll_affine | (intros; apply GlobalTheory.FNQ.qAll_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNPole

theorem qAll_monomial (E : Subring ℂ) (M k : ℕ) :
    QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  refine ⟨fun n => if n = k then 1 else 0, fun τ => ?_, fun n => ?_⟩
  · have := hasSum_single (f := fun n : ℕ => (if n = k then (1 : ℂ) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / M)) k (fun n hn => by simp [hn])
    simpa using this
  · dsimp only; split_ifs
    · exact E.one_mem
    · exact E.zero_mem

theorem qAll_of_int (E : Subring ℂ) {f : ℍ → ℂ} (h : ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 f fun n => (c n : ℂ)) :
    QAll (· ∈ E) 1 f := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨_, hc, fun n => intCast_mem E (c n)⟩

theorem qAll_congr {p : ℂ → Prop} {N : ℕ} {f g : ℍ → ℂ} (hf : QAll p N f) (h : ∀ τ, f τ = g τ) :
    QAll p N g := by
  have : f = g := funext h
  exact this ▸ hf

theorem qAll_pole_affine : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ),
    (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d →
    QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) →
    QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  intro E N w a d b φ hE hN ha hd hφ
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hM : 0 < N * (a * (d' + 1)) := by positivity
  have RC := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed E (N * (a * (d' + 1))) hM
  obtain ⟨hDq, hqD⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  have h1 := QAll.of_dvd hM ⟨a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E N a (d' + 1) b _ hE hN ha (by omega) hφ)
  have h2 := QAll.of_dvd hM ⟨N * a, by ring⟩ E.zero_mem
    (GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular E 1 a (d' + 1) b _ hE one_pos ha (by omega) (qAll_of_int E hqD))
  have h3 := QAll.of_dvd hM (one_dvd _) E.zero_mem (qAll_of_int E hDq)
  have h2w := RC.2.2.2.2.1 _ w h2
  have h3w := RC.2.2.2.2.1 _ (w * (a * (d' + 1))) h3
  have h4 := RC.1 _ (hE (-((w : ℚ) * b) / (d' + 1)))
  have h5 := qAll_monomial E (N * (a * (d' + 1))) (N * w * a * a * (d' * (d' + 2)))
  have hP := RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ (RC.2.2.2.1 _ _ h1 h2w) h3w) h4) h5
  refine qAll_congr hP fun τ => ?_
  simp only [up]
  set U := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)) with hUdef
  have him : 0 < (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im := by
    have : (((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ)).im = a * τ.im / (d' + 1) := by
      rw [Complex.div_natCast_im]; simp
    rw [this]; have := τ.im_pos; positivity
  have hU : (U : ℂ) = ((a : ℂ) * τ + b) / ((d' + 1 : ℕ) : ℂ) := by
    rw [hUdef, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have key : Complex.exp (2 * Real.pi * Complex.I * (U : ℂ)) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (w * (a * (d' + 1))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hU]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hd' : (d' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d')
    push_cast
    field_simp
    ring
  have hDU := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero U
  have hDτ := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have e1 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (U : ℂ))
  have e2 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))
  have e3 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (((-((w : ℚ) * b) / (d' + 1) : ℚ)) : ℂ))
  have e4 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * ((N * w * a * a * (d' * (d' + 2)) : ℕ) : ℂ) * τ /
        ((N * (a * (d' + 1)) : ℕ) : ℂ))
  rw [div_pow, div_pow, ← key]
  field_simp

end GlobalTheory.FNPole
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubstStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) → QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNPole.qAll_pole_affine | exact GlobalTheory.FNPole.qAll_pole_affine | (intros; apply GlobalTheory.FNPole.qAll_pole_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruence
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

open Matrix CongruenceSubgroup


set_option backward.isDefEq.respectTransparency false in
theorem conj_Gamma_den_mul (g : GL (Fin 2) ℚ) (M : ℕ) (y : SL(2, ℤ))
    (hy' : y ∈ Gamma ((g.1.den * (g⁻¹).1.den) * M)) :
    ∃ z ∈ Gamma M, ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      g.1 * ((y : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (g⁻¹).1 := by
  obtain ⟨y, hy⟩ := y
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, hz_coe⟩
  rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  change z.map (Int.cast : ℤ → ZMod M) = 1
  ext i j
  change (↑((1 : Matrix (Fin 2) (Fin 2) ℤ) i j +
    M • (A₁.num * k * A₂.num) i j) : ZMod M) = (1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j
  simp [nsmul_eq_mul, Matrix.one_apply]

theorem exists_conj_principal_congruence :
    ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n),
      ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  intro g
  let G : GL (Fin 2) ℚ := g
  refine ⟨G.1.den * (G⁻¹).1.den, Nat.mul_pos (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)) (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)), fun N δ hδ => ?_⟩
  rw [mul_comm] at hδ
  obtain ⟨z, hz, hzc⟩ := conj_Gamma_den_mul G N δ hδ
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h21 : (G⁻¹).1 * G.1 = 1 := by
    simp only [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  show G.1 * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
    ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) * G.1
  have e1 : ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  have e2 : ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  rw [e1, e2, hzc, Matrix.mul_assoc, h21, Matrix.mul_one]

end GlobalTheory.FN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruenceStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRat_conj_principal_congruence : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n), ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  first | exact @GlobalTheory.FN.exists_conj_principal_congruence | exact GlobalTheory.FN.exists_conj_principal_congruence | (intros; apply GlobalTheory.FN.exists_conj_principal_congruence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobius
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobius
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HermFN

lemma lin_ne_zero (c e : ℤ) (z : ℂ) (hz : 0 < z.im) (h : c ≠ 0 ∨ e ≠ 0) : (c : ℂ) * z + e ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hc
  · subst hc; simp at hre; rcases h with h | h <;> simp_all
  · linarith

lemma common_den (g : GQ) : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (N : ℚ) * ent g i j = z := by
  refine ⟨∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (ent g i j).den_pos))
  · intro i j
    have hdv : (ent g i j).den ∣ ∏ i : Fin 2, ∏ j : Fin 2, (ent g i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (ent g i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin 2, (ent g i j).den) (Finset.mem_univ i))
    obtain ⟨k, hk⟩ := hdv
    refine ⟨k * (ent g i j).num, ?_⟩
    rw [hk]
    have := Rat.mul_den_eq_num (ent g i j)
    push_cast
    rw [← this]; ring

lemma upper_step (p p' x b dd q : ℤ) (a : ℕ) (τ : ℂ) (hd0 : (dd : ℂ) ≠ 0) (hpC : (p : ℂ) = a * p')
    (hq'C : (p' : ℂ) * b + x * dd = q) :
    ((p' : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((x : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
  rw [hpC, ← hq'C]; field_simp; ring

lemma left_step (m0 m1 A B C D : ℤ) (N : ℕ) (τ : ℂ) (hN : (N : ℂ) ≠ 0) (hD : (C : ℂ) * τ + D ≠ 0) :
    (m0 : ℂ) / N * (((A : ℂ) * τ + B) / ((C : ℂ) * τ + D)) + (m1 : ℂ) / N =
      (((m0 * A + m1 * C : ℤ) : ℂ) * τ + ((m0 * B + m1 * D : ℤ) : ℂ)) / (N * ((C : ℂ) * τ + D)) := by
  have hD' : τ * (C : ℂ) + D ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero hN hD)]
  push_cast
  field_simp
  ring

end GlobalTheory.HermFN

namespace GlobalTheory.HermFN

theorem hermite (g : GQ) : ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧
    ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  obtain ⟨N, hN, hm⟩ := common_den g
  choose m hm using hm
  have hdetg : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
    have h := g.2
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  set nI : ℤ := m 0 0 * m 1 1 - m 0 1 * m 1 0 with hnI
  have hn : 0 < nI := by
    have hq : (nI : ℚ) = (N : ℚ) ^ 2 * (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0) := by
      rw [hnI]; push_cast; rw [← hm 0 0, ← hm 0 1, ← hm 1 0, ← hm 1 1]; ring
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (0 : ℚ) < nI := by rw [hq]; positivity
    exact_mod_cast this
  refine ⟨nI.toNat, by omega, ?_⟩
  intro γ₀
  have hdet0 : γ₀ 0 0 * γ₀ 1 1 - γ₀ 0 1 * γ₀ 1 0 = 1 := by
    have := γ₀.2; rwa [Matrix.det_fin_two] at this
  set p : ℤ := m 0 0 * γ₀ 0 0 + m 0 1 * γ₀ 1 0 with hp_def
  set r : ℤ := m 1 0 * γ₀ 0 0 + m 1 1 * γ₀ 1 0 with hr_def
  set q : ℤ := m 0 0 * γ₀ 0 1 + m 0 1 * γ₀ 1 1 with hq_def
  set s : ℤ := m 1 0 * γ₀ 0 1 + m 1 1 * γ₀ 1 1 with hs_def
  have hps : p * s - q * r = nI := by
    rw [hp_def, hr_def, hq_def, hs_def, hnI]; linear_combination (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hdet0
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hps; omega
  set a : ℕ := Int.gcd p r with ha_def
  have ha : 0 < a := Int.gcd_pos_iff.mpr hpr
  set p' : ℤ := p / a
  set r' : ℤ := r / a
  have hp : p = a * p' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left p r)).symm
  have hr : r = a * r' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right p r)).symm
  have cop : IsCoprime p' r' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd ha)
  obtain ⟨γ, h0, h1⟩ := cop.exists_SL2_col 0
  have hγ : p' * γ 1 1 - γ 0 1 * r' = 1 := by
    have := γ.2; rw [Matrix.det_fin_two, h0, h1] at this; linear_combination this
  set b : ℤ := γ 1 1 * q - γ 0 1 * s with hb_def
  set dd : ℤ := p' * s - r' * q with hdd_def
  have had : (a : ℤ) * dd = nI := by
    rw [hdd_def, ← hps]; linear_combination (-s) * hp + q * hr
  have hd : 0 < dd := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith
  have hq' : p' * b + γ 0 1 * dd = q := by rw [hb_def, hdd_def]; linear_combination q * hγ
  have hs' : r' * b + γ 1 1 * dd = s := by rw [hb_def, hdd_def]; linear_combination s * hγ
  refine ⟨γ, a, dd.toNat, b, ?_, ?_⟩
  · zify; rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hn.le]; exact had
  · intro τ
    have hz : 0 < (τ : ℂ).im := τ.im_pos
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hdC : ((dd.toNat : ℕ) : ℂ) = (dd : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hd.le]
    have hd0 : (dd : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc : ∀ i j, ((ent g i j : ℚ) : ℂ) = (m i j : ℂ) / N := by
      intro i j
      have : ent g i j = (m i j : ℚ) / N := by
        rw [← hm i j]; field_simp
      rw [this]; push_cast; rfl
    have hD0 : ((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ) ≠ 0 := by
      apply lin_ne_zero _ _ _ hz
      by_contra h; push_neg at h; rw [h.1, h.2] at hdet0; simp at hdet0
    have hRS : (r : ℂ) * τ + s ≠ 0 := lin_ne_zero r s _ hz hrs
    have hpC : (p : ℂ) = a * p' := by exact_mod_cast hp
    have hrC : (r : ℂ) = a * r' := by exact_mod_cast hr
    have hq'C : (p' : ℂ) * b + γ 0 1 * dd = q := by exact_mod_cast hq'
    have hs'C : (r' : ℂ) * b + γ 1 1 * dd = s := by exact_mod_cast hs'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hdC]
    simp only [mob, hc, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    have eL : ((m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N) /
        ((m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N)
        = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
      have e1 : (m 0 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 0 1 : ℂ) / N
          = ((p : ℂ) * τ + q) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 0 0) (m 0 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      have e2 : (m 1 0 : ℂ) / N * ((((γ₀ 0 0 : ℤ) : ℂ) * τ + ((γ₀ 0 1 : ℤ) : ℂ)) / (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) + (m 1 1 : ℂ) / N
          = ((r : ℂ) * τ + s) / (N * (((γ₀ 1 0 : ℤ) : ℂ) * τ + ((γ₀ 1 1 : ℤ) : ℂ))) := by
        exact left_step (m 1 0) (m 1 1) (γ₀ 0 0) (γ₀ 0 1) (γ₀ 1 0) (γ₀ 1 1) N τ hNC hD0
      rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hNC hD0)]
    have eR : ((γ 0 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 0 1 : ℤ) : ℂ) = ((p : ℂ) * τ + q) / dd := by
      rw [h0]; exact upper_step p p' (γ 0 1) b dd q a τ hd0 hpC hq'C
    have eR2 : ((γ 1 0 : ℤ) : ℂ) * (((a : ℂ) * τ + b) / dd) + ((γ 1 1 : ℤ) : ℂ) = ((r : ℂ) * τ + s) / dd := by
      rw [h1]; exact upper_step r r' (γ 1 1) b dd s a τ hd0 hrC hs'C
    have hofSL : ∀ i j, ((ent (ofSL γ) i j : ℚ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
      intro i j; show (((γ i j : ℤ) : ℚ) : ℂ) = _; push_cast; rfl
    simp only [hofSL]
    rw [eL, eR, eR2, div_div_div_cancel_right₀ hd0]

end GlobalTheory.HermFN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobiusStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧ ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.HermFN.hermite | exact GlobalTheory.HermFN.hermite | (intros; apply GlobalTheory.HermFN.hermite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRat
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_mul_le (m k : ℕ) : CongruenceSubgroup.Gamma (m * k) ≤ CongruenceSubgroup.Gamma m := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c := fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) =>
    congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ _ h1
  · simpa using c _ _ h2
  · simpa using c _ _ h3
  · simpa using c _ _ h4

theorem inR_cmp : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  intro E g f hE ⟨N, w, hN, hinv, hexp⟩
  obtain ⟨n₁, hn₁, hH⟩ := GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g
  obtain ⟨n₂, hn₂, hC⟩ := GlobalTheory.T.glTwoPosRat_conj_principal_congruence g
  obtain ⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩
  · intro δ hδ τ
    have hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂) := by
      have : N * n₁ * n₂ = N * n₂ * n₁ := by ring
      rw [this] at hδ
      exact gamma_mul_le _ _ hδ
    obtain ⟨δ', hδ'm, hgδ⟩ := hC N δ hδ'
    have e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ) := by
      rw [cmp_mul, cmp_sl]
    have e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f := by
      rw [cmp_mul, cmp_sl]
      congr 1
      funext σ
      exact hinv δ' hδ'm σ
    have := congrFun (e1.symm.trans (hgδ ▸ e2)) τ
    exact this
  · intro γ₀
    obtain ⟨γ, a, d, b, had, hmob⟩ := hH γ₀
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have key := GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)
    rw [had] at key
    have hlift := QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _)
      (p := (· ∈ E)) (Subring.zero_mem E) key
    convert hlift using 2 with τ
    congr 1
    have hz : (((a : ℂ) * τ + b) / d).im > 0 := by
      have : (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ) := by
        push_cast; field_simp
      rw [this]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have : (0 : ℝ) < (a : ℝ) / d := by positivity
      have := τ.im_pos
      simp only [UpperHalfPlane.coe_im]
      positivity
    show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)
    have hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) =
        ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) := by
      rw [← mob_sl, hzc]
    simp only [up]
    rw [hmob τ, hm, UpperHalfPlane.ofComplex_apply]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRatStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  first | exact @GlobalTheory.FN.inR_cmp | exact GlobalTheory.FN.inR_cmp | (intros; apply GlobalTheory.FN.inR_cmp <;> assumption)
end
