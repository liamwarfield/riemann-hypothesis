module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularAction
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangular
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dite_eq_left hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangularStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ : HahnSeries ℚ Ω,
  qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.qD_sub | exact GlobalTheory.CyclotomicQExpansion.qD_sub | (intros; apply GlobalTheory.CyclotomicQExpansion.qD_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubst
namespace GlobalTheory.CyclotomicQExpansion
open GlobalTheory.KZ

theorem exp_sl_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have hdet : 0 < ent g 0 0 * ent g 1 1 := by
    have h := g.2
    have h' : 0 < Matrix.det ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := h
    rw [Matrix.det_fin_two] at h'
    simp only [ent] at hg ⊢
    rw [hg, mul_zero, sub_zero] at h'
    exact h'
  have hd : ent g 1 1 ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hdet; exact lt_irrefl _ hdet
  have ha : ent g 0 0 ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hdet; exact lt_irrefl _ hdet
  have hpos : 0 < ent g 0 0 / ent g 1 1 := by
    have : ent g 0 0 / ent g 1 1 = (ent g 0 0 * ent g 1 1) / (ent g 1 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hdet (by positivity)
  ext s
  unfold sub scale
  rw [dite_eq_left hpos]
  set e := (OrderIso.mulLeft₀ (ent g 0 0 / ent g 1 1) hpos).toOrderEmbedding with he
  have hs : s = e (s * ent g 1 1 / ent g 0 0) := by
    simp only [he, RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  rw [hs, HahnSeries.embDomain_coeff]
  have key := X.exp_upper g hg f (s * ent g 1 1 / ent g 0 0)
  have h2 : s * ent g 1 1 / ent g 0 0 * ent g 0 0 / ent g 1 1 = e (s * ent g 1 1 / ent g 0 0) := by
    rw [← hs]; field_simp
  rw [h2] at key
  rw [key]
  rfl

end GlobalTheory.CyclotomicQExpansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubstStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ f : X.K,
  X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.exp_sl_upper | exact GlobalTheory.CyclotomicQExpansion.exp_sl_upper | (intros; apply GlobalTheory.CyclotomicQExpansion.exp_sl_upper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularAction
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.DlUp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem sub_coeff (ε : Ω →+* ℂ) {a b d : ℚ} (h : 0 < a / d) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε a b d φ).coeff s = eOm ε ((a / d)⁻¹ * s * b / d) * φ.coeff ((a / d)⁻¹ * s) := by
  have hs : s = (OrderIso.mulLeft₀ (a / d) h).toOrderEmbedding ((a / d)⁻¹ * s) := by
    show s = (a / d) * ((a / d)⁻¹ * s)
    rw [mul_inv_cancel_left₀ h.ne']
  unfold sub scale
  rw [dite_eq_left h]
  conv_lhs => rw [hs]
  rw [HahnSeries.embDomain_coeff]
  rfl

theorem theta_one (φ : HahnSeries ℚ Ω) : theta 1 φ = qD φ := by
  ext r
  simp [theta, qD, cm]

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {y : Ω} {k : ℕ} (hk : k ≠ 0) (hy : y ^ k = 1) : y ∈ A := by
  rw [← A.valuation_le_one_iff]
  by_contra hlt
  push_neg at hlt
  have h := one_lt_pow' hlt hk
  rw [← map_pow, hy, map_one] at h
  exact lt_irrefl _ h

theorem eOm_pow [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hy : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have h' : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x.num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * h'
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  haveI : NeZero x.den := ⟨x.den_nz⟩
  haveI : NeZero (x.den : Ω) := ⟨Nat.cast_ne_zero.2 x.den_nz⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos x.den Ω x.den_pos))
  have hζ : IsPrimitiveRoot z x.den := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hεζ : IsPrimitiveRoot (ε z) x.den := hζ.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := hεζ.eq_pow_of_pow_eq_one hy
  have hrange : ∃ w, ε w = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := ⟨z ^ i, by rw [map_pow, hi]⟩
  have hε : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := Function.invFun_eq hrange
  apply ε.injective
  rw [map_pow, hε, hy, map_one]

theorem eOm_unit [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) :
    eOm ε x ≠ 0 ∧ eOm ε x ∈ A ∧ (eOm ε x)⁻¹ ∈ A := by
  have h := eOm_pow ε x
  refine ⟨fun h0 => ?_, mem_of_pow_eq_one A x.den_nz h, mem_of_pow_eq_one A x.den_nz (by rw [inv_pow, h, inv_one])⟩
  rw [h0, zero_pow x.den_nz] at h
  exact zero_ne_one h

theorem prim_sub [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) {a b d : ℚ} (h : 0 < a / d)
    {ψ : HahnSeries ℚ Ω} (hψ : Prim A ψ) : Prim A (sub ε a b d ψ) := by
  obtain ⟨h1, r, hr0, hr⟩ := hψ
  refine ⟨fun s => ?_, (a / d) * r, ?_, ?_⟩
  · rw [sub_coeff ε h]; exact mul_mem (eOm_unit ε A _).2.1 (h1 _)
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne']; exact mul_ne_zero (eOm_unit ε A _).1 hr0
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne', mul_inv]; exact mul_mem (eOm_unit ε A _).2.2 hr

theorem isDl_sl_upper : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  intro Ω _ _ _ ε X A N l _ n g h10 ha hd hc f φ hdl
  obtain ⟨hφ, a₀, b₀, κ, hκ, hfb, hPa, hPb, hcg⟩ := hdl
  have hpos : 0 < ent g 0 0 / ent g 1 1 := div_pos ha hd
  have hexp : ∀ u, X.exp (X.sl g u) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp u) :=
    fun u => GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst Ω ε X g h10 u
  have hmul := GlobalTheory.T.substUpperTriangularHahn_mul_and_one Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hqd := GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hco := sub_coeff ε (b := ent g 0 1) hpos
  have hss : ∀ ψ χ : HahnSeries ℚ Ω, sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (ψ - χ) =
      sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) ψ - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) χ := by
    intro ψ χ; ext s; simp [hco, mul_sub]
  simp only [theta_one] at hcg
  refine ⟨?_, X.sl g a₀, X.sl g b₀, κ, hκ, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hco, smul_eq_mul]
    exact mul_mem hc (mul_mem (eOm_unit ε A _).2.1 (hφ _))
  · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
  · rw [hexp]; exact prim_sub ε A hpos hPa
  · rw [hexp]; exact prim_sub ε A hpos hPb
  · intro s
    simp only [theta_one]
    rw [hexp, hexp, hqd, hqd]
    have e1 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (φ * X.exp a₀ * X.exp b₀) := by
      rw [(hmul _ _).1, (hmul _ _).1]; ring
    have e2 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀)) *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) *
        (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp b₀))) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀) * X.exp b₀ - X.exp a₀ * qD (X.exp b₀)) := by
      rw [hss, (hmul _ _).1, (hmul _ _).1]; ring
    rw [e1, e2]
    obtain ⟨z, hz, hzeq⟩ := hcg ((ent g 0 0 / ent g 1 1)⁻¹ * s)
    refine ⟨algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) *
      eOm ε ((ent g 0 0 / ent g 1 1)⁻¹ * s * ent g 0 1 / ent g 1 1) * z,
      mul_mem (mul_mem hc (eOm_unit ε A _).2.1) hz, ?_⟩
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul, hco, hco,
      smul_eq_mul, smul_eq_mul, ← mul_sub, ← mul_sub, hzeq]
    ring

end GlobalTheory.DlUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularActionStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  first | exact @GlobalTheory.DlUp.isDl_sl_upper | exact GlobalTheory.DlUp.isDl_sl_upper | (intros; apply GlobalTheory.DlUp.isDl_sl_upper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups Matrix

noncomputable section
namespace GlobalTheory.HeckeTh

theorem toGQ_coe (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0:ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
  unfold toGQ; rw [dite_eq_left h]
  apply Subtype.ext; apply Units.ext
  simp [ofSL, Matrix.SpecialLinearGroup.toGLPos]

theorem ent_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (i j : Fin 2) : ent (toGQ m) i j = (m i j : ℚ) := by
  unfold ent toGQ; rw [dite_eq_left h]; simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_inv (q c : ℕ) (hc : 0 < c) (h : Nat.Coprime q c) : ∃ (a : ℕ) (t : ℤ), (a : ℤ) * q - t * c = 1 := by
  have hg := Nat.gcd_eq_gcd_ab q c
  rw [h] at hg
  set x := Nat.gcdA q c
  set y := Nat.gcdB q c
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨(x % c).toNat, ?_⟩
  have hx : ((x % c).toNat : ℤ) = x % c := Int.toNat_of_nonneg (Int.emod_nonneg _ hc')
  rw [hx]
  have hd : (c : ℤ) ∣ (x % c) * q - 1 := by
    have e : (x % c) * q - 1 = -((c : ℤ) * (x / c) * q) - c * y := by
      rw [Int.emod_def]; push_cast at hg; linarith
    rw [e]; exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_right _ _)
  obtain ⟨t, ht⟩ := hd
  exact ⟨t, by linarith [ht]⟩

theorem isAlgClosure_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    IsAlgClosure ℚ Ω := by
  haveI : CharZero Ω := ε.charZero
  refine ⟨inferInstance, ⟨fun c => ?_⟩⟩
  obtain ⟨D, hD, hk⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hk 0
  have e : (X.exp (algebraMap Ω X.K c)).coeff 0 = c := by
    rw [AlgHom.commutes, HahnSeries.algebraMap_apply']; simp
  rw [e] at hk
  have h1 : IsIntegral ℚ ((D : Ω) ^ k * c) := hk.tower_top
  have hD0 : ((D : Ω) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have e2 : c = (((D:ℚ) ^ k)⁻¹ : ℚ) • ((D : Ω) ^ k * c) := by
    rw [Algebra.smul_def]; simp [hD0]
  rw [e2]; exact (h1.smul _).isAlgebraic

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f g : X.Kˣ) :
    X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp [Tower.cls, ofMul_mul, TensorProduct.tmul_add]

theorem cls_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : X.cls l n 1 = 0 := by
  simp [Tower.cls]

theorem cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) (k : ℕ) :
    X.cls l n (f ^ k) = k • X.cls l n f := by
  induction k with
  | zero => simp [cls_one]
  | succ k ih => rw [pow_succ, cls_mul, ih, succ_nsmul]

theorem cls_lpow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) (s : ℕ) :
    X.cls l n (f ^ (l ^ n * s)) = 0 := by
  rw [cls_pow, ← Nat.cast_smul_eq_nsmul ℤ_[l], Tower.cls, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)

theorem cls_prod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (s : Finset ℕ) (g : ℕ → X.Kˣ) :
    X.cls l n (∏ k ∈ s, g k) = ∑ k ∈ s, X.cls l n (g k) := by
  induction s using Finset.induction_on with
  | empty => simp [cls_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, cls_mul, ih]

theorem isDl_congr {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f : X.K} {φ ψ : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (hψ : ∀ r, ψ.coeff r ∈ A) (hc : ∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) :
    IsDl X A l n s f ψ := by
  obtain ⟨-, a, b, κ, hκ, e, pa, pb, c⟩ := h
  refine ⟨hψ, a, b, κ, hκ, e, pa, pb, ?_⟩
  rw [GlobalTheory.ThAdd.dv_iff] at c ⊢
  have hc' : GlobalTheory.ThAdd.Dv A l n (ψ - φ) := by
    intro r; obtain ⟨z, hz, ez⟩ := hc r
    exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_sub, mul_neg, ← ez]; ring⟩
  have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
      (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
        (ψ - φ) * (X.exp a * X.exp b) := by ring
  rw [key]
  exact c.add (hc'.mul (GlobalTheory.ThAdd.Ig.mul pa.1 pb.1))

theorem isDl_prod {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} (S : Finset ℕ) (g : ℕ → X.K)
    (ψ : ℕ → HahnSeries ℚ Ω) (h : ∀ k ∈ S, IsDl X A l n s (g k) (ψ k)) :
    IsDl X A l n s (∏ k ∈ S, g k) (∑ k ∈ S, ψ k) := by
  induction S using Finset.induction_on with
  | empty => simpa using GlobalTheory.ThAdd.isDl_one X A l n s
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.ThAdd.isDl_mul (h a (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem eOm_zero : eOm ε 0 = 1 := GlobalTheory.CyclotomicQExpansion.Api.eOm_eq_of (by simp)

theorem sub_vq (q : ℕ) (ψ : HahnSeries ℚ Ω) : sub ε (q : ℚ) 0 1 ψ = vq q ψ := by
  unfold sub vq
  rw [div_one]
  congr 1
  ext r; simp [cm, eOm_zero]

theorem sl_pos (g : SL(2, ℤ)) : 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [g.det_coe]; exact one_pos


open StabHecke in
theorem PP_conj {N l : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ} (hm : PP N l m) (δ : SL(2, ℤ)) (hN : (N : ℤ) ∣ δ 1 0)
    (hl : (l : ℤ) ∣ δ 1 0) : PP N l (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  have hd : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by have := δ.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 : (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) 0 0 =
      m 0 0 + (δ 1 0 * (m 0 0 * δ 0 1 + δ 1 1 * m 0 1 - δ 0 1 * m 1 1) - m 1 0 * (δ 0 1 * δ 0 0)) := by
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    linear_combination (m 0 0) * hd
  have e10 : (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) 1 0 =
      δ 1 0 * (-(m 0 0 * δ 0 0) - δ 1 0 * m 0 1 + δ 0 0 * m 1 1) + m 1 0 * (δ 0 0 * δ 0 0) := by
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, add_sub_right_comm]
    exact dvd_add h1 (dvd_sub (dvd_mul_of_dvd_left hN _) (dvd_mul_of_dvd_left h2 _))
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left hN _) (dvd_mul_of_dvd_left h2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left hl _) (dvd_mul_of_dvd_left h3 _)
  · rw [e00]
    obtain ⟨t, ht⟩ := dvd_sub (dvd_mul_of_dvd_left hl (m 0 0 * δ 0 1 + δ 1 1 * m 0 1 - δ 0 1 * m 1 1))
      (dvd_mul_of_dvd_left h3 (δ 0 1 * δ 0 0))
    rw [ht]; exact h4.add_mul_left_left t


open StabHecke in
theorem mem_coset {N l q : ℕ} (hq : q.Prime) {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hm : m.det = q) (hPm : PP N l m) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ m = (g : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o' := by
  rcases coset q hq _ hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · set g' := g * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hg'
    have hs : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have he : g' * repT q σ none = m := by
      rw [hg', ← hg]
      show g * _ * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul]
    have hd : g'.det = 1 := det_eq_one_of_mul hq.pos g' _ _ he (det_repT q σ none) hm
    exact ⟨none, ⟨g', hd⟩, mem_Gam_of_PP N l ⟨g', hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql none) hPm, he.symm⟩
  · have he : g * repT q σ (some ⟨k, hk⟩) = m := by simpa [repT] using hg
    have hd : g.det = 1 := det_eq_one_of_mul hq.pos g _ _ he (det_repT q σ _) hm
    exact ⟨some ⟨k, hk⟩, ⟨g, hd⟩, mem_Gam_of_PP N l ⟨g, hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql _) hPm, he.symm⟩


open StabHecke in
theorem perm_rep {N l q : ℕ} (hq : q.Prime) {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (δ : SL(2, ℤ)) (hN : (N : ℤ) ∣ δ 1 0) (hl : (l : ℤ) ∣ δ 1 0) :
    ∃ π : Option (Fin q) ≃ Option (Fin q), ∀ o, ∃ g ∈ Gam N l,
      repT q σ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = ((δ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ (π o) := by
  have hc : ∀ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := fun g => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∀ o, ∃ o', ∃ g ∈ Gam N l,
      repT q σ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = ((δ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o' := by
    intro o
    obtain ⟨o', g, hg, e⟩ := mem_coset hq hσ hql _ (by
      rw [Matrix.det_mul, Matrix.det_mul, det_repT, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]) (PP_conj (congruenceCondition_heckeRepresentative hσ hql o) δ hN hl)
    refine ⟨o', g, hg, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hc,
      Matrix.one_mul]
  choose f g hg he using key
  have hinj : Function.Injective f := by
    intro o p h
    apply coset_representatives_hecke_disjoint hq σ o p ((δ * g p) * (δ * g o)⁻¹)
    have h1 : repT q σ o = repT q σ o * δ * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_one]
    have h2 : repT q σ p = repT q σ p * δ * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_one]
    rw [h1, h2, he o, he p, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun o => ⟨g o, hg o, he o⟩⟩

theorem isDiam_one_of_mem {N l : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gam N l) : IsDiam N l 1 g := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  refine ⟨Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N h1, h2⟩, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  simpa [en] using h1.2.1


open StabHecke in
theorem coset_decomp (X : Tower Ω ε) (N l : ℕ) [hl : Fact l.Prime] (w d q : ℕ) (hq : q.Prime) (hqNl : ¬ q ∣ N * l)
    (hd : d.Coprime N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b) =
      ∑ k ∈ Finset.range q, X.act l !![1, (k : ℤ); 0, (q : ℤ)] (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) +
        X.act l !![(q : ℤ), 0; 0, 1] (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_left h l)
  have hql : q.Coprime l := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_right h N)
  have hσ := isDiam_sgD_of_coprime (l := l) hl.out.ne_zero hqN
  have hδ := isDiam_sgD_of_coprime (l := l) hl.out.ne_zero hd
  obtain ⟨π, hπ⟩ := perm_rep hq hσ (Nat.isCoprime_iff_coprime.2 hql) _ (diam_facts hδ).1 (diam_facts hδ).2.1
  have hr : ∀ o, 0 < (repT q (sgD N l q) o).det := fun o => by rw [det_repT]; exact_mod_cast hq.pos
  have step : ∀ o, X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (repT q (sgD N l q) o) b) =
      X.act l (repT q (sgD N l q) (π o)) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
    intro o
    obtain ⟨g, hg, e⟩ := hπ o
    have h1 := isDiam_mul hδ (isDiam_one_of_mem hg)
    rw [one_mul] at h1
    rw [act_act X l _ _ (sl_pos _) (hr o), e, ← act_act X l _ _ (hr _) (sl_pos _), X.act_isDiam_eq hb h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heckeT_eq, map_sum, Finset.sum_congr rfl fun o _ => step o,
    Equiv.sum_comp π fun o => X.act l (repT q (sgD N l q) o) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b),
    Fintype.sum_option, add_comm, Finset.sum_range]
  congr 1
  have h1 := isDiam_mul hδ hσ
  rw [mul_comm q d] at h1
  have hD : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, hq.pos]
  rw [← X.act_isDiam_eq hb h1, Matrix.SpecialLinearGroup.coe_mul, ← act_act X l _ _ (sl_pos _) (sl_pos _),
    act_act X l _ _ hD (sl_pos _)]
  rfl

theorem conj_mem_Gamma1 {M : ℕ} {τ γ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 M)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 M) : τ * γ * τ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by
  have hτ' := CongruenceSubgroup.Gamma0_mem.1 hτ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨g1, g2, g3⟩ := hγ
  have dt := τ.det_coe
  rw [Matrix.det_fin_two] at dt
  have dt' : ((τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 : ℤ) : ZMod M) = 1 := by rw [dt]; simp
  push_cast at dt'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [hτ'] at dt'
  rw [hτ', g1, g2, g3]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination dt'
  · linear_combination dt'
  · ring

theorem sl_sl_conj (X : Tower Ω ε) (τ γ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL γ) (X.sl (ofSL τ) f) = X.sl (ofSL τ) (X.sl (ofSL (τ * γ * τ⁻¹)) f) := by
  rw [← X.sl_mul, ← X.sl_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem inv_sl (X : Tower Ω ε) {M : ℕ} {τ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 M) {f : X.K}
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.sl (ofSL τ) f) := by
  intro γ hγ
  rw [sl_sl_conj, hf _ (conj_mem_Gamma1 hτ hγ)]

def hn (X : Tower Ω ε) (q : ℕ) (τ : SL(2, ℤ)) : X.K →* X.K where
  toFun u := ∏ o : Option (Fin q), X.sl (toGQ (StabHecke.repT q τ o)) u
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

open StabHecke in
theorem hn_comm (X : Tower Ω ε) {M q : ℕ} {τ : SL(2, ℤ)} (hq : q.Prime) (hτ : IsDiam M 1 q τ) {u : X.K}
    (hu : Inv X (CongruenceSubgroup.Gamma1 M) u) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    X.sl (ofSL δ) (hn X q τ u) = hn X q τ (X.sl (ofSL δ) u) := by
  obtain ⟨π, hπ⟩ := perm_rep hq hτ (by simpa using isCoprime_one_right) δ
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hδ)) (by simp)
  have hr : ∀ o, 0 < (repT q τ o).det := fun o => by rw [det_repT]; exact_mod_cast hq.pos
  have step : ∀ o, X.sl (ofSL δ) (X.sl (toGQ (repT q τ o)) u) = X.sl (toGQ (repT q τ (π o))) (X.sl (ofSL δ) u) := by
    intro o
    obtain ⟨g, hg, e⟩ := hπ o
    rw [← X.sl_mul, ← toGQ_coe δ, ← toGQ_mul_of_pos _ _ (hr o) (sl_pos _), e, toGQ_mul_of_pos _ _ (sl_pos _) (hr _),
      X.sl_mul, toGQ_coe, toGQ_coe, map_mul, X.sl_mul, inv_sl X hδ hu g (Subgroup.mem_inf.1 hg).1]
  simp only [hn, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [map_prod, Finset.prod_congr rfl fun o _ => step o,
    Equiv.prod_comp π fun o => X.sl (toGQ (repT q τ o)) (X.sl (ofSL δ) u)]

theorem hn_inv (X : Tower Ω ε) {M q : ℕ} {τ : SL(2, ℤ)} (hq : q.Prime) (hτ : IsDiam M 1 q τ) {u : X.K}
    (hu : Inv X (CongruenceSubgroup.Gamma1 M) u) : Inv X (CongruenceSubgroup.Gamma1 M) (hn X q τ u) := by
  intro γ hγ
  rw [hn_comm X hq hτ hu (CongruenceSubgroup.Gamma1_in_Gamma0 M hγ), hu γ hγ]

theorem hn_eq (X : Tower Ω ε) {q : ℕ} (hq : 0 < q) (τ : SL(2, ℤ)) (u : X.K) :
    hn X q τ u = (∏ k ∈ Finset.range q, X.sl (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) u) *
      X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.sl (ofSL τ) u) := by
  have hD : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, hq]
  simp only [hn, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_option, mul_comm, Finset.prod_range, ← X.sl_mul, ← toGQ_coe, ← toGQ_mul_of_pos _ _ (sl_pos _) hD]
  rfl

theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) (z : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n z = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ z) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at h ⊢
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_val_apply, h, Tower.cls, LinearMap.reduceModIdeal_apply]
  rfl

theorem eval_homog (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w n : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ_[l]) (hy : (l : ℤ_[l]) ^ n ∣ y) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m b ![x, y]) =
      x ^ w • AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m b ![1, 0]) := by
  have h1 : b ∈ PolAct.homF (⊤ : Submodule ℤ_[l] (X.Khat l)) w := by
    refine (Submodule.span_le.2 ?_ : X.B N l w ≤ _) hb
    rintro x ⟨⟨c, -, hc⟩, -⟩
    exact ⟨c, fun _ => trivial, hc⟩
  obtain ⟨c, -, hc⟩ := PolAct.subst_mem (A := ⊤) (X.kmap l (X.sl (toGQ m)).toRingEquiv) (fun _ _ => trivial) (mZl l m) h1
  have hc' : ∀ u, X.act l m b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i := hc
  obtain ⟨t, rfl⟩ := hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc', hc', map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul, smul_smul]
  rcases Nat.eq_zero_or_pos (w - (i : ℕ)) with h | h
  · have : (i : ℕ) = w := by have := i.2; omega
    rw [h, this]; simp
  · obtain ⟨k, hk⟩ : ∃ k, w - (i : ℕ) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [hk, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_smul]
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
    rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [pow_succ']
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)))

theorem mem_Gamma0_of {N l n : ℕ} (hc : Nat.Coprime N l) {δ : SL(2, ℤ)} (h1 : δ ∈ CongruenceSubgroup.Gamma1 N)
    (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) : δ ∈ CongruenceSubgroup.Gamma0 (N * l ^ n) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  rw [CongruenceSubgroup.Gamma0_mem]
  obtain ⟨-, -, h10⟩ := h1
  obtain ⟨-, -, h20, -⟩ := h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h20
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h20
  push_cast at h20 ⊢
  exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right n hc)) h10 (by exact_mod_cast h20)

def Dlt (X : Tower Ω ε) (N l n : ℕ) (f : X.K) : Prop :=
  ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
    ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n)

theorem dlt_sl (X : Tower Ω ε) {N l n : ℕ} {τ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 (N * l ^ n))
    (hτN : τ ∈ CongruenceSubgroup.Gamma0 N) {f : X.K} (hf : Dlt X N l n f) : Dlt X N l n (X.sl (ofSL τ) f) := by
  intro δ h1 h2
  obtain ⟨g, hg, e⟩ := hf (τ * δ * τ⁻¹) (conj_mem_Gamma1 hτN h1) (by
    have := (CongruenceSubgroup.Gamma_normal (l ^ n)).conj_mem _ h2 τ
    rwa [mul_neg, neg_mul] at this)
  exact ⟨_, inv_sl X hτ hg, by rw [sl_sl_conj, ← map_mul, e, map_pow]⟩

theorem dlt_hn (X : Tower Ω ε) {N l n q : ℕ} (hc : Nat.Coprime N l) {τ : SL(2, ℤ)} (hq : q.Prime)
    (hτ : IsDiam (N * l ^ n) 1 q τ) {f : X.K} (hI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hf : Dlt X N l n f) : Dlt X N l n (hn X q τ f) := by
  intro δ h1 h2
  obtain ⟨g, hg, e⟩ := hf δ h1 h2
  exact ⟨_, hn_inv X hq hτ hg, by rw [hn_comm X hq hτ hI (mem_Gamma0_of hc h1 h2), ← map_mul, e, map_pow]⟩

def su (X : Tower Ω ε) (m : Matrix (Fin 2) (Fin 2) ℤ) : X.Kˣ →* X.Kˣ :=
  Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom

theorem coe_su (X : Tower Ω ε) (m : Matrix (Fin 2) (Fin 2) ℤ) (f : X.Kˣ) :
    ((su X m f : X.Kˣ) : X.K) = X.sl (toGQ m) f := rfl

theorem eval_act (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w n : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w)
    (s m : Matrix (Fin 2) (Fin 2) ℤ) (a : ℕ) (ha : m 0 0 = a) (hm : (l : ℤ) ^ n ∣ m 1 0) (f : X.Kˣ)
    (hf : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l s b ![1, 0]) = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m (X.act l s b) ![1, 0]) = X.cls l n (su X m f ^ a ^ w) := by
  have e : mZl l m *ᵥ ![1, 0] = ![(a : ℤ_[l]), ((m 1 0 : ℤ) : ℤ_[l])] := by
    ext i; fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]
  have h1 : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l s b (mZl l m *ᵥ ![1, 0])) = X.cls l n (f ^ a ^ w) := by
    rw [e, eval_homog X N l w n b hb s _ _ (by exact_mod_cast (Int.castRingHom ℤ_[l]).map_dvd hm), hf, cls_pow,
      ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  rw [← map_pow]
  exact eval_kmap X l n _ _ _ h1

theorem dl_cong [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) {N l n : ℕ} [hl : Fact l.Prime]
    (hlA : (l : Ω) ∈ A.nonunits) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (y f : X.Kˣ) (k : ℕ)
    (hyI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (y : X.K))
    (hfI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K)) (hy : Dlt X N l n (y : X.K))
    (hf : Dlt X N l n (f : X.K)) (u : X.Kˣ) (hu : (f : X.K) = (y : X.K) ^ k * (u : X.K) ^ l ^ n)
    {ψ φ : HahnSeries ℚ Ω} (hψ : IsDl X A l n 1 (y : X.K) ψ) (hφ : IsDl X A l n 1 (f : X.K) φ) (r : ℚ) :
    CgA A l n (((k : Ω) • ψ).coeff r) (φ.coeff r) := by
  have hN : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; exact hlN (dvd_zero l))
  haveI : IsAlgClosure ℚ Ω := isAlgClosure_of_tower X
  have hy0 : (y : X.K) ^ k ≠ 0 := pow_ne_zero _ y.ne_zero
  have hL : (u : X.K) ^ l ^ n = f / (y : X.K) ^ k := by rw [hu]; field_simp
  have hT := GlobalTheory.T.modularTower_rootOfInvariant_T_invariant X N l n hl.out hl2 hlN hN (u : X.K) u.ne_zero (by
      intro γ hγ; rw [hL, map_div₀, map_pow, hyI γ hγ, hfI γ hγ]) (by
      intro δ h1 h2
      obtain ⟨g, hgI, hg⟩ := hy δ h1 h2
      obtain ⟨g', hg'I, hg'⟩ := hf δ h1 h2
      refine ⟨g' / g ^ k, fun γ hγ => by rw [map_div₀, map_pow, hgI γ hγ, hg'I γ hγ], ?_⟩
      rw [mul_pow, ← map_pow, hL, map_div₀, div_mul_div_comm, hg', map_pow, ← mul_pow, hg, div_pow, ← pow_mul,
        ← pow_mul, mul_comm k])
  exact GlobalTheory.T.logDerivQExpansion_mul_primePow_congr X A l hlA n _ _ hy0 u.ne_zero hT _ _ (GlobalTheory.ThAdd.isDl_pow hψ k) (hu ▸ hφ) r

theorem isDl_hq [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) {q : ℕ}
    (hq0 : 0 < q) (hqA : (q : Ω)⁻¹ ∈ A) {f : X.K} {φ : HahnSeries ℚ Ω} (h : IsDl X A l n 1 f φ) :
    IsDl X A l n 1 (∏ k ∈ Finset.range q, X.sl (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) f) (hq ε q φ) := by
  rw [hq, Finset.smul_sum]
  refine isDl_prod _ _ _ fun k _ => ?_
  have hd : (0 : ℤ) < (!![1, (k : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by simp [Matrix.det_fin_two, hq0]
  have := GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action Ω ε X A 0 l n (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) (by simp [ent_toGQ _ hd])
    (by simp [ent_toGQ _ hd]) (by simp [ent_toGQ _ hd, hq0]) (by simpa [ent_toGQ _ hd] using hqA) f φ h
  rw [HahnSeries.C_mul_eq_smul] at this
  simpa [ent_toGQ _ hd] using this

theorem isDl_vq [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) {q : ℕ}
    (hq0 : 0 < q) {f : X.K} {φ : HahnSeries ℚ Ω} (h : IsDl X A l n 1 f φ) :
    IsDl X A l n 1 (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) ((q : Ω) • vq q φ) := by
  have hd : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simp [Matrix.det_fin_two, hq0]
  have := GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action Ω ε X A 0 l n (toGQ !![(q : ℤ), 0; 0, 1]) (by simp [ent_toGQ _ hd])
    (by simp [ent_toGQ _ hd, hq0]) (by simp [ent_toGQ _ hd]) (by simp [ent_toGQ _ hd]) f φ h
  rw [HahnSeries.C_mul_eq_smul] at this
  rw [← sub_vq (ε := ε)]
  simpa [ent_toGQ _ hd] using this

theorem isThB_heckeT : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d q : ℕ), q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A →
    (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
      (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  intro Ω _ _ _ ε X A N l hlF n w d q hqP hqNl hqA hlA hl2 hlN hd b hb φ φ' _ _ h₀ h'
  obtain ⟨f₀, hf₀I, hf₀c, hf₀δ, hf₀D⟩ := h₀
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h'
  haveI : IsAlgClosure ℚ Ω := isAlgClosure_of_tower X
  have hl : l.Prime := hlF.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hlN (dvd_zero l))
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have hq0 : 0 < q := hqP.pos
  have hqc : Nat.Coprime q (N * l ^ (n + 1)) := (Nat.Prime.coprime_iff_not_dvd hqP).2 fun h =>
    ((Nat.Prime.dvd_mul hqP).1 h).elim (fun h => hqNl (dvd_mul_of_dvd_left h l))
      fun h => hqNl (dvd_mul_of_dvd_right (hqP.dvd_of_dvd_pow h) N)
  obtain ⟨a, t, hat⟩ := exists_inv q _ (Nat.mul_pos hN0 (pow_pos hl.pos (n + 1))) hqc
  push_cast at hat
  obtain ⟨τ, h00, h10, h11⟩ : ∃ τ : SL(2, ℤ), τ 0 0 = a ∧ τ 1 0 = N * l ^ (n + 1) ∧ τ 1 1 = q :=
    ⟨⟨!![(a : ℤ), t; N * l ^ (n + 1), (q : ℤ)], by rw [Matrix.det_fin_two_of]; exact hat⟩, rfl, rfl, rfl⟩
  have hG : ∀ M : ℕ, (M : ℤ) ∣ N * l ^ (n + 1) → τ ∈ CongruenceSubgroup.Gamma0 M := fun M h => by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, h10]; exact h
  have hGM := hG (N * l ^ n) ⟨l, by push_cast; ring⟩
  have hGN := hG N (dvd_mul_right _ _)
  have hτM : IsDiam (N * l ^ n) 1 q τ := ⟨Subgroup.mem_inf.2 ⟨hGM, hG 1 (by simp)⟩, by simp [en, h11]⟩
  have hτN : IsDiam N l q τ := ⟨Subgroup.mem_inf.2 ⟨hGN, hG l ⟨N * l ^ n, by ring⟩⟩, by simp [en, h11]⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, a ^ w * q ^ w = 1 + l ^ n * s := by
    have h1 : 1 ≡ a * q [MOD l ^ n] := Nat.modEq_iff_dvd.2 ⟨t * N * l, by push_cast; linear_combination hat⟩
    have h2 := h1.pow w
    have h3 : 0 < a * q := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exfalso
        have : (l : ℤ) ∣ 1 := ⟨-(t * N * l ^ n), by push_cast at hat; linear_combination -hat⟩
        exact hl.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast this))
      · exact Nat.mul_pos h hq0
    rw [one_pow] at h2
    obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ h3)).1 h2
    exact ⟨s, by rw [← hs, ← mul_pow]; have := Nat.one_le_pow w _ h3; omega⟩

  have hy : ((su X τ f₀ : X.Kˣ) : X.K) = X.sl (ofSL τ) f₀ := by rw [coe_su, toGQ_coe]
  have hyI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((su X τ f₀ : X.Kˣ) : X.K) := hy ▸ inv_sl X hGM hf₀I
  have hyδ : Dlt X N l n ((su X τ f₀ : X.Kˣ) : X.K) := hy ▸ dlt_sl X hGM hGN hf₀δ
  have hcl : X.cls l n (su X τ f₀ ^ a ^ w) = X.cls l n f' := by
    have h1 := isDiam_mul (isDiam_sgD_of_coprime (l := l) hl.ne_zero hd) hτN
    rw [mul_comm q d] at h1
    rw [← hf'c, ← X.act_isDiam_eq hb h1, Matrix.SpecialLinearGroup.coe_mul,
      ← StabHecke.act_act X l _ _ (sl_pos _) (sl_pos _),
      eval_act X N l w n b hb _ _ a h00 (by rw [h10]; exact ⟨N * l, by ring⟩) f₀ hf₀c]
  obtain ⟨u, hu⟩ := GlobalTheory.T.modularTower_class_eq_imp_pow_ratio X l n _ _ hcl
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l A hlA n 1
    ((su X τ f₀ : X.Kˣ) : X.K) one_pos (Units.ne_zero _) (by
      show X.sl (ofSL (ModularGroup.T ^ 1)) _ = _
      rw [pow_one]
      exact hyI _ (by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T]))
  rw [Nat.cast_one] at hψ
  have hcg := dl_cong X A hlA hl2 hlN (su X τ f₀) f' (a ^ w) hyI hf'I hyδ hf'δ u
    (by rw [hu, Units.val_pow_eq_pow_val]) hψ hf'D

  have hF : (((∏ k ∈ Finset.range q, su X !![1, (k : ℤ); 0, (q : ℤ)] f₀) *
      su X !![(q : ℤ), 0; 0, 1] (su X τ f₀) : X.Kˣ) : X.K) = hn X q τ f₀ := by
    rw [hn_eq X hq0, Units.val_mul, Units.coe_prod, coe_su, hy]; rfl
  refine ⟨(∏ k ∈ Finset.range q, su X !![1, (k : ℤ); 0, (q : ℤ)] f₀) * su X !![(q : ℤ), 0; 0, 1] (su X τ f₀),
    ?_, ?_, ?_, ?_⟩
  · rw [hF]; exact hn_inv X hqP hτM hf₀I
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coset_decomp X N l w d q hqP hqNl hd b hb, Pi.add_apply, Finset.sum_apply, map_add (f := _), map_sum, cls_mul, cls_prod,
      eval_act X N l w n b hb _ _ q rfl (by simp) f' hf'c]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [eval_act X N l w n b hb _ _ 1 rfl (by simp) f₀ hf₀c, one_pow, pow_one]
      · have e : f' = su X τ f₀ ^ a ^ w * u ^ l ^ n := Units.ext (by rw [hu]; simp)
        rw [e, map_mul, map_pow, map_pow, mul_pow, ← pow_mul, ← pow_mul, hs, pow_add, pow_one, cls_mul, cls_mul,
          cls_lpow, cls_lpow, add_zero, add_zero]
  · rw [hF]; exact dlt_hn X hNl hqP hτM hf₀I hf₀δ
  · rw [hF, hn_eq X hq0, ← hy]
    have h1 := isDl_hq X A l n hq0 hqA hf₀D
    have hqm : (q : Ω) ∈ A := natCast_mem A q
    refine isDl_congr (GlobalTheory.ThAdd.isDl_mul h1 (isDl_vq X A l n hq0 hψ)) (fun r => ?_) fun r => ?_
    · rw [HahnSeries.coeff_add, HahnSeries.coeff_smul, Api.coeff_vq hq0, smul_eq_mul]
      exact add_mem (h1.1 r) (mul_mem (pow_mem hqm _) (hf'D.1 _))
    · obtain ⟨z, hz, ez⟩ := hcg (r / q)
      have hs' : (a : Ω) ^ w * (q : Ω) ^ w = 1 + (l : Ω) ^ n * s := by exact_mod_cast congrArg (Nat.cast : ℕ → Ω) hs
      refine ⟨(q : Ω) ^ (w + 1) * z - q * s * ψ.coeff (r / q),
        sub_mem (mul_mem (pow_mem hqm _) hz) (mul_mem (mul_mem hqm (natCast_mem A s)) (hψ.1 _)), ?_⟩
      rw [HahnSeries.coeff_smul, smul_eq_mul, Nat.cast_pow] at ez
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Api.coeff_vq hq0, smul_eq_mul]
      linear_combination (q : Ω) ^ (w + 1) * ez - (q : Ω) * ψ.coeff (r / q) * hs'

end GlobalTheory.HeckeTh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwistStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → 1 ≤ N → ∀ (n w d q : ℕ), Odd w → q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  first | exact @GlobalTheory.HeckeTh.isThB_heckeT | exact GlobalTheory.HeckeTh.isThB_heckeT | (intros; apply GlobalTheory.HeckeTh.isThB_heckeT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamond
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.ThNHecke

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem inv_natCast_mem (A : ValuationSubring Ω) {l q : ℕ} (hq : q.Prime) (hl : l.Prime) (hql : q ≠ l)
    (hlA : (l : Ω) ∈ A.nonunits) : ((q : Ω))⁻¹ ∈ A := by
  have hcop : Nat.Coprime q l := (Nat.coprime_primes hq hl).mpr hql
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A v)
  have hqle : A.valuation (q : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A q)
  have hl1 : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).mp hlA
  have hq1 : A.valuation (q : Ω) = 1 := by
    refine le_antisymm hqle (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Ω) * (q : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have h2 : A.valuation ((v : Ω) * (l : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, map_one] at h3
    exact lt_irrefl _ h3
  rw [← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]

theorem op_mem_B [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (N l w : ℕ) [Fact l.Prime]
    (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.op N l T b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := hj
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X ε.injective ⟨φ, h2, h1⟩ l).1
  have hNl : Nat.Coprime N l :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

theorem isThB_cong [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [hl : Fact l.Prime]
    (l2 : l ≠ 2) (hN : ¬ l ∣ N) (hN1 : 1 ≤ N) (hlA : (l : Ω) ∈ A.nonunits) (n : ℕ) (b : X.Fn l)
    (φ φ' : HahnSeries ℚ Ω) (h1 : IsThB X A N l n b φ) (h2 : IsThB X A N l n b φ') :
    ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ hδ'
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, hgI γ hγ, hg'I γ hγ]
      · rw [div_pow, ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring)
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)

end GlobalTheory.ThNHecke


open GlobalTheory.ThNHecke in
theorem GlobalTheory.CyclotomicQExpansion.thN_hecke : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : l.Prime := Fact.out
  have stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w :=
    fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc
  have dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w :=
    fun e he c hc => stab (Letter.D e) he c hc
  have exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c) :=
    fun m e he c hc => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc
  have ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) :=
    fun m e he c hc => (exL m e he c hc).1
  have uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
      IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r) :=
    fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'
  refine ⟨?_, ?_, ?_⟩
  · intro q hqP hqd r
    have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql : q ≠ l := by
      rintro rfl; exact hqd (dvd_mul_left q N)
    have hqinv := inv_natCast_mem A hqP hl hql hlA
    have hTb : X.heckeT N l q b ∈ X.B N l w := stab (Letter.T q) ⟨hqP, hqd⟩ b hb
    have e1 := exL n d hd b hb
    have e2 := exL n (d * q) (Nat.Coprime.mul_left hd hqN) b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
        (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)) :=
      GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1
    exact uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r
  · intro r
    have hUb : X.heckeU l b ∈ X.B N l w := stab Letter.U trivial b hb
    have e1 := exL (n + 1) d hd b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b))
        (uq l (thN X A N l (n + 1) d b)) :=
      GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1
    exact uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r
  · intro a ha r
    have hDb : X.diam N l a b ∈ X.B N l w := stab (Letter.D a) ha b hb
    have h1 := (GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)
    exact uniq n _ (dB (d * a) (Nat.Coprime.mul_left hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul_left hd ha) b hb) r
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamondStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_hecke | exact GlobalTheory.CyclotomicQExpansion.thN_hecke | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_hecke <;> assumption)
end
