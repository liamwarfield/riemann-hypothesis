module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_dvdPow {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hx : ∀ k, DvdPow ϖ (k + 1) x) : x = 0 := by
  by_contra h0
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have key : ∀ N : ℕ, Valued.v x ≤ WithZero.exp (-(N : ℤ)) := by
    intro N
    obtain ⟨b, hb, hxb⟩ := hx N
    rw [hxb, map_mul, map_pow, hϖ]
    calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
          mul_le_mul' le_rfl hb
      _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
          rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by push_cast; omega)
  obtain ⟨m, hm⟩ : ∃ m, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h1 := key ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  have := Int.self_le_toNat (-m)
  push_cast at h1
  omega

end GlobalTheory.Hk3.IntWittBase

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_map {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {m : ℕ} {a : L}
    (h : DvdPow ϖ m a) : DvdPow ϖ m (σ a) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨σ b, ?_, by rw [map_mul, map_pow, hσϖ]⟩
  show Valued.v (σ b) ≤ 1
  rw [hσv]; exact hb

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_apply (σ : L →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ A i j = σ (A j i) := rfl

theorem int_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L) (hB : ∀ i j, B i j ∈ intL L) :
    ∀ i j, (A * B) i j ∈ intL L := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem int_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := by
  intro i j; rw [cT_apply]; show Valued.v (σ _) ≤ 1; rw [hσv]; exact hA j i

theorem mc_mul_left {ϖ : L} {n m : ℕ} {A D : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m ((A * D) i j) := by
  intro i j; rw [Matrix.mul_apply]; exact dvdPow_sum _ _ fun l _ => dvdPow_mul_int (hD l j) (hA i l)

theorem mc_mul_right {ϖ : L} {n m : ℕ} {D B : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j))
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, DvdPow ϖ m ((D * B) i j) := by
  intro i j; rw [Matrix.mul_apply]
  exact dvdPow_sum _ _ fun l _ => by rw [mul_comm]; exact dvdPow_mul_int (hD i l) (hB l j)

theorem mc_cT {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {n m : ℕ}
    {D : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m (cT σ D i j) := by
  intro i j; rw [cT_apply]; exact dvdPow_map hσv hσϖ (hD j i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_sub (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT_apply]

end GlobalTheory.Hk3.IntWittBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchy
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchy
open Matrix Filter Topology

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem val_lt_exp_of_dvdPow_succ {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {N : ℕ} (hx : DvdPow ϖ (N + 1) x) : Valued.v x < WithZero.exp (-(N : ℤ)) := by
  obtain ⟨b, hb, hxb⟩ := hx
  rw [hxb, map_mul, map_pow, hϖ]
  calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
        mul_le_mul' le_rfl hb
    _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
    _ < WithZero.exp (-(N : ℤ)) := WithZero.exp_lt_exp.2 (by push_cast; omega)

theorem isClosed_dvdPow_sub {ϖ : L} (h0 : ϖ ≠ 0) (m : ℕ) (c : L) : IsClosed {x : L | DvdPow ϖ m (x - c)} := by
  have hp : ϖ ^ m ≠ 0 := pow_ne_zero _ h0
  have he : {x : L | DvdPow ϖ m (x - c)} =
      (fun x => (ϖ ^ m)⁻¹ * (x - c)) ⁻¹' ((Valued.v (R := L)).integer : Set L) := by
    ext x
    constructor
    · rintro ⟨b, hb, hxb⟩
      show Valued.v ((ϖ ^ m)⁻¹ * (x - c)) ≤ 1
      rw [hxb, inv_mul_cancel_left₀ hp]; exact hb
    · intro hx
      exact ⟨(ϖ ^ m)⁻¹ * (x - c), hx, by rw [mul_inv_cancel_left₀ hp]⟩
  rw [he]
  exact (Valued.isClosed_integer L).preimage (by fun_prop)

theorem exists_limit_dvdPow (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (a : ℕ → L) (ha : ∀ k, DvdPow ϖ (k + 1) (a (k + 1) - a k)) :
    ∃ b : L, ∀ k, DvdPow ϖ (k + 1) (b - a k) := by
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hint : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ]
    show WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.2 (by omega)
  have hstep : ∀ k m, k ≤ m → DvdPow ϖ (k + 1) (a m - a k) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rw [sub_self]; exact dvdPow_zero ϖ _
    | succ m hkm ih =>
      have := dvdPow_add (dvdPow_mono hint (Nat.succ_le_succ hkm) (ha m)) ih
      rwa [sub_add_sub_cancel] at this
  have hc : CauchySeq a := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by
      simp
    obtain ⟨e, he⟩ : ∃ e, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e :=
      ⟨_, (WithZero.exp_log hγ).symm⟩
    refine ⟨(-e).toNat, fun m hm n hn => ?_⟩
    show Valued.v.restrict (a n - a m) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    have h1 := dvdPow_sub (hstep _ n hn) (hstep _ m hm)
    rw [sub_sub_sub_cancel_right] at h1
    refine (val_lt_exp_of_dvdPow_succ hϖ h1).trans_le (WithZero.exp_le_exp.2 ?_)
    have := Int.self_le_toNat (-e)
    omega
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨b, fun k => ?_⟩
  exact (isClosed_dvdPow_sub h0 (k + 1) (a k)).mem_of_tendsto hb
    (eventually_atTop.2 ⟨k, fun m hm => hstep k m hm⟩)

end GlobalTheory.Hk3.IntWittBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchyStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | exact GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | (intros; apply GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStep
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStepStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_newton_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  first | exact @GlobalTheory.Hk3.UnitaryNewton.newton_step | exact GlobalTheory.Hk3.UnitaryNewton.newton_step | (intros; apply GlobalTheory.Hk3.UnitaryNewton.newton_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairing
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev OV (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring

abbrev Res (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : Type :=
  IsLocalRing.ResidueField (OV L)

theorem isUnit_iff (x : OV L) : IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : OV L) : L) ≤ 1 := (u : OV L).2
    have h2 : Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) ≤ 1 := ((u⁻¹ : (OV L)ˣ) : OV L).2
    have h3 : ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [show ((u : OV L) : L) * (((u⁻¹ : (OV L)ˣ) : OV L) : L) = (((u : OV L) * ((u⁻¹ : (OV L)ˣ) : OV L) : OV L) : L) from rfl, Units.mul_inv]; rfl
    have h4 : Valued.v ((u : OV L) : L) * Valued.v (((u⁻¹ : (OV L)ˣ) : OV L) : L) = 1 := by
      rw [← map_mul, h3, map_one]
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
      _ ≤ Valued.v ((u : OV L) : L) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _
  · intro h
    have hx : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hm : (x : L)⁻¹ ∈ OV L := by
      show Valued.v (x : L)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one (b := (⟨_, hm⟩ : OV L)) (Subtype.ext (mul_inv_cancel₀ hx))

theorem lt_one_iff_le {a : WithZero (Multiplicative ℤ)} :
    a < 1 ↔ a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, a = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
    show WithZero.exp m < WithZero.exp 0 ↔ WithZero.exp m ≤ WithZero.exp (-1)
    rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem residue_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : OV L) : IsLocalRing.residue (OV L) x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  have hϖ0 : ϖ ≠ 0 := by intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hx1 : Valued.v (x : L) ≤ 1 := x.2
  constructor
  · intro h
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx1 h
    rw [lt_one_iff_le, ← hϖ] at hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hlt zero_le'
  · rintro ⟨b, hb, hxb⟩ h
    have hb' : Valued.v b ≤ 1 := hb
    have : Valued.v (x : L) ≤ Valued.v ϖ := by
      rw [hxb, map_mul, pow_one]
      calc Valued.v ϖ * Valued.v b ≤ Valued.v ϖ * 1 := mul_le_mul' le_rfl hb'
        _ = _ := mul_one _
    rw [h, hϖ] at this
    exact absurd (lt_one_iff_le.2 le_rfl) (not_lt.2 this)

def sigO (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : OV L →+* OV L :=
  (σ.comp (OV L).subtype).codRestrict (OV L) fun x => by
    show Valued.v (σ (x : L)) ≤ 1
    rw [hσv]; exact x.2

theorem sigO_coe (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    ((sigO σ hσv x : OV L) : L) = σ x := rfl

theorem sigO_le (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsLocalRing.maximalIdeal (OV L) ≤ Ideal.comap (sigO σ hσv) (IsLocalRing.maximalIdeal (OV L)) := by
  intro x hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff, sigO_coe, hσv,
    ← isUnit_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  exact hx

def sigK (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) : Res L →+* Res L :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (OV L)) (sigO σ hσv) (sigO_le σ hσv)

theorem sigK_residue (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : OV L) :
    sigK σ hσv (IsLocalRing.residue (OV L) x) = IsLocalRing.residue (OV L) (sigO σ hσv x) := rfl

end GlobalTheory.Hk3.ResWitt

end

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]


open Classical in
noncomputable def redL (x : L) : Res L := if h : x ∈ OV L then IsLocalRing.residue (OV L) ⟨x, h⟩ else 0

theorem redL_coe (x : OV L) : redL (x : L) = IsLocalRing.residue (OV L) x := by
  unfold redL; rw [dite_eq_left x.2]

theorem redL_of_mem {x : L} (hx : x ∈ intL L) : redL x = IsLocalRing.residue (OV L) ⟨x, hx⟩ :=
  redL_coe ⟨x, hx⟩

theorem redL_add {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x + y) = redL x + redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).add_mem hx hy), ← map_add (f := _)]; rfl

theorem redL_mul {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x * y) = redL x * redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).mul_mem hx hy), ← map_mul]; rfl

theorem redL_sub {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) : redL (x - y) = redL x - redL y := by
  rw [redL_of_mem hx, redL_of_mem hy, redL_of_mem ((intL L).sub_mem hx hy), ← map_sub]; rfl

theorem redL_sum {ι : Type} (s : Finset ι) (f : ι → L) (hf : ∀ i, f i ∈ intL L) :
    redL (∑ i ∈ s, f i) = ∑ i ∈ s, redL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, redL_of_mem (intL L).zero_mem]; exact map_zero _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, redL_add (hf j) (Subring.sum_mem _ fun i _ => hf i), ih]

theorem redL_sigma (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    redL (σ x) = sigK σ hσv (redL x) := by
  have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  rw [redL_of_mem hx, redL_of_mem hσx, sigK_residue]; rfl

theorem redL_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {x : L} (hx : x ∈ intL L) : redL x = 0 ↔ DvdPow ϖ 1 x := by
  rw [redL_of_mem hx]; exact residue_eq_zero_iff hϖ ⟨x, hx⟩

theorem redL_surj (a : Res L) : ∃ x ∈ intL L, redL x = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  exact ⟨y, y.2, redL_coe y⟩

theorem redL_ne_zero_of_v {x : L} (hx : Valued.v x = 1) : redL x ≠ 0 := by
  have hxi : x ∈ intL L := by show Valued.v x ≤ 1; rw [hx]
  rw [redL_of_mem hxi, Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not, isUnit_iff]
  exact hx

theorem sigK_invol (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσσ : ∀ x, σ (σ x) = x) (a : Res L) :
    sigK σ hσv (sigK σ hσv a) = a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective a
  rw [sigK_residue, sigK_residue]; congr 1; exact Subtype.ext (hσσ _)

theorem isQA_sigK {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) :
    GlobalTheory.SgAlg.IsQA (sigK σ h.2.1) := by
  obtain ⟨hσσ, hσv, -, -, ⟨x, hx, hxv⟩, -⟩ := id h
  refine ⟨sigK_invol σ _ hσσ, ⟨redL x, ?_⟩, inferInstance, ?_, fun y _ hy => hy.isUnit⟩
  · intro he
    have hσx : σ x ∈ intL L := by show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
    apply redL_ne_zero_of_v hxv
    rw [redL_sub hσx hx, redL_sigma σ hσv hx, he, sub_self]
  · have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two h hq
    have hne := redL_ne_zero_of_v h2
    have h2i : (2 : L) ∈ intL L := by show Valued.v (2 : L) ≤ 1; rw [h2]
    have : redL (2 : L) = 2 := by
      rw [show (2 : L) = 1 + 1 by norm_num, redL_add (intL L).one_mem (intL L).one_mem,
        redL_of_mem (intL L).one_mem]
      rw [show (⟨1, (intL L).one_mem⟩ : OV L) = 1 from rfl, map_one]; norm_num
    rw [this] at hne
    exact hne.isUnit

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def redM {a b : Type} (A : Matrix a b L) : Matrix a b (Res L) := A.map redL

def IntM {a b : Type} (A : Matrix a b L) : Prop := ∀ i j, A i j ∈ intL L

theorem intM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => (intL L).mul_mem (hA i l) (hB l j)

theorem intM_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : IntM (Formalism.UG.cT σ A) := by
  intro i j; show Valued.v (σ (A j i)) ≤ 1; rw [hσv]; exact hA j i

theorem redM_mul {a b c : Type} [Fintype b] {A : Matrix a b L} {B : Matrix b c L} (hA : IntM A) (hB : IntM B) :
    redM (A * B) = redM A * redM B := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.mul_apply]
  rw [redL_sum _ _ fun l => (intL L).mul_mem (hA i l) (hB l j)]
  exact Finset.sum_congr rfl fun l _ => redL_mul (hA i l) (hB l j)

theorem redM_sub {a b : Type} {A B : Matrix a b L} (hA : IntM A) (hB : IntM B) :
    redM (A - B) = redM A - redM B := by
  ext i j; simp only [redM, Matrix.map_apply, Matrix.sub_apply]; exact redL_sub (hA i j) (hB i j)

theorem redM_cT (σ : L →+* L) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : Type} {A : Matrix a b L}
    (hA : IntM A) : redM (Formalism.UG.cT σ A) = GlobalTheory.SgAlg.cT (sigK σ hσv) (redM A) := by
  ext i j
  show redL (σ (A j i)) = sigK σ hσv (redL (A j i))
  exact redL_sigma σ hσv (hA j i)

theorem redM_eq_zero_iff {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {a b : Type} {A : Matrix a b L} (hA : IntM A) : redM A = 0 ↔ ∀ i j, DvdPow ϖ 1 (A i j) := by
  constructor
  · intro h i j; rw [← redL_eq_zero_iff hϖ (hA i j)]; exact congrFun (congrFun h i) j
  · intro h; ext i j; exact (redL_eq_zero_iff hϖ (hA i j)).2 (h i j)

theorem redM_one {a : Type} [DecidableEq a] : redM (1 : Matrix a a L) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · rw [redL_of_mem (intL L).one_mem]; exact map_one _
  · rw [redL_of_mem (intL L).zero_mem]; exact map_zero _

theorem free_redM {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {z : ι → Fin n → L} (hz : ∀ i r, z i r ∈ intL L)
    (hI : IndepMod ϖ z) : GlobalTheory.SgAlg.Free (redM (Matrix.of fun r i => z i r)) := by
  set X : Matrix (Fin n) ι (Res L) := redM (Matrix.of fun r i => z i r)
  have hinj : LinearMap.ker (Matrix.toLin' X) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro e he
    choose d hd hde using fun i => redL_surj (e i)
    have hs : ∀ r, DvdPow ϖ 1 (∑ i, d i * z i r) := by
      intro r
      rw [← redL_eq_zero_iff hϖ (Subring.sum_mem _ fun i _ => (intL L).mul_mem (hd i) (hz i r)),
        redL_sum _ _ fun i => (intL L).mul_mem (hd i) (hz i r)]
      have := congrFun he r
      rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at this
      rw [Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [redL_mul (hd i) (hz i r), hde, mul_comm]; rfl
    have h0 := hI d hd hs
    funext i
    rw [← hde i]
    exact (redL_eq_zero_iff hϖ (hd i)).2 (h0 i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem hform_eq_entry (σ : L →+* L) {n : ℕ} {ι : Type} (J : Matrix (Fin n) (Fin n) L) (z : ι → Fin n → L) (a b : ι) :
    Formalism.UG.hform σ J (z a) (z b) = (Formalism.UG.cT σ (Matrix.of fun r i => z i r) * J * Matrix.of fun r i => z i r) a b := by
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.Hk3.ResWitt

namespace GlobalTheory.Hk3.ResWitt

open Formalism.UG GlobalTheory.Hk3.IntWitt

theorem exists_int_unitary_mod_of_gram_mod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hJh ι _ z z' hz hz' hI hI' hG
  classical
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ := hU.2.2.2.1
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  obtain ⟨g0, hg0⟩ := hJT
  have hJi : IntM J := by
    intro i j; rw [hJdef, ← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (intL L)) i j).2
  have hJinv : IntM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    intro i j; rw [← hg0, ← map_inv]; exact (((g0⁻¹ : GL (Fin n') (intL L)) : Matrix (Fin n') (Fin n') (intL L)) i j).2
  set X : Matrix (Fin n') ι L := Matrix.of fun r i => z i r with hXdef
  set X' : Matrix (Fin n') ι L := Matrix.of fun r i => z' i r with hX'def
  have hXi : IntM X := fun r i => hz i r
  have hX'i : IntM X' := fun r i => hz' i r

  have hHerm : GlobalTheory.SgAlg.IsHermU (sigK σ hσv) (redM J) := by
    refine ⟨?_, ?_⟩
    · rw [← redM_cT σ hσv hJi]; congr 1; ext i j; exact hJh j i
    · refine Matrix.isUnit_det_of_right_inverse (B := redM ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) ?_
      rw [← redM_mul hJi hJinv, hJdef, ← Units.val_mul, mul_inv_cancel, Units.val_one, redM_one]
  have hgram : ∀ (Y : Matrix (Fin n') ι L), IntM Y →
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM Y) (redM Y) = redM (Formalism.UG.cT σ Y * J * Y) := by
    intro Y hY
    rw [redM_mul (intM_mul (intM_cT hσv hY) hJi) hY, redM_mul (intM_cT hσv hY) hJi, redM_cT σ hσv hY]
    rfl
  have hP : GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X) (redM X) =
      GlobalTheory.SgAlg.pairM (sigK σ hσv) (redM J) (redM X') (redM X') := by
    rw [hgram X hXi, hgram X' hX'i]
    have hint : ∀ Y : Matrix (Fin n') ι L, IntM Y → IntM (Formalism.UG.cT σ Y * J * Y) :=
      fun Y hY => intM_mul (intM_mul (intM_cT hσv hY) hJi) hY
    have h0 : redM (Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) = 0 := by
      rw [redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ X' * J * X' - Formalism.UG.cT σ X * J * X) (fun i j => (intL L).sub_mem (hint X' hX'i i j) (hint X hXi i j))]
      intro a b
      have := hG a b
      rwa [hform_eq_entry, hform_eq_entry] at this
    rw [redM_sub (hint X' hX'i) (hint X hXi), sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨gb, hgU, hgX⟩ := GlobalTheory.witt_free_tuples (sigK σ hσv) (isQA_sigK hU hq) (redM J) hHerm (redM X) (redM X')
    (free_redM hϖ hz hI) (free_redM hϖ hz' hI') hP
  choose g hgi hge using fun i j => redL_surj (gb i j)
  have hgI : IntM (Matrix.of g) := fun i j => hgi i j
  have hred : redM (Matrix.of g) = gb := by ext i j; exact hge i j
  refine ⟨Matrix.of g, hgi, ?_, ?_⟩
  · have hint1 : IntM (Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g) := intM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI
    refine (redM_eq_zero_iff hϖ (A := Formalism.UG.cT σ (Matrix.of g) * J * Matrix.of g - J) (fun i j => (intL L).sub_mem (hint1 i j) (hJi i j))).1 ?_
    rw [redM_sub hint1 hJi, redM_mul (intM_mul (intM_cT hσv hgI) hJi) hgI, redM_mul (intM_cT hσv hgI) hJi,
      redM_cT σ hσv hgI, hred]
    exact sub_eq_zero.2 hgU
  · intro i r
    have hint2 : IntM (Matrix.of g * X) := intM_mul hgI hXi
    have h0 : redM (Matrix.of g * X - X') = 0 := by
      rw [redM_sub hint2 hX'i, redM_mul hgI hXi, hred, hgX, sub_self]
    have := (redM_eq_zero_iff hϖ (A := Matrix.of g * X - X') (fun i j => (intL L).sub_mem (hint2 i j) (hX'i i j))).1 h0 r i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hXdef, hX'def] using this

end GlobalTheory.Hk3.ResWitt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairingStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_integral_vectors_pairing : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod | exact GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod | (intros; apply GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizer
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizerStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_unitary_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.witt_mod_base | exact GlobalTheory.Hk3.IntWittBase.witt_mod_base | (intros; apply GlobalTheory.Hk3.IntWittBase.witt_mod_base <;> assumption)
end
