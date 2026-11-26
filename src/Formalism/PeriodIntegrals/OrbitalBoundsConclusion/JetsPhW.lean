module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLow
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.FirstJetIntegralGeneralHolds
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

theorem logOk_low {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (h : LogOk l ex) :
    PowerSeries.constantCoeff l = 0 ∧
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 ∧ ‖PowerSeries.coeff 1 ex‖ ≤ 1 := by
  obtain ⟨hex, hsub, v, hvint, hv⟩ := h
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hc := congrArg MvPowerSeries.constantCoeff hsub
    rw [const_subst hex] at hc
    rw [hc]
    exact PowerSeries.constantCoeff_X
  have hl1 : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hsub
    rw [pcoeff1_subst hex l, PowerSeries.coeff_one_X] at hc
    exact hc
  have hv0 : PowerSeries.coeff 0 v * PowerSeries.coeff 1 l = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hv
    simpa [PowerSeries.coeff_mul, dX] using hc
  have hev : PowerSeries.coeff 1 ex = PowerSeries.coeff 0 v := by
    linear_combination PowerSeries.coeff 0 v * hl1 - PowerSeries.coeff 1 ex * hv0
  refine ⟨hl0, hl1, ?_⟩
  rw [hev]
  exact hvint 0

theorem firstJetIntegralGeneral_holds : OneG := by
  intro p _ l ex ph h hp hs
  obtain ⟨_, _, h2⟩ := logOk_low h
  have h1 := (logOk_low h).2.1
  have h0 := (logOk_low h).1
  have hex := h.1
  have hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1 := by simp
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp [Xv]
  have hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X]
  have hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [const_subst hX0]
    exact h0
  have hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) =
      PowerSeries.coeff 1 l := by
    rw [coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]
  have hB0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hBe : MvPowerSeries.coeff (Finsupp.single () 1)
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l := by
    rw [MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]
  have hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [mulBy, const_subst hB0]
    exact hex
  have hAe : MvPowerSeries.coeff (Finsupp.single () 1)
      (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1 := by
    rw [mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]
    linear_combination (-1 : ℂ_[p]) * h1
  have hf : MvPowerSeries.coeff (Finsupp.single () 1)
      (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]
  have hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]
  have hint := hs.2 (Finsupp.single () 1)
  unfold IsIntP at hint
  rw [coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg] at hint
  have hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1 := by
    have h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph) := by
      ring
    rw [h2c, norm_neg, norm_mul, norm_two hp, one_mul] at hint
    exact hint
  show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1
  rw [pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) h2

end PI.JetsPhW.Low
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv (R := ℂ_[p]) i f

def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph

def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)

def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv (R := ℂ_[p]) i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)

def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)

def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0

def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)

def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g

def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))

def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)

def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)

abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l

def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

end PI.JetsPhW.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.SecondJetIntegralGeneralHolds
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

private lemma coeff_mulBy_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (hlog : LogOk l ex) (c : ℂ_[p])
    {A : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c A) = 0 ∧
      MvPowerSeries.coeff E0 (mulBy l ex c A) = c * MvPowerSeries.coeff E0 A ∧
      MvPowerSeries.coeff E1 (mulBy l ex c A) = c * MvPowerSeries.coeff E1 A := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hI : MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_mul, hAl, mul_zero]
  have e : mulBy l ex c A = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst A l) ex := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, const_subst hI]; exact hlog.1
  · rw [e, coeff_expX_subst hI, MvPowerSeries.coeff_C_mul, coeff_expX_subst hA]
    linear_combination (c * MvPowerSeries.coeff E0 A) * hle
  · rw [e, coeff_expY_subst hI, MvPowerSeries.coeff_C_mul, coeff_expY_subst hA]
    linear_combination (c * MvPowerSeries.coeff E1 A) * hle

private lemma coeff_be_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
    (hlog : LogOk l ex) {A B : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hA1 : MvPowerSeries.coeff E1 A = 0)
    (hB0 : MvPowerSeries.coeff E0 B = 0) :
    MvPowerSeries.coeff E0 (be l ex ph A B) = 0 ∧ MvPowerSeries.coeff E1 (be l ex ph A B) = 0 ∧
      MvPowerSeries.coeff bivariateExponentMonomial (be l ex ph A B) =
        2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B *
          (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex * PowerSeries.coeff 1 l ^ 2 +
            PowerSeries.coeff 2 ph) := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hBl : MvPowerSeries.constantCoeff (PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hB]; exact hl0
  have hS : MvPowerSeries.constantCoeff
      (PowerSeries.subst A l + PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), hAl, hBl, add_zero]
  have ea : add l ex A B = PowerSeries.subst (PowerSeries.subst A l + PowerSeries.subst B l) ex := rfl
  have hadd : MvPowerSeries.constantCoeff (add l ex A B) = 0 := by
    rw [ea, const_subst hS]; exact hlog.1
  have eb : be l ex ph A B = PowerSeries.subst (add l ex A B) ph - PowerSeries.subst A ph -
      PowerSeries.subst B ph := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eb, map_sub, map_sub, coeff_expX_subst hadd, coeff_expX_subst hA, coeff_expX_subst hB, ea, coeff_expX_subst hS, map_add (f := _),
      coeff_expX_subst hA, coeff_expX_subst hB, hB0]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E0 A) * hle
  · rw [eb, map_sub, map_sub, coeff_expY_subst hadd, coeff_expY_subst hA, coeff_expY_subst hB, ea, coeff_expY_subst hS, map_add (f := _),
      coeff_expY_subst hA, coeff_expY_subst hB, hA1]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E1 B) * hle
  · rw [eb, map_sub, map_sub, coeff_expXY_subst hadd, coeff_expXY_subst hA, coeff_expXY_subst hB,
      ea, coeff_expXY_subst hS, coeff_expX_subst hS, coeff_expY_subst hS, map_add, map_add, map_add, coeff_expXY_subst hA, coeff_expXY_subst hB,
      coeff_expX_subst hA, coeff_expX_subst hB, coeff_expY_subst hA, coeff_expY_subst hB, hA1, hB0]
    linear_combination (PowerSeries.coeff 1 ph * (MvPowerSeries.coeff bivariateExponentMonomial A + MvPowerSeries.coeff bivariateExponentMonomial B) +
      2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B * PowerSeries.coeff 2 ph *
        (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

theorem secondJetIntegralGeneral_holds : TwoG := by
  intro p _ l ex ph a b hlog hsim
  obtain ⟨hl0, hle, he1⟩ := logOk_low hlog
  have hex0 : PowerSeries.constantCoeff ex = 0 := hlog.1
  have cX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by
    simp [Xv]
  have x00 : MvPowerSeries.coeff E0 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x01 : MvPowerSeries.coeff E1 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x10 : MvPowerSeries.coeff E0 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x11 : MvPowerSeries.coeff E1 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  obtain ⟨ma0, ma1, ma2⟩ := coeff_mulBy_low_degree hlog a (cX 0)
  obtain ⟨mb0, mb1, mb2⟩ := coeff_mulBy_low_degree hlog b (cX 1)
  obtain ⟨u0, u1, u2⟩ := coeff_be_low_degree ph hlog ma0 (cX 1) (by rw [ma2, x01, mul_zero]) x10
  obtain ⟨v0, v1, v2⟩ := coeff_be_low_degree ph hlog (cX 0) mb0 x01 (by rw [mb1, x10, mul_zero])
  set D := (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
    MvPowerSeries (Fin 2) ℂ_[p]) with hD
  have hD0 : MvPowerSeries.constantCoeff D = 0 := hsim.1
  have d0 : MvPowerSeries.coeff E0 D = 0 := by rw [hD, map_sub, u0, v0, sub_zero]
  have d1 : MvPowerSeries.coeff E1 D = 0 := by rw [hD, map_sub, u1, v1, sub_zero]

  have hs : (bivariateExponentMonomial.sum fun _ k => k) = 2 := degree_expXY
  have hexp : MvPowerSeries.coeff bivariateExponentMonomial (expMv D) = MvPowerSeries.coeff bivariateExponentMonomial D := by
    change (∑ n ∈ Finset.range ((bivariateExponentMonomial.sum fun _ k => k) + 1),
      MvPowerSeries.coeff bivariateExponentMonomial (D ^ n) / (n.factorial : ℂ_[p])) = _
    rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_two,
      coeff_expXY_mul hD0 hD0, d0, d1]
    simp [MvPowerSeries.coeff_one, expXY_ne_zero]
  have hint : ‖MvPowerSeries.coeff bivariateExponentMonomial D‖ ≤ 1 := by
    rw [← hexp]; exact hsim.2 bivariateExponentMonomial
  have hjet : jet ex ph 2 = 2 * (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex +
      PowerSeries.coeff 2 ph * PowerSeries.coeff 1 ex ^ 2) := by
    unfold jet
    rw [pcoeff2_subst hex0 ph]
    norm_num
  have hval : MvPowerSeries.coeff bivariateExponentMonomial D = (a - b) * jet ex ph 2 * PowerSeries.coeff 1 l ^ 2 := by
    rw [hD, map_sub, u2, v2, ma1, mb2, x00, x11, hjet]
    linear_combination (-2 * (a - b) * PowerSeries.coeff 2 ph *
      (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

  have hl1 : 1 ≤ ‖PowerSeries.coeff 1 l‖ := by
    have h := congrArg norm hle
    rw [norm_mul, norm_one] at h
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg (PowerSeries.coeff 1 ex), norm_nonneg (PowerSeries.coeff 1 l)]
  rw [hval, norm_mul, norm_pow] at hint
  unfold IsIntP
  have hxy := norm_nonneg ((a - b) * jet ex ph 2)
  have := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hl1) hxy
  linarith

end PI.JetsPhW.Low
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.HighGOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.PolarizationDifferenceFormulaHolds
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

namespace R

variable {K : Type*} [CommRing K]

theorem cc_l {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := PowerSeries.constantCoeff_subst (R := K) (PowerSeries.HasSubst.of_constantCoeff_zero' hex) l
  rw [hl] at h1
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
  simp only [pow_zero, map_one, smul_eq_mul, mul_one] at h1
  have h2 : PowerSeries.coeff 0 l = 0 := by
    rw [← h1]
    exact PowerSeries.constantCoeff_X
  simpa using h2

theorem l_ex {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) {τ : Type*} {x : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x ex) l = x := by
  have ha : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hb : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← PowerSeries.subst_comp_subst_apply ha hb, hl, PowerSeries.subst_X hb]

theorem ph_ex {ex ph : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0) {τ : Type*}
    {s : MvPowerSeries τ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    PowerSeries.subst (PowerSeries.subst s ex) ph =
      PowerSeries.subst s (PowerSeries.subst ex ph : PowerSeries K) := (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
    (PowerSeries.HasSubst.of_constantCoeff_zero hs) ph).symm

theorem cc_sum {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0) {τ : Type*}
    {a b : MvPowerSeries τ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l + PowerSeries.subst b l) = 0 := by
  rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero ha l hl0,
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0, add_zero]

end R

section
variable {p : ℕ} [Fact p.Prime] {σ : Type*} {l ex ph : PowerSeries ℂ_[p]}

theorem phAt_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph) := by
  unfold PI.JetsPhW.phAt PI.JetsPhW.add psi
  exact PI.JetsPhW.W.R.ph_ex hex
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

theorem l_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold PI.JetsPhW.add
  exact PI.JetsPhW.W.R.l_ex hex hl
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

theorem cc_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold PI.JetsPhW.add
  exact PowerSeries.constantCoeff_subst_eq_zero
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb) ex hex

end

theorem cubeDefectFormula_holds : Rw3 := by
  intro p _ l ex ph h
  obtain ⟨hex, hl, -⟩ := h
  have h0 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h1 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h2 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  unfold PI.JetsPhW.cubeE
  rw [phAt_add hex hl (cc_add hex hl h0 h1) h2,
    l_add hex hl h0 h1, phAt_add hex hl h0 h1,
    phAt_add hex hl h1 h2, phAt_add hex hl h2 h0]

end PI.JetsPhW.W
end
end

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

section
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem Dv_add (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f + g) = Dv v i f + Dv v i g := by
  simp only [Dv, map_add (f := _), mul_add]

theorem Dv_sub (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f - g) = Dv v i f - Dv v i g := by
  simp only [Dv, map_sub, mul_sub]

end

private theorem pderiv_lX (hP : PdSelf) (hN : PdNe) {p : ℕ} [Fact p.Prime]
    {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) :
    MvPowerSeries.pderiv (R := ℂ_[p]) i (lX l j : MvPowerSeries σ ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (PI.JetsPhW.dX l) else 0 := by
  split_ifs with h
  · subst h
    exact hP p σ j l
  · exact hN p σ i j l h

private theorem isIntP_constantCoeff_of_integralMv {p : ℕ} [Fact p.Prime] {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (h : PI.JetsPhW.IntegralMv F) : PI.JetsPhW.IsIntP (MvPowerSeries.constantCoeff F) := by
  have h0 := h 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem highG_of (hC : DChain) (hS : DSelf) (hN : PdNe) (hP : PdSelf) (hE : Ev0) (hJ : JetD)
    (hL : LogDer) (hI : Dint) : HighG := by
  intro p hp l ex ph hpair hD i hi1 hi2
  have hDdef := cubeDefectFormula_holds p l ex ph hpair
  obtain ⟨hex, hl, v, hvint, hv⟩ := hpair
  obtain ⟨hD0, hDe⟩ := hD
  simp only [sub_zero] at hD0 hDe
  have hl0 : PowerSeries.constantCoeff l = 0 := PI.JetsPhW.W.R.cc_l hex hl
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    intro j; simp
  have hLc : ∀ j : Fin 3, MvPowerSeries.constantCoeff (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun j => (hE p (Fin 3) _ l (hX j)).trans hl0
  have hpd : ∀ i j : Fin 3, MvPowerSeries.pderiv (R := ℂ_[p]) i (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) else 0 :=
    fun i j => pderiv_lX hP hN l i j
  have hd : ∀ (i : Fin 3) (S : MvPowerSeries (Fin 3) ℂ_[p]) (c : ℂ_[p]) (g : PowerSeries ℂ_[p]),
      MvPowerSeries.constantCoeff S = 0 →
      MvPowerSeries.pderiv (R := ℂ_[p]) i S =
        MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) →
      Dv v i (PowerSeries.subst S g) = MvPowerSeries.C c * PowerSeries.subst S (PI.JetsPhW.dX g) :=
    fun i S c g h1 h2 => hC p (Fin 3) i l v g S c hv h1 h2
  have hXne : ∀ (i j : Fin 3) (g : PowerSeries ℂ_[p]), j ≠ i →
      Dv v i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) g) = 0 := by
    intro i j g h
    simp only [Dv]
    rw [hN p (Fin 3) i j g h, mul_zero]
  have hq : ∀ j : Fin 3, (PI.JetsPhW.phAt ph (PI.JetsPhW.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) ph := fun j => rfl
  have c012 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c01 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c12 : MvPowerSeries.constantCoeff (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c20 : MvPowerSeries.constantCoeff (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have p0_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_12 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_20 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_20 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p2_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 2 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p2_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 2 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have e1 : Dv v 0 (PI.JetsPhW.cubeE l ex ph) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph) := by
    rw [hDdef]
    simp only [Dv_add, Dv_sub, hq]
    rw [hd 0 _ 1 _ c012 p0_012, hd 0 _ 1 _ c01 p0_01, hd 0 _ 0 _ c12 p0_12, hd 0 _ 1 _ c20 p0_20,
      hS p (Fin 3) 0 v ph, hXne 0 1 ph (by decide), hXne 0 2 ph (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e2 : Dv v 1
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph)) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) := by
    simp only [Dv_add, Dv_sub]
    rw [hd 1 _ 1 _ c012 p1_012, hd 1 _ 1 _ c01 p1_01, hd 1 _ 0 _ c20 p1_20, hXne 1 0 _ (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e3 : Dv v 2
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) := by
    rw [Dv_sub, hd 2 _ 1 _ c012 p2_012, hd 2 _ 0 _ c01 p2_01]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero]
  have h1 : PI.JetsPhW.IntegralMv (Dv v 0 (PI.JetsPhW.cubeE l ex ph)) := hL p (Fin 3) 0 v _ hvint hD0 hDe
  rw [e1] at h1
  have h2 := hI p (Fin 3) 1 v _ hvint h1
  rw [e2] at h2
  have h3 := hI p (Fin 3) 2 v _ hvint h2
  rw [e3] at h3
  have hk : ∀ k : ℕ, PI.JetsPhW.IntegralMv (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
      ((PI.JetsPhW.dX (A := ℂ_[p]))^[k + 3] (psi ex ph))) := by
    intro k
    induction k with
    | zero => exact h3
    | succ k ih =>
      have h4 := hI p (Fin 3) 0 v _ hvint ih
      rw [hd 0 _ 1 _ c012 p0_012, map_one, one_mul] at h4
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Function.iterate_succ_apply']
      exact h4
  have hψ : PowerSeries.constantCoeff (psi ex ph) = PowerSeries.constantCoeff ph := hE p Unit ex ph hex
  rcases i with _ | _ | _ | k
  ·
    have hph : PowerSeries.constantCoeff ph = 0 := by
      have h0 := hD0
      rw [hDdef] at h0
      simp only [map_add (f := _), map_sub, hq] at h0
      rw [hE p (Fin 3) _ _ c012, hE p (Fin 3) _ _ c01, hE p (Fin 3) _ _ c12, hE p (Fin 3) _ _ c20,
        hE p (Fin 3) _ _ (hX 0), hE p (Fin 3) _ _ (hX 1), hE p (Fin 3) _ _ (hX 2), hψ] at h0
      linear_combination h0
    rw [hJ p ex ph]
    show PI.JetsPhW.IsIntP (PowerSeries.constantCoeff (psi ex ph))
    rw [hψ, hph]
    simp [PI.JetsPhW.IsIntP]
  · exact absurd rfl hi1
  · exact absurd rfl hi2
  · have hc := isIntP_constantCoeff_of_integralMv (hk k)
    rw [hE p (Fin 3) _ _ c012] at hc
    rw [hJ p ex ph]
    exact hc

end PI.JetsPhW.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ChainSt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLog
noncomputable section

open Classical

namespace PI.JetsPhW.W

open PI.JetsPhW MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem intMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul hF hG

theorem intMv_pderiv {F : MvPowerSeries σ ℂ_[p]} (i : σ) (hF : IntegralMv F) :
    IntegralMv (pderiv (R := ℂ_[p]) i F) :=
  _root_.UpperTheory.Reformulated.B.Gwb7.intMv_pderiv i hF

theorem intMv_inv {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 :=
  _root_.UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv hF h1

theorem coeff_pow_eq_zero {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero n hf)

def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ Finset.range N, coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expT, map_sum, map_smul, smul_eq_mul, div_eq_inv_mul]

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expMv, coeff_expT]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_range] at *; omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero hf (by omega), zero_div]

theorem pderiv_expT (f : MvPowerSeries σ ℂ_[p]) (i : σ) (N : ℕ) :
    pderiv (R := ℂ_[p]) i (expT f (N + 1)) = pderiv (R := ℂ_[p]) i f * expT f N := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expT, map_sum, Derivation.map_smul, Finset.mul_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pderiv_pow, Nat.add_sub_cancel, smul_eq_C_mul, smul_eq_C_mul]
  have hn : ((n + 1 : ℕ) : MvPowerSeries σ ℂ_[p]) = C ((n + 1 : ℕ) : ℂ_[p]) := (map_natCast C _).symm
  have key : ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) = (n.factorial : ℂ_[p])⁻¹ := by
    have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  rw [hn]
  calc C ((n + 1).factorial : ℂ_[p])⁻¹ * (C ((n + 1 : ℕ) : ℂ_[p]) * f ^ n * pderiv (R := ℂ_[p]) i f)
      = C (((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p])) * (f ^ n * pderiv (R := ℂ_[p]) i f) := by
        rw [map_mul]; ring
    _ = pderiv (R := ℂ_[p]) i f * (C (n.factorial : ℂ_[p])⁻¹ * f ^ n) := by rw [key]; ring

theorem pderiv_expMv {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) (i : σ) :
    pderiv (R := ℂ_[p]) i (expMv f) = pderiv (R := ℂ_[p]) i f * expMv f := by
  ext α
  have h1 : coeff α (pderiv (R := ℂ_[p]) i (expMv f)) =
      coeff α (pderiv (R := ℂ_[p]) i (expT f (Finsupp.degree α + 1 + 1))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_expMv_eq_expT hf]
    rw [map_add (f := _), Finsupp.degree_single]; omega
  rw [h1, pderiv_expT, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  refine (coeff_expMv_eq_expT hf ?_).symm
  have := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hx)
  rw [map_add (f := _)] at this; omega

theorem constantCoeff_expMv (f : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem L0 {f c : MvPowerSeries σ ℂ_[p]} (i : σ) (hf : constantCoeff f = 0)
    (hE : IntegralMv (expMv f)) (hc : IntegralMv c) : IntegralMv (c * pderiv (R := ℂ_[p]) i f) := by
  obtain ⟨G, hG, hEG⟩ := intMv_inv hE (constantCoeff_expMv f)
  have : c * pderiv (R := ℂ_[p]) i f = c * pderiv (R := ℂ_[p]) i (expMv f) * G := by
    rw [pderiv_expMv hf, mul_assoc, mul_assoc, hEG, mul_one]
  rw [this]
  exact intMv_mul (intMv_mul hc (intMv_pderiv i hE)) hG

end PI.JetsPhW.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffPowEqZeroOfDegreeLt
noncomputable section

open PI.JetsPhW

namespace PI.JetsPhW.Ch

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_dX (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PI.JetsPhW.dX f) = ((n : R) + 1) * PowerSeries.coeff (n + 1) f := by
  simp only [PI.JetsPhW.dX, PowerSeries.coeff_mk]

theorem dX_eq (f : PowerSeries R) : dX f = PowerSeries.derivative (R := R) f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_dX]
  ring

theorem degree_le_of_le {y e : σ →₀ ℕ} (h : y ≤ e) : y.degree ≤ e.degree := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  rw [map_add (f := _)]
  exact Nat.le_add_right _ _

theorem coeff_pow_eq_zero_of_degree_lt {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {e : σ →₀ ℕ} {d : ℕ} (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d ha)

theorem coeff_subst_congr {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {f g : PowerSeries R} {N : ℕ} (hfg : ∀ k < N, PowerSeries.coeff k f = PowerSeries.coeff k g)
    {e : σ →₀ ℕ} (he : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) = MvPowerSeries.coeff e (PowerSeries.subst a g) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k < N
  · rw [hfg k hk]
  · rw [coeff_pow_eq_zero_of_degree_lt ha (lt_of_lt_of_le he (not_lt.mp hk)), smul_zero, smul_zero]

theorem coeff_mul_congr (u : MvPowerSeries σ R) {f g : MvPowerSeries σ R} {e : σ →₀ ℕ}
    (hfg : ∀ y ≤ e, MvPowerSeries.coeff y f = MvPowerSeries.coeff y g) :
    MvPowerSeries.coeff e (u * f) = MvPowerSeries.coeff e (u * g) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hfg p.2 (by rw [← hp]; exact le_add_self)]

theorem pderiv_subst_coe (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (q : Polynomial R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a (q : PowerSeries R)) =
      MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (dX (q : PowerSeries R)) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [dX_eq, PowerSeries.derivative_coe, PowerSeries.subst_coe hs,
    PowerSeries.subst_coe hs, Derivation.map_aeval, smul_eq_mul]
  ring

theorem pderiv_subst (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g) =
      MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (dX g) := by
  ext e
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i
        (PowerSeries.subst a (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    congr 1
    refine coeff_subst_congr ha (N := e.degree + 2) (fun k hk => ?_) ?_
    · exact (PowerSeries.coeff_coe_trunc_of_lt hk).symm
    · rw [map_add (f := _), Finsupp.degree_single]
      omega
  have h2 : MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (PI.JetsPhW.dX g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i a *
        PowerSeries.subst a (PI.JetsPhW.dX (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    refine coeff_mul_congr _ fun y hy => ?_
    refine coeff_subst_congr ha (N := e.degree + 1) (fun k hk => ?_) ?_
    · rw [coeff_dX, coeff_dX, PowerSeries.coeff_coe_trunc_of_lt (n := k + 1) (m := e.degree + 2) (by omega)]
    · exact Nat.lt_succ_of_le (degree_le_of_le hy)
  rw [h1, pderiv_subst_coe i ha, h2]

theorem pderiv_subst_X_self (i : σ) (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i) (dX g) := by
  rw [pderiv_subst i (a := MvPowerSeries.X i) (MvPowerSeries.constantCoeff_X i) g,
    MvPowerSeries.pderiv_X_self, one_mul]

theorem pderiv_subst_X_ne {i j : σ} (h : j ≠ i) (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst (MvPowerSeries.X j) g) = 0 := by
  rw [pderiv_subst i (a := MvPowerSeries.X j) (MvPowerSeries.constantCoeff_X j) g,
    MvPowerSeries.pderiv_X_of_ne h, zero_mul]

theorem subst_one' (a : MvPowerSeries σ R) : PowerSeries.subst a (1 : PowerSeries R) = 1 := by
  simpa using PowerSeries.subst_C (a := a) (1 : R)

private theorem powerSeries_hasSubst_mvPowerSeries_X (i : σ) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)

theorem subst_v_mul {l v : PowerSeries R} (hv : v * dX l = 1) (i : σ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) v *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) (dX l) = 1 := by
  rw [← PowerSeries.subst_mul (powerSeries_hasSubst_mvPowerSeries_X i), hv, subst_one']

end Chain

end PI.JetsPhW.Ch
end
end

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

theorem pderiv_subst_self : PdSelf := fun _ _ _ i g => Ch.pderiv_subst_X_self i g

theorem pderiv_subst_ne : PdNe := fun _ _ _ _ _ g h => Ch.pderiv_subst_X_ne h g

theorem derivative_chain_rule : DChain := by
  intro p _ σ i l v g s c hv hs hpd
  unfold Dv
  rw [Ch.pderiv_subst i hs, hpd]
  linear_combination (MvPowerSeries.C c * PowerSeries.subst s (dX g)) * Ch.subst_v_mul hv i

theorem derivative_self : DSelf := by
  intro p _ σ i v g
  unfold Dv
  rw [Ch.pderiv_subst_X_self, ← PowerSeries.subst_mul
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) v (dX g)]

theorem evaluation_at_zero : Ev0 := by
  intro p _ σ s g hs
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have h2 : MvPowerSeries.constantCoeff
      (PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ (by simp)
  have h4 : PowerSeries.subst s g = PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g)) +
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
    rw [← PowerSeries.subst_C (a := s) (PowerSeries.constantCoeff g), ← PowerSeries.subst_add hsub,
      sub_add_cancel]
  rw [h4, map_add (f := _), h2, zero_add, MvPowerSeries.constantCoeff_C]

theorem jet_derivative_integrality : JetD := by
  intro p _ ex ph n
  have h : (dX (A := ℂ_[p])) = ⇑(PowerSeries.derivative (R := ℂ_[p])) := funext Ch.dX_eq
  rw [h, PowerSeries.constantCoeff_iterate_derivative]
  rfl

theorem intMv_subst_X {p : ℕ} [Fact p.Prime] {σ : Type*} {v : PowerSeries ℂ_[p]} (hv : IntP v) (i : σ) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hv _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem derivative_integral : Dint := fun _ _ _ i _ _ hv hf => intMv_mul (intMv_subst_X hv i) (intMv_pderiv i hf)

theorem log_derivative_integral_jet_integrality : LogDer := fun _ _ _ i _ _ hv hf hE => L0 i hf hE (intMv_subst_X hv i)

end PI.JetsPhW.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.GlueHoldsVar
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

theorem glue_holds_var : Glue := by
  intro hI hH hO hT
  refine ⟨?_, ?_, ?_⟩
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hc i hi1 hi2
    exact hH p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc i hi1 hi2
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hp hc
    exact hO p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hp hc
  · intro p _ W wq ex ph a b h1 h2 h3 h4 h6 hW hex hl hc
    exact hT p (PI.JetsPhW.flog W wq) ex ph a b ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc

end PI.JetsPhW.W
end
end

theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
