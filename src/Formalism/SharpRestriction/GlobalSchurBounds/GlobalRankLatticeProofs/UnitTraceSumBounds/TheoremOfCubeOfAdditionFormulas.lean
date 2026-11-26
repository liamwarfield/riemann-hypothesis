module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNormHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.LogThirdPointSum
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.CoeffSingleLg
noncomputable section

namespace PI.FglShared

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem l_constantCoeff {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h := constantCoeff_subst_of_zero (a := ex) hex0 l
  rw [hinv] at h
  rw [← h]
  exact PowerSeries.constantCoeff_X

theorem subst_subst_eq {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']

theorem l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : l ≠ 0 := by
  rintro rfl
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  rw [← PowerSeries.coe_substAlgHom hex, map_zero] at hinv
  exact PowerSeries.X_ne_zero hinv.symm

theorem exists_coeff_ne {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : ∃ k, k ≠ 0 ∧ PowerSeries.coeff k l ≠ 0 := by
  have hl0 := l_constantCoeff hex0 hinv
  by_contra hc
  push Not at hc
  apply l_ne_zero hex0 hinv
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hl0
  · simpa using hc k hk

theorem subst_ne_zero {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) (hne : y ≠ 0) : PowerSeries.subst y ex ≠ 0 := by
  intro h0
  have h := subst_subst_eq hex0 hinv hy
  rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)] at h
  exact hne h.symm

theorem coeff_single_lg {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) {k : ℕ}
    (hk : k ≠ 0) : coeff (Finsupp.single i k) (PowerSeries.subst (X j : MvPowerSeries σ ℂ_[p]) l) =
      if j = i then PowerSeries.coeff k l else 0 := by
  rw [PowerSeries.coeff_subst_single]
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : Finsupp.single i k ≠ Finsupp.single j ((Finsupp.single i k) j) := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hji), Finsupp.single_zero]
      exact Finsupp.single_ne_zero.mpr hk
    rw [if_neg hne, if_neg hji]

end PI.FglShared

end
end

section -- merged from Formalism.PeriodIntegrals.PhiCubeOfFactor
noncomputable section

open Classical

namespace PI.PhiCubeOfFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex E : PowerSeries ℂ_[p]) (Q : MvPowerSeries (Fin 2) ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * eAt E (add l ex (Xv 0) (Xv 1)) *
        eAt E (sub l ex (Xv 0) (Xv 1)) =
      Q * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      Q = add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * n) →
    Simeq (phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt E (Xv 0) + 2 * phAt E (Xv 1))

end PI.PhiCubeOfFactor
end
end

section -- merged from Formalism.PeriodIntegrals.CubicExponentialFactor
noncomputable section

open Classical

namespace PI.CubicExponentialFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq l ex E : PowerSeries ℂ_[p])
    (T : MvPowerSeries (Fin 3) ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    T * eAt E (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 * eAt E (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 *
        eAt E (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 =
      eAt wq (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) * eAt wq (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) *
        eAt wq (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) *
        (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * eAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2))) *
        (sub l ex (Xv 0) (Xv 1) * eAt E (sub l ex (Xv 0) (Xv 1))) *
        (sub l ex (Xv 1) (Xv 2) * eAt E (sub l ex (Xv 1) (Xv 2))) *
        (sub l ex (Xv 2) (Xv 0) * eAt E (sub l ex (Xv 2) (Xv 0))) →
    (∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T = add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * sub l ex (Xv 0) (Xv 1) * sub l ex (Xv 1) (Xv 2) *
        sub l ex (Xv 2) (Xv 0) * n) →
    Simeq (phAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt E (sub l ex (Xv 0) (Xv 1)) +
        phAt E (sub l ex (Xv 1) (Xv 2)) + phAt E (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt E (Xv 0) + phAt E (Xv 1) + phAt E (Xv 2)))

end PI.CubicExponentialFactor
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CcPrEq
noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem cc_pr_eq {x y : MvPowerSeries (Fin 3) ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (pr x y f) = MvPowerSeries.constantCoeff f := by
  unfold pr
  have hz : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := fun i => by fin_cases i <;> simpa
  have ha : MvPowerSeries.HasSubst ![x, y] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow]
      fin_cases s <;> simp [hx, hy] <;> exact hs

theorem main : Lemma := by
  intro p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hadd
  obtain ⟨S, hS⟩ := PI.AddIntG.Wk.exists_intS p
  have hS1 : W.a₁ ∈ S := (hS _).2 h1
  have hS2 : W.a₂ ∈ S := (hS _).2 h2
  have hS3 : W.a₃ ∈ S := (hS _).2 h3
  have hS4 : W.a₄ ∈ S := (hS _).2 h4
  have hS6 : W.a₆ ∈ S := (hS _).2 h6
  have hint : ∀ {σ : Type} (F : MvPowerSeries σ ℂ_[p]), IntegralMv F ↔ F ∈ SerS S σ := fun F => by
    rw [mem_SerS]
    exact forall_congr' fun e => (hS _).symm
  have hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := (hint _).1 hadd
  have hwq := PI.AddIntG.Wk.wq_mem hS1 hS2 hS3 hS4 hS6 hW
  obtain ⟨μ, hμS, hμ⟩ := mu_exists hwq
  obtain ⟨m, hmS, hm1, hmμ⟩ := m_exists hS1 hS2 hS3 hS4 hS6 hW hμS hμ
  obtain ⟨u1, hu1S, hu11, hu1⟩ := add_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  obtain ⟨u, huS, hu0, hu⟩ := sub_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  have hl0 := cc_flog W wq
  have hsub : ∀ i j : Fin 3, sub (flog W wq) ex (MvPowerSeries.X i) (MvPowerSeries.X j) =
      (MvPowerSeries.X i - MvPowerSeries.X j) * pr (MvPowerSeries.X i) (MvPowerSeries.X j) u := by
    intro i j
    have ha := hasSubst_pr (h0X (p := p) i) (h0X (p := p) j)
    rw [sub_pr hl0 (h0X i) (h0X j), hu]
    unfold pr
    rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_X ha]
    simp
  have hvS : ∀ i j : Fin 3, pr (MvPowerSeries.X i) (MvPowerSeries.X j) u ∈ SerS S (Fin 3) := fun i j =>
    pr_mem (h0X i) (h0X j) (X_mem_SerS' S i) (X_mem_SerS' S j) huS
  have hv1 : ∀ i j : Fin 3, MvPowerSeries.constantCoeff (pr (MvPowerSeries.X i) (MvPowerSeries.X j) u) = 1 :=
    fun i j => (cc_pr_eq (h0X i) (h0X j) u).trans hu0
  have hw1 : MvPowerSeries.constantCoeff (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u) = 1 := by
    rw [map_mul, map_mul, map_mul, hu11, hv1, hv1, hv1]
    norm_num
  have hwS : u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u * pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u *
      pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u ∈ SerS S (Fin 3) :=
    mul_mem (mul_mem (mul_mem hu1S (hvS 0 1)) (hvS 1 2)) (hvS 2 0)
  have hinv := MvPowerSeries.mul_inv_cancel (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)
    (by rw [hw1]; exact one_ne_zero)
  refine ⟨m * (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)⁻¹,
    (hint _).2 (mul_mem hmS (PI.AddIntG.Wk.inv_mem_SerS S hw1 hwS)), ?_, ?_⟩
  · rw [map_mul, MvPowerSeries.constantCoeff_inv, hw1, hm1, inv_one, mul_one]
  · rw [T_eq, hμ, hmμ, hu1, hsub 0 1, hsub 1 2, hsub 2 0]
    linear_combination (-((MvPowerSeries.X 2 - s3 W wq) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * m)) * hinv

end PI.FglTriFactor.Wk
end
end

theorem formal_group_tri_factor : PI.FglTriFactor.Lemma := PI.FglTriFactor.Wk.main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubicExponentialFactor.ExpMvAddC
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubicExponentialFactor.NormAddLeOne
noncomputable section

namespace PI.CubicExponentialFactor.Wk

open PI.CubicExponentialFactor

variable {p : ℕ} [Fact p.Prime]

theorem norm_add_le_one {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem trunc_mul {f g : PowerSeries ℂ_[p]} {k : ℕ} (hf : ∀ j < k, ‖PowerSeries.coeff j f‖ ≤ 1)
    (hg : ∀ j < k, ‖PowerSeries.coeff j g‖ ≤ 1) : ∀ j < k, ‖PowerSeries.coeff j (f * g)‖ ≤ 1 := by
  classical
  intro j hj
  rw [PowerSeries.coeff_mul]
  have key : ∀ s : Finset (ℕ × ℕ), (∀ q ∈ s, q.1 + q.2 = j) →
      ‖∑ q ∈ s, PowerSeries.coeff q.1 f * PowerSeries.coeff q.2 g‖ ≤ 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert q s hq ih =>
      intro hs
      rw [Finset.sum_insert hq]
      have hq' := hs q (Finset.mem_insert_self q s)
      refine norm_add_le_one ?_ (ih fun q' h' => hs q' (Finset.mem_insert_of_mem h'))
      rw [norm_mul]
      exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))
  exact key _ (fun q h => by simpa using h)

theorem term_int {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {m k : ℕ} (hm : 1 ≤ m) {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ m * F)‖ ≤ 1 := by
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (PowerSeries.X ^ m) F,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) (hF _ (by omega))
  · simp

theorem term_int1 {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {k : ℕ} {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * F)‖ ≤ 1 := by
  have h := term_int ha (m := 1) le_rfl hF
  rwa [pow_one] at h

theorem wq_int {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (ha1 : IsIntP W.a₁)
    (ha2 : IsIntP W.a₂) (ha3 : IsIntP W.a₃) (ha4 : IsIntP W.a₄) (ha6 : IsIntP W.a₆)
    (hW : IsWq W wq) : ∀ k, ‖PowerSeries.coeff k wq‖ ≤ 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h2 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 2)‖ ≤ 1 := by
      rw [pow_two]
      exact trunc_mul ih ih
    have h3 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 3)‖ ≤ 1 := by
      have e : wq ^ 3 = wq ^ 2 * wq := by ring
      rw [e]
      exact trunc_mul h2 ih
    dsimp only [IsWq] at hW
    rw [hW]
    simp only [map_add (f := _)]
    refine norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one
      (norm_add_le_one ?_ ?_) ?_) ?_) ?_) ?_
    · rw [PowerSeries.coeff_one]
      split_ifs <;> simp
    · exact term_int1 ha1 ih
    · exact term_int ha2 (by norm_num) ih
    · exact term_int ha3 (by norm_num) h2
    · exact term_int ha4 (by norm_num) h2
    · exact term_int ha6 (by norm_num) h3

end PI.CubicExponentialFactor.Wk

end
end

noncomputable section

namespace PI.CubicExponentialFactor.Wk

open PI.CubicExponentialFactor MvPowerSeries PI.FglShared

set_option linter.unusedSimpArgs false

variable {p : ℕ} [Fact p.Prime]

theorem logMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : logMv F = logS F := rfl

theorem expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := rfl

theorem expMv_addC {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
  exact PI.FglShared.expMv_add' hf hg

theorem main : Lemma := by
  intro p _ W wq l ex E T ha1 ha2 ha3 ha4 ha6 hW hex0 hinv hE0 hT ⟨n, hnI, hn1, hTn⟩
  classical

  set x0 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 0 with hx0
  set x1 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 1 with hx1
  set x2 : MvPowerSeries (Fin 3) ℂ_[p] := Xv 2 with hx2
  have hl0 : PowerSeries.constantCoeff l = 0 := PI.FglShared.l_constantCoeff hex0 hinv
  have hL0 : MvPowerSeries.constantCoeff (logS E) = 0 := PI.FglShared.constantCoeff_logS E
  have hXc : ∀ i : Fin 3, constantCoeff (Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    intro i
    simp [Xv]
  have hlg0 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (lg l a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hl0
  have hpt0 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (pt ex a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hex0
  have hadd0 : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      constantCoeff (add l ex a b) = 0 := by
    intro a b ha hb
    unfold add
    exact hpt0 _ (by rw [map_add (f := _), hlg0 a ha, hlg0 b hb, add_zero])
  have hsub0 : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      constantCoeff (sub l ex a b) = 0 := by
    intro a b ha hb
    unfold sub
    exact hpt0 _ (by rw [map_sub, hlg0 a ha, hlg0 b hb, sub_zero])
  have c0 : constantCoeff x0 = 0 := hXc 0
  have c1 : constantCoeff x1 = 0 := hXc 1
  have c2 : constantCoeff x2 = 0 := hXc 2
  set s := add l ex (add l ex x0 x1) x2 with hs
  set d1 := sub l ex x0 x1 with hd1
  set d2 := sub l ex x1 x2 with hd2
  set d3 := sub l ex x2 x0 with hd3
  have cs : constantCoeff s = 0 := hadd0 _ _ (hadd0 _ _ c0 c1) c2
  have cd1 : constantCoeff d1 = 0 := hsub0 _ _ c0 c1
  have cd2 : constantCoeff d2 = 0 := hsub0 _ _ c1 c2
  have cd3 : constantCoeff d3 = 0 := hsub0 _ _ c2 c0

  set ψ : MvPowerSeries (Fin 3) ℂ_[p] → MvPowerSeries (Fin 3) ℂ_[p] :=
    fun a => PowerSeries.subst a (logS E) with hψdef
  have hψ0 : ∀ a, constantCoeff a = 0 → constantCoeff (ψ a) = 0 :=
    fun a ha => PowerSeries.constantCoeff_subst_eq_zero ha _ hL0
  have hexpψ : ∀ a, constantCoeff a = 0 → expMv (ψ a) = eAt E a := by
    intro a ha
    rw [expMv_eq, PI.FglShared.expMv_subst' ha hL0, PI.FglShared.expMv_logS hE0]
    rfl
  have hφ : ∀ a, constantCoeff a = 0 → phAt E a = -ψ a := by
    intro a ha
    have hsa : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hsa, map_neg, PowerSeries.coe_substAlgHom hsa]

  set A := ψ s + ψ d1 + ψ d2 + ψ d3 with hA
  set B := ψ x0 + ψ x1 + ψ x2 with hB
  have cA : constantCoeff A = 0 := by
    simp only [hA, map_add (f := _), hψ0 _ cs, hψ0 _ cd1, hψ0 _ cd2, hψ0 _ cd3, add_zero]
  have cB : constantCoeff B = 0 := by
    simp only [hB, map_add (f := _), hψ0 _ c0, hψ0 _ c1, hψ0 _ c2, add_zero]
  have hFG : (phAt E s + phAt E d1 + phAt E d2 + phAt E d3) - 3 * (phAt E x0 + phAt E x1 + phAt E x2) =
      -A + (B + B + B) := by
    rw [hφ _ cs, hφ _ cd1, hφ _ cd2, hφ _ cd3, hφ _ c0, hφ _ c1, hφ _ c2]
    simp only [hA, hB]
    ring
  have cFG : constantCoeff (-A + (B + B + B)) = 0 := by
    simp only [map_add (f := _), map_neg, cA, cB, neg_zero, add_zero]
  set Z := expMv (-A + (B + B + B)) with hZdef
  have hexpA : expMv A = eAt E s * eAt E d1 * eAt E d2 * eAt E d3 := by
    have h1 : constantCoeff (ψ s + ψ d1) = 0 := by rw [map_add (f := _), hψ0 _ cs, hψ0 _ cd1, add_zero]
    have h2 : constantCoeff (ψ s + ψ d1 + ψ d2) = 0 := by rw [map_add (f := _), h1, hψ0 _ cd2, add_zero]
    rw [hA, expMv_addC h2 (hψ0 _ cd3), expMv_addC h1 (hψ0 _ cd2), expMv_addC (hψ0 _ cs) (hψ0 _ cd1),
      hexpψ _ cs, hexpψ _ cd1, hexpψ _ cd2, hexpψ _ cd3]
  have hexpB : expMv B = eAt E x0 * eAt E x1 * eAt E x2 := by
    have h1 : constantCoeff (ψ x0 + ψ x1) = 0 := by rw [map_add (f := _), hψ0 _ c0, hψ0 _ c1, add_zero]
    rw [hB, expMv_addC h1 (hψ0 _ c2), expMv_addC (hψ0 _ c0) (hψ0 _ c1), hexpψ _ c0, hexpψ _ c1,
      hexpψ _ c2]
  have hexp3B : expMv (B + B + B) = (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 := by
    have h1 : constantCoeff (B + B) = 0 := by rw [map_add (f := _), cB, add_zero]
    rw [expMv_addC h1 cB, expMv_addC cB cB, hexpB]
    ring
  have hZA : Z * (eAt E s * eAt E d1 * eAt E d2 * eAt E d3) = (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 := by
    rw [← hexpA, ← hexp3B, hZdef, ← expMv_addC cFG cA]
    congr 1
    ring

  obtain ⟨k, hk0, hkl⟩ := PI.FglShared.exists_coeff_ne hex0 hinv
  have hcoef : ∀ i j : Fin 3, MvPowerSeries.coeff (Finsupp.single i k)
      (lg l (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p])) = if i = j then PowerSeries.coeff k l else 0 := by
    intro i j
    unfold lg
    rw [PowerSeries.coeff_subst_single]
    by_cases hij : i = j
    · subst hij
      simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji, Finsupp.single_apply, hk0]
  have hne : ∀ (y : MvPowerSeries (Fin 3) ℂ_[p]) (i : Fin 3),
      MvPowerSeries.coeff (Finsupp.single i k) y = PowerSeries.coeff k l → y ≠ 0 := by
    intro y i hy h0
    rw [h0, map_zero] at hy
    exact hkl hy.symm
  have hlgadd : ∀ a b : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff b = 0 →
      lg l (add l ex a b) = lg l a + lg l b := by
    intro a b ha hb
    have hy : constantCoeff (lg l a + lg l b) = 0 := by rw [map_add (f := _), hlg0 a ha, hlg0 b hb, add_zero]
    unfold add pt lg
    exact PI.FglShared.subst_subst_eq hex0 hinv hy
  have hptne : ∀ y : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff y = 0 → y ≠ 0 → pt ex y ≠ 0 := by
    intro y hy0 hy
    unfold pt
    exact PI.FglShared.subst_ne_zero hex0 hinv hy0 hy
  have e0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x0) = PowerSeries.coeff k l := by
    have h := hcoef 0 0
    rw [if_pos rfl] at h
    exact h
  have e1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x1) = 0 := by
    have h := hcoef 0 1
    rw [if_neg (by decide)] at h
    exact h
  have e2 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) k) (lg l x2) = 0 := by
    have h := hcoef 0 2
    rw [if_neg (by decide)] at h
    exact h
  have f1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) k) (lg l x1) = PowerSeries.coeff k l := by
    have h := hcoef 1 1
    rw [if_pos rfl] at h
    exact h
  have f2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 3) k) (lg l x2) = 0 := by
    have h := hcoef 1 2
    rw [if_neg (by decide)] at h
    exact h
  have g2 : MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) k) (lg l x2) = PowerSeries.coeff k l := by
    have h := hcoef 2 2
    rw [if_pos rfl] at h
    exact h
  have g0 : MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) k) (lg l x0) = 0 := by
    have h := hcoef 2 0
    rw [if_neg (by decide)] at h
    exact h
  have hs0 : s ≠ 0 := by
    have hs' : s = pt ex (lg l x0 + lg l x1 + lg l x2) := by
      show pt ex (lg l (add l ex x0 x1) + lg l x2) = _
      rw [hlgadd x0 x1 c0 c1]
    rw [hs']
    refine hptne _ (by rw [map_add (f := _), map_add (f := _), hlg0 _ c0, hlg0 _ c1, hlg0 _ c2]; simp) (hne _ 0 ?_)
    rw [map_add (f := _), map_add (f := _), e0, e1, e2]
    simp
  have hd10 : d1 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c0, hlg0 _ c1, sub_zero]) (hne _ 0 ?_)
    rw [map_sub, e0, e1, sub_zero]
  have hd20 : d2 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c1, hlg0 _ c2, sub_zero]) (hne _ 1 ?_)
    rw [map_sub, f1, f2, sub_zero]
  have hd30 : d3 ≠ 0 := by
    refine hptne _ (by rw [map_sub, hlg0 _ c2, hlg0 _ c0, sub_zero]) (hne _ 2 ?_)
    rw [map_sub, g2, g0, sub_zero]
  have hE1 : ∀ a : MvPowerSeries (Fin 3) ℂ_[p], constantCoeff a = 0 → constantCoeff (eAt E a) = 1 := by
    intro a ha
    have hsa := PowerSeries.HasSubst.of_constantCoeff_zero ha
    have h1 : constantCoeff (PowerSeries.subst a (E - 1)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha _ (by rw [map_sub, hE0, map_one, sub_self])
    rw [← PowerSeries.coe_substAlgHom hsa, map_sub, map_one, map_sub, map_one, sub_eq_zero] at h1
    unfold eAt
    rw [← PowerSeries.coe_substAlgHom hsa]
    exact h1
  have hR : (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_pow, map_mul, map_mul, hE1 _ c0, hE1 _ c1, hE1 _ c2, map_zero] at this
    norm_num at this

  have hT' : s * d1 * d2 * d3 * n * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 =
      (eAt wq x0 * eAt wq x1 * eAt wq x2) * (s * d1 * d2 * d3) *
        (eAt E s * eAt E d1 * eAt E d2 * eAt E d3) := by
    rw [hTn] at hT
    linear_combination hT
  have hkey : (s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3) * (n * Z) =
      (s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3) * (eAt wq x0 * eAt wq x1 * eAt wq x2) := by
    linear_combination Z * hT' + ((eAt wq x0 * eAt wq x1 * eAt wq x2) * (s * d1 * d2 * d3)) * hZA
  have hQR : s * d1 * d2 * d3 * (eAt E x0 * eAt E x1 * eAt E x2) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hd10) hd20) hd30) hR
  have hnZ : n * Z = eAt wq x0 * eAt wq x1 * eAt wq x2 := mul_left_cancel₀ hQR hkey

  let Wr : Subring ℂ_[p] :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) =>
        show ‖a * b‖ ≤ 1 by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := show ‖(1 : ℂ_[p])‖ ≤ 1 by rw [norm_one]
      add_mem' := fun {a b} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) =>
        show ‖a + b‖ ≤ 1 from (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := show ‖(0 : ℂ_[p])‖ ≤ 1 by rw [norm_zero]; exact zero_le_one
      neg_mem' := fun {a} (ha : ‖a‖ ≤ 1) => show ‖-a‖ ≤ 1 by rw [norm_neg]; exact ha }
  let n' : MvPowerSeries (Fin 3) Wr := fun α => ⟨MvPowerSeries.coeff α n, hnI α⟩
  have hmap : MvPowerSeries.map Wr.subtype n' = n := by
    ext α
    rfl
  have hcn' : constantCoeff n' = 1 := by
    apply Subtype.ext
    have : Wr.subtype (constantCoeff n') = 1 := by
      rw [← MvPowerSeries.constantCoeff_map, hmap, hn1]
    exact this
  obtain ⟨u, hu⟩ : IsUnit n' := MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hcn']; exact isUnit_one)
  set v := MvPowerSeries.map Wr.subtype (↑u⁻¹ : MvPowerSeries (Fin 3) Wr) with hv
  have hnv : n * v = 1 := by
    rw [hv, ← hmap, ← hu, ← map_mul, Units.mul_inv, map_one]
  have hZP : Z = (eAt wq x0 * eAt wq x1 * eAt wq x2) * v := by
    calc Z = (n * v) * Z := by rw [hnv, one_mul]
      _ = (n * Z) * v := by ring
      _ = _ := by rw [hnZ]
  have hwqW : ∀ i : Fin 3, PI.FglPhSplit.Wk.AllIn Wr (eAt wq (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p])) := by
    intro i α
    unfold eAt
    rw [PowerSeries.coeff_subst_single]
    split_ifs
    · exact PI.CubicExponentialFactor.Wk.wq_int ha1 ha2 ha3 ha4 ha6 hW _
    · exact Wr.zero_mem
  have hvW : PI.FglPhSplit.Wk.AllIn Wr v := by
    intro α
    rw [hv, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff α (↑u⁻¹ : MvPowerSeries (Fin 3) Wr)).2
  have hZW : PI.FglPhSplit.Wk.AllIn Wr Z := by
    rw [hZP]
    exact PI.FglPhSplit.Wk.allIn_mul (PI.FglPhSplit.Wk.allIn_mul
      (PI.FglPhSplit.Wk.allIn_mul (hwqW 0) (hwqW 1)) (hwqW 2)) hvW
  unfold Simeq
  rw [hFG]
  exact ⟨cFG, fun α => hZW α⟩

end PI.CubicExponentialFactor.Wk

end
end

theorem thetaCube_triple_relation : PI.CubicExponentialFactor.Lemma := PI.CubicExponentialFactor.Wk.main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFactorIdentity.ExpMvEq
noncomputable section

namespace PI.PhiCubeOfFactor.Wk

open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared

variable {p : ℕ} [Fact p.Prime]

theorem logMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : logMv F = logS F := rfl

theorem expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := rfl

theorem main : Lemma := by
  intro p _ l ex E Q hex0 hinv hE1 hfun hQ
  obtain ⟨n, hnI, hn0, rfl⟩ := hQ
  have hl0 := l_constantCoeff hex0 hinv
  have hcX : ∀ i : Fin 2, constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => constantCoeff_X i
  have hlg : ∀ i : Fin 2, constantCoeff (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := by
    intro i
    unfold lg
    rw [constantCoeff_subst_of_zero (hcX i)]
    exact hl0
  have hs0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg l (Xv 1)) = 0 := by
    rw [map_add (f := _), hlg, hlg, add_zero]
  have hd0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) - lg l (Xv 1)) = 0 := by
    rw [map_sub, hlg, hlg, sub_zero]
  have hA0 : constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold add pt
    rw [constantCoeff_subst_of_zero hs0]
    exact hex0
  have hB0 : constantCoeff (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold sub pt
    rw [constantCoeff_subst_of_zero hd0]
    exact hex0
  obtain ⟨k, hk, hlk⟩ := exists_coeff_ne hex0 hinv
  have hc0 : ∀ i : Fin 2, coeff (Finsupp.single (0 : Fin 2) k) (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) =
      if i = 0 then PowerSeries.coeff k l else 0 := fun i => coeff_single_lg l 0 i hk
  have hAne : (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold add pt
    refine subst_ne_zero hex0 hinv hs0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_add (f := _), map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hBne : (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold sub pt
    refine subst_ne_zero hex0 hinv hd0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_sub, map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hcanc : eAt E (add l ex (Xv 0) (Xv 1)) * eAt E (sub l ex (Xv 0) (Xv 1)) =
      n * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hAne hBne)
    linear_combination hfun
  have hexp0 : PI.FglPhSplit.expMv (0 : PowerSeries ℂ_[p]) = 1 := by
    refine MvPowerSeries.ext fun α => ?_
    change (∑ m ∈ Finset.range ((α.sum fun _ k => k) + 1),
      MvPowerSeries.coeff α ((0 : PowerSeries ℂ_[p]) ^ m) / (m.factorial : ℂ_[p])) = MvPowerSeries.coeff α 1
    rw [Finset.sum_eq_single 0 (fun m _ hm => by rw [zero_pow hm, map_zero, zero_div])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
    simp
  have hL0 : constantCoeff (logS E) = 0 := constantCoeff_logS E
  have hnL0 : constantCoeff (-logS E) = 0 := by rw [map_neg, hL0, neg_zero]
  have hUE : PI.FglPhSplit.expMv (-logS E) * E = 1 := by
    have h := expMv_add' hnL0 hL0
    rw [neg_add_cancel, hexp0, expMv_logS hE1] at h
    exact h.symm
  have hsub : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (phAt E a) * eAt E a = 1 := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, expMv_subst' ha hnL0, ← PowerSeries.subst_mul hS, hUE, ← PowerSeries.coe_substAlgHom hS,
      map_one]
  have hneg : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (-phAt E a) = eAt E a := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hS, ← map_neg, neg_neg, PowerSeries.coe_substAlgHom hS,
      expMv_subst' ha hL0, expMv_logS hE1]
  have hph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (phAt E a) = 0 := by
    intro a ha
    unfold phAt
    rw [constantCoeff_subst_of_zero ha, logMv_eq]
    exact hnL0
  have hnph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (-phAt E a) = 0 := by
    intro a ha
    rw [map_neg, hph0 a ha, neg_zero]
  have hf : phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) -
      (2 * phAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + 2 * phAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) + -phAt E (Xv 0) + -phAt E (Xv 0) +
        -phAt E (Xv 1) + -phAt E (Xv 1) := by ring
  refine ⟨?_, ?_⟩
  · rw [hf, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hph0 _ hA0, hph0 _ hB0, hnph0 _ (hcX 0),
      hnph0 _ (hcX 1)]
    ring
  · rw [expMv_eq, hf]
    have c1 := hph0 _ hA0
    have c2 := hph0 _ hB0
    have c3 := hnph0 _ (hcX 0)
    have c4 := hnph0 _ (hcX 1)
    rw [expMv_add' (by simp only [map_add (f := _), c1, c2, c3, c4, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c3,
      expMv_add' (by simp only [map_add (f := _), c1, c2, add_zero]) c3,
      expMv_add' c1 c2, hneg _ (hcX 0), hneg _ (hcX 1)]
    refine int_of_mul_eq_one hnI hn0 ?_
    have e1 := hsub _ hA0
    have e2 := hsub _ hB0
    linear_combination (PI.FglPhSplit.expMv (phAt E (add l ex (Xv 0) (Xv 1))) *
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1)))) * hcanc.symm +
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1))) * eAt E (sub l ex (Xv 0) (Xv 1)) * e1 + e2

end PI.PhiCubeOfFactor.Wk

end
end

theorem phiCubeOfFactor : PI.PhiCubeOfFactor.Lemma := PI.PhiCubeOfFactor.Wk.main
end

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem lemma_three_one_third_holds : LemmaThreeOneThird := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact formal_group_tri_factor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem lemma_three_one_second_holds : UnitTraceSumSecondBound := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact fglChordFactor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem cube3OfDet_holds : Cube3OfDet := by
  intro p hp g hOk hE hQ hn
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact thetaCube_triple_relation p g.W g.wq g.l g.ex (ePhi1 g.lam g.abelian₂ g.C g.wq) _ h1 h2 h3 h4 h6 hW he0 hel hE hQ hn

theorem cube_second_of_determinant_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicFrobeniusStickelberger D) : cube3 D :=
  cube_second_identity_of_determinant lemma_three_one_third_holds cube3OfDet_holds D hQ (addInt_holds D)

theorem cube_first_of_addition_holds : CubeIdentityFromAdditionFormula := by
  intro p hp g hOk hE hId hn
  obtain ⟨_, hW, he0, hel⟩ := hOk
  exact phiCubeOfFactor p _ g.ex _ _ he0 hel hE hId hn

theorem cube_first_of_addition_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) : cube2 D :=
  addition_identity_of_sigma_formula lemma_three_one_second_holds cube_first_of_addition_holds D hQ (ePhiOne_holds D) (addInt_holds D)

theorem theorem_of_cube_of_addition_formulas (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) (hQd : PAdicFrobeniusStickelberger D) : cube D :=
  cube_of cube_of_two_identities_holds D (cube_first_of_addition_formula D hQ) (cube_second_of_determinant_formula D hQd)

end Formalism.MainNotions.Ext.CutA
