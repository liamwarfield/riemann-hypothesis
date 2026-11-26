module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.PtsMem

theorem inc_injective (D : D7) : Function.Injective (inc D) := by
  haveI : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField ℚ)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion ℚ) = 1 := congrArg (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ => x v) h
    exact zero_ne_one h2
  haveI : Nontrivial (AE D) := by
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight :
        IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AE D) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ D.host.E).injective
    exact hinj.nontrivial
  exact (inc D).injective

theorem sgA_inc (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem mem_GA (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) :
    g ∈ GA D N ↔ ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
      (g : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  have h1 : (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  change ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : Matrix (Fin N) (Fin N) (AE D)) =
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) ↔ _
  rw [h1, Matrix.mul_one]

theorem map_ct (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) :
    ((γ.map D.host.conj).transpose).map (inc D) = ((γ.map (inc D)).map (sgA D)).transpose := by
  ext i j
  simp [sgA_inc]

theorem unitary_of_isRat (D : D7) {N : ℕ} (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : γ * (γ.map D.host.conj).transpose = 1 := by
  have hg := (mem_GA D _).1 g.2
  unfold IsRat at h
  rw [h, ← map_ct, ← Matrix.map_mul] at hg
  rw [mul_eq_one_comm]
  apply Matrix.map_injective (inc_injective D)
  simp only
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_isRat (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : γ * (γ.map D.host.conj).transpose = 1) :
    ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ := by
  have h' : (γ.map D.host.conj).transpose * γ = 1 := mul_eq_one_comm.1 h
  have a : γ.map (inc D) * ((γ.map D.host.conj).transpose).map (inc D) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : ((γ.map D.host.conj).transpose).map (inc D) * γ.map (inc D) = 1 := by
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨⟨_, _, a, b⟩, (mem_GA D _).2 ?_⟩, rfl⟩
  change ((γ.map (inc D)).map (sgA D)).transpose * γ.map (inc D) = 1
  rw [← map_ct, b]

def ratSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {g | ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ}
  one_mem' := ⟨1, by
    unfold IsRat
    rw [Matrix.map_one _ (map_zero _) (map_one _)]; rfl⟩
  mul_mem' := by
    rintro a b ⟨γ, ha⟩ ⟨γ', hb⟩
    refine ⟨γ * γ', ?_⟩
    unfold IsRat at *
    rw [Matrix.map_mul, ← ha, ← hb]; rfl
  inv_mem' := by
    rintro a ⟨γ, ha⟩
    refine ⟨(γ.map D.host.conj).transpose, ?_⟩
    have hg := (mem_GA D _).1 a.2
    unfold IsRat at *
    rw [map_ct, ← ha]
    exact Units.inv_eq_of_mul_eq_one_left hg

def intSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {k | IntG D (k : GL (Fin N) (AE D))}
  one_mem' := by
    intro i j
    have : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact ⟨this, by simpa using this⟩
  mul_mem' := by
    intro a b ha hb i j
    constructor
    · rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (ha i l).1 (hb l j).1
    · rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hb i l).2 (ha l j).2
  inv_mem' := by
    intro a ha i j
    refine ⟨(ha i j).2, ?_⟩
    rw [Subgroup.coe_inv, inv_inv]
    exact (ha i j).1

end GlobalTheory.NormSum.PtsMem

open GlobalTheory.NormSum.PtsMem in
theorem GlobalTheory.NormSum.mem_ratG_intG : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  intro D N
  refine ⟨fun g => ?_, fun k => ?_, exists_isRat D, unitary_of_isRat D, inc_injective D⟩
  · have : ratG D N = ratSub D N := Subgroup.closure_eq (ratSub D N)
    rw [this]; rfl
  · have : intG D N = intSub D N := Subgroup.closure_eq (intSub D N)
    rw [this]; rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembershipStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_integralPoints_membership : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  first | exact @GlobalTheory.NormSum.mem_ratG_intG | exact GlobalTheory.NormSum.mem_ratG_intG | (intros; apply GlobalTheory.NormSum.mem_ratG_intG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDualStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCovolume_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  first | exact @GlobalTheory.PlaneLattice.area_pos_and_selfDual | exact GlobalTheory.PlaneLattice.area_pos_and_selfDual | (intros; apply GlobalTheory.PlaneLattice.area_pos_and_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.AdelicApprox

variable (D : D7)

theorem levelC_natCast (n : ℕ) : Formalism.UG.P.levelafC D.host.E (n : 𝓞 ℚ) = (n : AE D) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem exists_denom (x : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * x ∈ OhE D := by
  obtain ⟨d, hd, hx⟩ := Formalism.UG.P.levelaf_denom x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hd
  · rw [← levelC_natCast, ← hc, Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem c) hx

theorem exists_approx (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ r : D.host.E, ∃ w ∈ OhE D, s = inc D r + (n : AE D) * w := by
  rw [← levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨_, t, ht, h⟩

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
      D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [hspec] at hne
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)
  rw [FractionalIdeal.mem_coe]
  unfold Host.AA0
  rw [FractionalIdeal.mem_inv_iff hB]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) (t : AE D)
    (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  unfold IhE at ht
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, a, ha, u, hu, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * u, mul_mem hs hu, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem absNorm_mul_mem_IhE (cc : Ideal (𝓞 D.host.K)) (s : AE D) (hs : s ∈ OhE D) :
    (Ideal.absNorm cc : AE D) * s ∈ IhE D cc := by
  refine AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, 1, one_mem_inverse_halfDifferent D, s, hs, ?_⟩
  simp

theorem approx_mod_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ →
    (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc,
      inc D e - y = (m : AE D) * t) ∧
    (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧
    (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  intro D cc hcc
  refine ⟨fun y m hm => ?_, exists_denom D, mul_mem_IhE D cc⟩
  obtain ⟨k, hk, hy⟩ := exists_denom D y
  have hn : 0 < Ideal.absNorm cc :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨r, w, hw, h⟩ := exists_approx D (k * m * Ideal.absNorm cc)
    (Nat.mul_pos (Nat.mul_pos hk hm) hn) _ hy
  refine ⟨(k : D.host.E)⁻¹ * r, _, absNorm_mul_mem_IhE D cc (-w) (neg_mem hw), ?_⟩
  have hu : inc D (k : D.host.E)⁻¹ * (k : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hk.ne'), map_one]
  rw [map_mul]
  push_cast at h
  linear_combination (-inc D (k : D.host.E)⁻¹) * h +
    (y - (m : AE D) * (Ideal.absNorm cc : AE D) * w) * hu

end GlobalTheory.AdelicApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdealStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc, inc D e - y = (m : AE D) * t) ∧ (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧ (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  first | exact @GlobalTheory.AdelicApprox.approx_mod_ideal | exact GlobalTheory.AdelicApprox.approx_mod_ideal | (intros; apply GlobalTheory.AdelicApprox.approx_mod_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
open Filter Topology

namespace GlobalTheory.ConjSeries

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem hasDerivAt_prod_pow_line (α : σ →₀ ℕ) (z : σ → ℂ) (i : σ) :
    HasDerivAt (fun t : ℂ => ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
      ((α i : ℂ) * z i ^ (α i - 1) * ∏ j ∈ Finset.univ.erase i, z j ^ α j) 0 := by
  have h : (fun t : ℂ => ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j) =
      fun t : ℂ => (z i + t) ^ α i * ∏ j ∈ Finset.univ.erase i, z j ^ α j := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h]
  have h2 := (((hasDerivAt_id (0 : ℂ)).const_add (z i)).fun_pow (α i)).mul_const
    (∏ j ∈ Finset.univ.erase i, z j ^ α j)
  simpa using h2

theorem hasSum_fderiv_series {f : (σ → ℂ) → ℂ} {c : (σ →₀ ℕ) → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : ∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) (f z)) (i : σ) :
    ∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ =>
      (c (α + Finsupp.single i 1) * ((α i : ℂ) + 1)) * ∏ j, z j ^ α j)
      (fderiv ℂ f z (Pi.single i 1)) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsum : Summable fun α : σ →₀ ℕ => ‖c α‖ * ∏ j, s ^ α j := by
    have h1 := (hball (fun _ => (s : ℂ)) (by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
      intro j
      rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]; linarith)).summable.norm
    simpa [norm_prod, abs_of_pos hs0] using h1
  filter_upwards [hf.eventually_analyticAt, Metric.ball_mem_nhds (0 : σ → ℂ) (half_pos hs0)]
    with z hz hzb
  rw [mem_ball_zero_iff] at hzb
  have hn : ∀ t ∈ Metric.ball (0 : ℂ) (s / 2), ‖z + t • (Pi.single i 1 : σ → ℂ)‖ < s := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    calc _ ≤ ‖z‖ + ‖t • (Pi.single i 1 : σ → ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖t‖ := by rw [norm_smul, Pi.norm_single, norm_one, mul_one]
      _ < s := by linarith
  have h1 := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) (s / 2))
    (F := fun (α : σ →₀ ℕ) (t : ℂ) => c α * ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
    hsum (fun α => by
      apply Differentiable.differentiableOn
      simp only [Pi.add_apply, Pi.smul_apply]
      fun_prop) Metric.isOpen_ball (fun α t ht => by
      rw [norm_mul, norm_prod]
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_)
        (norm_nonneg _)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm _ j).trans (hn t ht).le) _)
    (Metric.mem_ball_self (half_pos hs0))
  have h2 : (fun t : ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
      =ᶠ[𝓝 0] fun t : ℂ => f (z + t • (Pi.single i 1 : σ → ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hs0)] with t ht
    exact (hball _ (by rw [mem_ball_zero_iff]; linarith [hn t ht])).tsum_eq
  rw [h2.deriv_eq] at h1
  have h3 : deriv (fun t : ℂ => f (z + t • (Pi.single i 1 : σ → ℂ))) 0 =
      fderiv ℂ f z (Pi.single i 1) := hz.differentiableAt.lineDeriv_eq_fderiv
  rw [h3] at h1
  have h5 : HasSum (fun α : σ →₀ ℕ => c α *
      ((α i : ℂ) * z i ^ (α i - 1) * ∏ j ∈ Finset.univ.erase i, z j ^ α j))
      (fderiv ℂ f z (Pi.single i 1)) := by
    refine (congrArg (HasSum · _) (funext fun α => ?_)).mp h1
    exact ((hasDerivAt_prod_pow_line α z i).const_mul (c α)).deriv
  have hinj : Function.Injective fun α : σ →₀ ℕ => α + Finsupp.single i 1 :=
    add_left_injective _
  rw [← hinj.hasSum_iff] at h5
  · convert h5 using 2 with α
    simp only [Function.comp]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have : ∏ j ∈ Finset.univ.erase i, z j ^ (α + Finsupp.single i 1 : σ →₀ ℕ) j =
        ∏ j ∈ Finset.univ.erase i, z j ^ α j :=
      Finset.prod_congr rfl fun j hj => by
        simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this]
    simp
    ring
  · intro α hα
    have : α i = 0 := by
      by_contra h0
      have hle : Finsupp.single i 1 ≤ α := by
        rw [Finsupp.single_le_iff]; omega
      obtain ⟨m', rfl⟩ := exists_add_of_le hle
      exact hα ⟨m', add_comm _ _⟩
    simp [this]

theorem coeff_taylor_of_hasSum (n : ℕ) :
    ∀ {f : (σ → ℂ) → ℂ} {c : (σ →₀ ℕ) → ℂ}, AnalyticAt ℂ f 0 →
    (∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) (f z)) →
    ∀ m : σ →₀ ℕ, m.degree < n → MvPowerSeries.coeff m (GlobalTheory.taylor f) = c m := by
  induction n with
  | zero => intro f c _ _ m hm; omega
  | succ n ih =>
    intro f c hf h m hm
    by_cases h0 : m = 0
    · subst h0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_taylor]
      have h1 := h.self_of_nhds
      have h2 : HasSum (fun α : σ →₀ ℕ => c α * ∏ j, (0 : σ → ℂ) j ^ α j)
          (c 0 * ∏ j, (0 : σ → ℂ) j ^ (0 : σ →₀ ℕ) j) := by
        refine hasSum_single 0 fun α hα => ?_
        obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by simpa using Finsupp.ne_iff.1 hα
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
      simpa using h1.unique h2
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h0
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    have h1 := ih (analyticAt_fderiv_apply hf (Pi.single i 1)) (hasSum_fderiv_series hf h i) m' (by
      rw [map_add (f := _), Finsupp.degree_single] at hm; omega)
    rw [taylor_fderiv hf, MvPowerSeries.coeff_pderiv] at h1
    have h4 : ((m' i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' i)
    rw [add_comm]
    exact mul_right_cancel₀ h4 h1

omit [DecidableEq σ] in
theorem eventually_summable_of_ne_zero {c : (σ →₀ ℕ) → ℂ}
    (hf : Continuous fun z : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j)
    (h0 : (fun z : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j) ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : σ → ℂ), Summable (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) := by
  have hd : Dense (Set.pi Set.univ fun _ : σ => ({0}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun _ _ => dense_compl_singleton 0
  obtain ⟨w, hw, hw0⟩ := hd.inter_open_nonempty _ (isOpen_ne_fun hf continuous_zero)
    (Function.ne_iff.1 h0)
  have hs : Summable (fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j) := by
    by_contra hs
    exact hw (tsum_eq_zero_of_not_summable hs)
  have hev : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ j, ‖z j‖ < ‖w j‖ := by
    refine eventually_all.2 fun j => ?_
    refine (continuous_apply j).norm.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hw0 j (Set.mem_univ j)
  filter_upwards [hev] with z hz
  refine Summable.of_norm_bounded hs.norm fun α => ?_
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_)
    (norm_nonneg _)
  rw [norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz j).le _

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem taylor_eq_coeff (D : D7) {N N' : ℕ} (F : VC D N N' → ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D F α = MvPowerSeries.coeff α (taylorDir (coordV D) F) := by
  rw [coeff_taylorDir, dirPolyDeriv_monomial_one, Formalism.MainNotions.TaylorLogMetric.taylor,
    Finsupp.prod_fintype _ _ (by simp), Nat.cast_prod, div_eq_inv_mul]
  rfl

theorem taylor_tsum (D : D7) {N N' : ℕ} (c : Mono D N N' → ℂ)
    (hd : Differentiable ℂ fun z : VC D N N' => ∑' α, c α * mono D α z)
    (h0 : (fun z : VC D N N' => ∑' α, c α * mono D α z) ≠ 0) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => ∑' α, c α * mono D α z) α = c α := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, coordV, Pi.single_apply]
  have hm : ∀ (β : Mono D N N') z, mono D β (L z) = ∏ j, z j ^ β j := fun β z => by
    rw [mono, Finsupp.prod_fintype _ _ (by simp)]
    rfl
  have han : AnalyticAt ℂ (fun z : VC D N N' => ∑' α, c α * mono D α z) 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hd)
  rw [taylor_eq_coeff, hc, ← taylor_comp_clm L han]
  have han' : AnalyticAt ℂ (fun z => ∑' α, c α * mono D α (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  have hcont : Continuous (fun z => ∑' α, c α * mono D α (L z)) :=
    hd.continuous.comp L.continuous
  have hne : (fun z => ∑' α, c α * mono D α (L z)) ≠ 0 := by
    intro h
    refine h0 (funext fun w => ?_)
    exact congrFun h fun k => w k.1 k.2.1 k.2.2
  simp only [hm] at han' hcont hne ⊢
  refine coeff_taylor_of_hasSum _ han' ?_ α (Nat.lt_succ_self _)
  filter_upwards [eventually_summable_of_ne_zero hcont hne] with z hz
  exact hz.hasSum

theorem coeff_minorPol_int (D : D7) {N N' : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D N N' n)
    (α : Mono D N N') : ∃ k : ℤ, AddMonoidAlgebra.coeff (minorPol D T) α = k := by
  have h : minorPol D T = MvPolynomial.map (Int.castRingHom ℂ)
      (∏ τ, ∏ j, (Matrix.of fun i i' : Fin N =>
        (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D N N') ℤ)).det) := by
    simp only [minorPol, map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext i i' : 2
    simp
  exact ⟨_, by rw [h, MvPolynomial.coeff_map]; rfl⟩

theorem taylor_fnConj : ∀ (D : D7) (N N' : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ), Differentiable ℂ (fnConj D M ρ G) → fnConj D M ρ G ≠ 0 → (∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (fnConj D M ρ G) α = cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D G α)) ∧ (CoefIn D G M → ∀ (n : D.what₂.Tau → ℕ) (T : Tup D N N' n), GL3Theta.applyAt0 D (minorPol D T) G ∈ M ∧ cj M ρ (GL3Theta.applyAt0 D (minorPol D T) G) = GL3Theta.applyAt0 D (minorPol D T) (fnConj D M ρ G)) := by
  intro D N N' M ρ G hd h0
  have h1 : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (fnConj D M ρ G) α = cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D G α) :=
    fun α => taylor_tsum D _ hd h0 α
  refine ⟨h1, fun hG n T => ?_⟩
  choose k hk using coeff_minorPol_int D T
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  let x : M := ∑ α ∈ (minorPol D T).support,
    (k α : M) * ((α.prod fun _ n => n.factorial : ℕ) : M) * ⟨_, hG α⟩
  have hx : GL3Theta.applyAt0 D (minorPol D T) G = x := by
    simp [GL3Theta.applyAt0, x, hk, Finsupp.prod]
  rw [hx, hcj]
  refine ⟨x.2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GL3Theta.applyAt0, x, hk, h1, map_sum, map_mul, map_intCast, map_natCast]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← hcj]
  simp [Finsupp.prod]

end GlobalTheory.ConjSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorCoeff_conjugateSeries : ∀ (D : D7) (N N' : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ), Differentiable ℂ (fnConj D M ρ G) → fnConj D M ρ G ≠ 0 → (∀ α, taylor D (fnConj D M ρ G) α = cj M ρ (taylor D G α)) ∧ (CoefIn D G M → ∀ (n : D.what₂.Tau → ℕ) (T : Tup D N N' n), GL3Theta.applyAt0 D (minorPol D T) G ∈ M ∧ cj M ρ (GL3Theta.applyAt0 D (minorPol D T) G) = GL3Theta.applyAt0 D (minorPol D T) (fnConj D M ρ G)) := by
  first | exact @GlobalTheory.ConjSeries.taylor_fnConj | exact GlobalTheory.ConjSeries.taylor_fnConj | (intros; apply GlobalTheory.ConjSeries.taylor_fnConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Complex
open scoped BigOperators ComplexConjugate Real

noncomputable section

namespace GlobalTheory.UnitaryTheta

section General

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsPosHerm (H : Sesq V) : Prop :=
  (∀ z w, H z w = conj (H w z)) ∧ ∀ z, z ≠ 0 → 0 < (H z z).re

def Heisenberg₂ (H : Sesq V) (x : V) (G : V → ℂ) : V → ℂ :=
  fun z => G (z + x) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2)

def kerTerm (H : Sesq V) (x w z : V) : ℂ :=
  cexp ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2)

def kerSum (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (z : V) : V → ℂ :=
  fun w => ∑' x : Λ, α x * kerTerm H x w z

def IsSemichar (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) : Prop :=
  (∀ x ∈ Λ, α x = 1 ∨ α x = -1) ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, (H x y).im = m) ∧
    ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * cexp (-((π : ℂ) * I) * ((H x y).im : ℂ))

end General

def formV (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (fun z z' w => by simp [Hf, add_mul, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_assoc, mul_div_assoc'])
    (fun z w w' => by simp [Hf, mul_add, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_left_comm, mul_div_assoc'])

theorem _root_.GlobalTheory.UnitaryTheta.isPosHerm_formV (D : _root_.Formalism.BasicNotions.D7) (T : _root_.Formalism.MainNotions.TaylorLogMetric.Tor D)
    (N N' : ℕ) (h : 0 < _root_.Formalism.MainNotions.TaylorLogMetric.area T.abelian₂) :
    _root_.GlobalTheory.UnitaryTheta.IsPosHerm (_root_.GlobalTheory.UnitaryTheta.formV D T N N') := by
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [_root_.GlobalTheory.UnitaryTheta.formV, LinearMap.mk₂'ₛₗ_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, map_div₀, map_sum, map_mul,
      Complex.conj_conj, Complex.conj_ofReal]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have hsum : ∀ τ i j, z τ i j * conj (z τ i j) = ((Complex.normSq (z τ i j) : ℝ) : ℂ) :=
      fun τ i j => Complex.mul_conj _
    simp only [_root_.GlobalTheory.UnitaryTheta.formV, LinearMap.mk₂'ₛₗ_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, hsum]
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
    refine div_pos ?_ h
    obtain ⟨τ, i, j, hz⟩ : ∃ τ i j, z τ i j ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz (funext fun τ => funext fun i => funext fun j => hne τ i j)
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨τ, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 hz⟩

end GlobalTheory.UnitaryTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem Hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_smul_left (c : ℂ) (x y : VC D N N') : Hf D T (c • x) y = c * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_conj (x y : VC D N N') : (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem Hf_smul_right (c : ℂ) (x y : VC D N N') : Hf D T x (c • y) = (starRingEnd ℂ) c * Hf D T x y := by
  rw [← Hf_conj D T (c • y) x, Hf_smul_left, map_mul, Hf_conj]

theorem Hf_zero_right (y : VC D N N') : Hf D T y 0 = 0 := by simp [Hf]

theorem Hf_nsmul_left (n : ℕ) (x y : VC D N N') : Hf D T (n • x) y = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

theorem Hf_nsmul_right (n : ℕ) (x y : VC D N N') : Hf D T x (n • y) = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_right, Complex.conj_natCast]

theorem Hf_im_swap (x y : VC D N N') : (Hf D T y x).im = -(Hf D T x y).im := by
  rw [← Hf_conj D T x y, Complex.conj_im]

theorem Hf_re_swap (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  rw [← Hf_conj D T x y, Complex.conj_re]

theorem U_zero (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf_zero_right]

theorem U_U (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) * U D T (x + y) G z := by
  have h : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← Hf_conj D T x y]
    apply Complex.ext <;> simp
    ring
  simp only [U, Hf_add_left, Hf_add_right, add_assoc]
  rw [h, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem U_mul (x : VC D N N') (a : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => a * G w) z = a * U D T x G z := by
  simp only [U, mul_assoc]

theorem U_sum {ι : Type*} (s : Finset ι) (x : VC D N N') (G : ι → VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => ∑ i ∈ s, G i w) z = ∑ i ∈ s, U D T x (G i) z := by
  simp only [U, Finset.sum_mul]

theorem differentiable_Hf (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem differentiable_U (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have h := differentiable_Hf D T x
  unfold U
  fun_prop

theorem differentiable_comb {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (comb D T c t G) := by
  have h := fun i => differentiable_U D T (t i) hG
  unfold comb
  fun_prop

def pad (m : ℕ) (z : VC D N N') : VC D (N + m) N' := fun τ a => Fin.append (z τ a) (0 : Fin m → ℂ)

def padM (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) : Matrix (Fin N') (Fin (N + m)) D.host.E :=
  fun a => Fin.append (A a) (0 : Fin m → D.host.E)

@[simp] theorem pad_left (m : ℕ) (z : VC D N N') (τ a) (i : Fin N) : pad D m z τ a (Fin.castAdd m i) = z τ a i := by
  simp [pad]

@[simp] theorem pad_right (m : ℕ) (z : VC D N N') (τ a) (i : Fin m) : pad D m z τ a (Fin.natAdd N i) = 0 := by
  simp [pad]

def padL (m : ℕ) : VC D N N' →ₗ[ℂ] VC D (N + m) N' where
  toFun := pad D m
  map_add' x y := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem padL_apply (m : ℕ) (z : VC D N N') : padL D m z = pad D m z := rfl

theorem pad_add (m : ℕ) (x y : VC D N N') : pad D m (x + y) = pad D m x + pad D m y := (padL D m).map_add x y

theorem pad_smul (m : ℕ) (c : ℂ) (x : VC D N N') : pad D m (c • x) = c • pad D m x := (padL D m).map_smul c x

theorem pad_nsmul (m n : ℕ) (x : VC D N N') : pad D m (n • x) = n • pad D m x := map_nsmul (padL D m) n x

theorem pad_zero (m : ℕ) : pad D m (0 : VC D N N') = 0 := (padL D m).map_zero

theorem pad_sum {ι : Type*} (s : Finset ι) (m : ℕ) (x : ι → VC D N N') :
    pad D m (∑ i ∈ s, x i) = ∑ i ∈ s, pad D m (x i) := map_sum (padL D m) x s

theorem differentiable_pad (m : ℕ) : Differentiable ℂ (pad D m : VC D N N' → VC D (N + m) N') :=
  (LinearMap.toContinuousLinearMap (padL D m)).differentiable

theorem pad_embV (h0 : ∀ τ, T.emb τ 0 = 0) (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    pad D m (embV D T A) = embV D T (padM D m A) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [embV, padM, h0]

theorem Hf_pad (m : ℕ) (x y : VC D N N') : Hf D T (pad D m x) (pad D m y) = Hf D T x y := by
  simp [Hf, Fin.sum_univ_add]

theorem U_pad (m : ℕ) (x : VC D N N') (G : VC D (N + m) N' → ℂ) :
    U D T x (fun z => G (pad D m z)) = fun z => U D T (pad D m x) G (pad D m z) := by
  funext z
  simp only [U, Hf_pad, pad_add]

theorem wdPh_pad (m : ℕ) (x : VC D N N') : wdPh D T (pad D m x) = wdPh D T x := by
  simp only [wdPh, qH, Hf_pad]

theorem comb_pad (m : ℕ) {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') (G : VC D (N + m) N' → ℂ) :
    comb D T c t (fun z => G (pad D m z)) = fun z => comb D T c (fun i => pad D m (t i)) G (pad D m z) := by
  funext z
  simp only [comb, U_pad]

def IsTr (A : AddSubgroup (VC D N N')) (F G : VC D N N' → ℂ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (m : ℕ), 0 < m ∧ (∀ i, m • t i ∈ A) ∧ G = comb D T c t F

theorem IsTr.trans {A : AddSubgroup (VC D N N')} {F G H : VC D N N' → ℂ} (h₁ : IsTr D T A F G)
    (h₂ : IsTr D T A G H) : IsTr D T A F H := by
  obtain ⟨k, c, t, m, hm, ht, rfl⟩ := h₁
  obtain ⟨k', c', t', m', hm', ht', rfl⟩ := h₂
  refine ⟨k' * k, fun p => c' (finProdFinEquiv.symm p).1 * c (finProdFinEquiv.symm p).2 *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        ((Hf D T (t' (finProdFinEquiv.symm p).1) (t (finProdFinEquiv.symm p).2)).im : ℂ)),
    fun p => t' (finProdFinEquiv.symm p).1 + t (finProdFinEquiv.symm p).2, m * m', Nat.mul_pos hm hm', ?_, ?_⟩
  · intro p
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_smul]; exact A.nsmul_mem (ht' _) _
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem (ht _) _
  · funext z
    have h : ∀ i, U D T (t' i) (comb D T c t F) z = ∑ j, c j * U D T (t' i) (U D T (t j) F) z := by
      intro i
      have := U_sum D T Finset.univ (t' i) (fun j w => c j * U D T (t j) F w) z
      simp only [U_mul] at this
      exact this
    have e : comb D T c' t' (comb D T c t F) z = ∑ i, c' i * U D T (t' i) (comb D T c t F) z := rfl
    rw [e]
    simp only [h, U_U]
    unfold comb
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem IsTr.single {A : AddSubgroup (VC D N N')} (F : VC D N N' → ℂ) (a : ℂ) (t : VC D N N') (m : ℕ)
    (hm : 0 < m) (ht : m • t ∈ A) : IsTr D T A F (fun z => a * U D T t F z) :=
  ⟨1, fun _ => a, fun _ => t, m, hm, fun _ => ht, by funext z; simp [comb]⟩

theorem IsTr.pad {A : AddSubgroup (VC D N N')} {m : ℕ} {B : AddSubgroup (VC D (N + m) N')} {R : ℕ} (hR : 0 < R)
    (hAB : ∀ y ∈ A, R • pad D m y ∈ B) {F : VC D (N + m) N' → ℂ} {G : VC D N N' → ℂ}
    (h : IsTr D T A (fun z => F (pad D m z)) G) :
    ∃ G₁, IsTr D T B F G₁ ∧ G = fun z => G₁ (pad D m z) := by
  obtain ⟨k, c, t, n, hn, ht, rfl⟩ := h
  refine ⟨_, ⟨k, c, fun i => GalTheta.pad D m (t i), R * n, Nat.mul_pos hR hn, fun i => ?_, rfl⟩, comb_pad D T m c t F⟩
  rw [mul_smul, ← pad_nsmul]
  exact hAB _ (ht i)

end GlobalTheory.GalTheta
end
end
