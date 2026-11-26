module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ChiUnit

open GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

theorem norm_integer_le {E K : Type} [Field E] [NumberField E] [NormedField K] [IsUltrametricDist K] (ψ : E →+* K) (r : 𝓞 E) :
    ‖ψ r‖ ≤ 1 := by
  have h : IsIntegral ℤ (ψ r) := (r.isIntegral_coe).map ψ.toIntAlgHom
  by_contra H
  push Not at H
  obtain ⟨f, hf, e⟩ := h
  rw [hf.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at e
  have e2 := congrArg norm (eq_neg_of_add_eq_zero_left e)
  rw [norm_neg, norm_pow] at e2
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · simp [h0] at e2
  · have := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.range f.natDegree)
      (f := fun i => Polynomial.eval₂ (algebraMap ℤ K) (ψ r) (Polynomial.C (f.coeff i) * Polynomial.X ^ i))
      (C := ‖ψ r‖ ^ (f.natDegree - 1)) (by positivity) (fun i hi => by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
        have h1 : ‖algebraMap ℤ K (f.coeff i)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        have h2 : ‖ψ r‖ ^ i ≤ ‖ψ r‖ ^ (f.natDegree - 1) :=
          pow_le_pow_right₀ H.le (by have := Finset.mem_range.1 hi; omega)
        calc _ ≤ 1 * _ := mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = _ := one_mul _)
    rw [← e2] at this
    exact absurd this (not_le.2 (pow_lt_pow_right₀ H (by omega)))

theorem exists_prime_under {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) :
    ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal ∧ ∀ r : 𝓞 E, r ∉ P.asIdeal → ‖ψ r‖ = 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ‖ψ r‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖ψ ((a + b : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by
        show ‖ψ ((0 : 𝓞 E) : E)‖ < 1
        simp
      smul_mem' := fun c a ha => by
        show ‖ψ ((c * a : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_integer_le ψ c)).trans_lt ha }
  have hI : ∀ r, r ∈ I ↔ ‖ψ r‖ < 1 := fun _ => Iff.rfl
  have h1 : ∀ r, r ∉ I → ‖ψ r‖ = 1 := fun r hr =>
    le_antisymm (norm_integer_le ψ r) (not_lt.1 hr)
  have hp : (p : 𝓞 E) ∈ I := by
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
      norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨⟨I, ⟨?_, fun {a b} hab => ?_⟩, ?_⟩, hp, h1⟩
  · rw [Ideal.ne_top_iff_one, hI]
    simp
  · by_contra H
    push Not at H
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at hab
    have ha := h1 a H.1
    have hb := h1 b H.2
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb
    rw [ha, hb] at hab
    simp at hab
  · intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem norm_eq_one_of_val {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) {y : E}
    (hy : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → P.valuation E y = 1) : ‖ψ y‖ = 1 := by
  obtain ⟨P, hP, h1⟩ := exists_prime_under ψ
  have key : ∀ x : E, IntAt P x → ‖ψ x‖ ≤ 1 := by
    rintro x ⟨r, s, hs, e⟩
    have := congrArg (fun z => ‖ψ z‖) e
    have h2 := h1 s hs
    rw [RingOfIntegers.coe_eq_algebraMap] at h2
    simp only [map_mul, norm_mul, h2, one_mul] at this
    rw [this]
    exact norm_integer_le ψ r
  have hv := hy P hP
  have h0 : y ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨a, b⟩ := (GlobalTheory.CharValCompare.val_eq_one_iff h0).1 hv
  have hb := key _ b
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 (by simpa using h0))] at hb
  exact le_antisymm (key _ a) hb

variable {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ}

theorem symm_conj (hs : s.Ok) (x : D.host.E) : s.iE.symm (D.host.conj x) = star (s.iE.symm x) := by
  apply s.iE.injective
  rw [hs.2, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem normOne_idTo (hs : s.Ok) {I J : Submodule (𝓞 X.E) X.E} (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    TaylorLogMetric.N1 D (idTo s I) := by
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.IdealTransport.transport D X s
  exact ⟨idTo s J, fun x => by rw [t1, t1, h1, symm_conj hs], by rw [← t2, h2, t3]⟩

theorem chi_span (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {y : X.E} (hy : star y * y = 1) :
    χ (idTo s (Submodule.span (𝓞 X.E) {y})) = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.IdealTransport.transport D X s
  letI := D.host.cmStar
  have hst : star (s.iE y) = s.iE (star y) := by
    apply D.host.φ₀.injective
    rw [hs.2]
    change D.host.φ₀ (@NumberField.IsCMField.complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ (s.iE y)) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hu : s.iE y ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, mul_comm (s.iE y), and_self, hst, ← map_mul, hy, map_one]
  have := hχ.2 ⟨_, hu⟩
  rw [t4, this, ← s.iT.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs.1]

theorem chi_pow (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {I J : Submodule (𝓞 X.E) X.E}
    (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    ∃ (h : ℕ) (y : X.E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 X.E) {y} = I ^ h ∧
      χ (idTo s I) ^ h = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  obtain ⟨-, t2, -⟩ := GlobalTheory.IdealTransport.transport D X s
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (idTo s (I ^ n)) := fun n => normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (idTo s (I ^ n)) = χ (idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (normOne_idTo hs h1 h2), ih]
  exact ⟨h, y, hh, hy, hyI, by rw [← chi_span hs hχ hy, hyI, hp]⟩

theorem map_mem_Qbar {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) (x : E) : φ x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

theorem chi_det_unit : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ϖ : 𝓞 X.E) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → s.Ok → TaylorLogMetric.IsChi D χ → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt X.E n P) → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)))‖ = 1 := by
  intro D X s χ p _ lam ϖ n N _ hs hχ hϖ hN hS
  obtain ⟨-, -, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  rw [t6]
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  obtain ⟨h, y, hh, hy, hyI, e⟩ := chi_pow hs hχ h1 h2
  have hv1 : ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    have h3 : MaxV P (detLat N) 1 := by
      have := GlobalTheory.CharVal.DetFrame.maxV_detLat X.E n N P 1 (fun x => by rw [hS P hP]; rfl)
      simpa using this
    have := h3.pow h
    rw [← hyI, one_pow] at this
    exact (maxV_span_singleton y).unique this
  have hv : ∀ P : HeightOneSpectrum (𝓞 X.E), (p : 𝓞 X.E) ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    rw [← hϖ] at hP
    rcases P.isPrime.mem_or_mem hP with hP | hP
    · exact hv1 P hP
    · have := GlobalTheory.CharValCompare.val_star_eq_one (hv1 (conjPrime₂ P) ((mem_conjP P ϖ).2 hP))
      rw [GlobalTheory.CharValCompare.conjP_conjP] at this
      have h4 := congrArg (P.valuation X.E) hy
      rwa [map_mul, this, one_mul, map_one] at h4
  let φ : X.Tau → X.E →+* TaylorLogMetric.Qbar := fun τ =>
    (s.σ₀.comp (X.emb τ)).codRestrict TaylorLogMetric.Qbar (map_mem_Qbar (s.σ₀.comp (X.emb τ)))
  have e' : χ (idTo s (detLat N)) ^ h = ((∏ τ, (φ τ y)⁻¹ : TaylorLogMetric.Qbar) : ℂ) := by
    rw [e]
    simp [φ]
  have hmem : χ (idTo s (detLat N)) ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hh ?_)
    rw [e']
    exact mem_algebraicClosure_iff.1 (Subtype.prop _)
  refine ⟨hmem, ?_⟩
  rw [TaylorLogMetric.lamC, dite_eq_left hmem]
  have e2 : (⟨_, hmem⟩ : TaylorLogMetric.Qbar) ^ h = ∏ τ, (φ τ y)⁻¹ := Subtype.ext (by rw [← e']; simp)
  have e3 := congrArg (fun z => ‖lam z‖) e2
  simp only [map_pow, norm_pow, map_prod, norm_prod, map_inv₀, norm_inv] at e3
  rw [Finset.prod_eq_one (fun τ _ => by
    have := norm_eq_one_of_val (lam.comp (φ τ)) hv
    rw [RingHom.comp_apply] at this
    rw [this, inv_one])] at e3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 e3

end GlobalTheory.MomT.ChiUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatSmulMemOfFg
namespace GlobalTheory.FinitelyGeneratedNatMultiple

theorem exists_nat_smul_mem_of_fg {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (NumberField.RingOfIntegers E) W]
    {M N : Submodule (NumberField.RingOfIntegers E) W}
    (hM : GlobalTheory.ThetaMove.Full M) (hN : Submodule.FG N) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : NumberField.RingOfIntegers E) • x ∈ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have hM' : ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : NumberField.RingOfIntegers E) • x ∈ M := hM
  choose n hn0 hn using hM'
  refine ⟨∏ y ∈ s, n y, Finset.prod_pos fun y _ => hn0 y, fun x hx => ?_⟩
  have hle : Submodule.span (NumberField.RingOfIntegers E) (s : Set W) ≤
      M.comap (LinearMap.lsmul (NumberField.RingOfIntegers E) W
        ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hy)
    show ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E) • y ∈ M
    rw [hk, mul_comm, Nat.cast_mul, mul_smul]
    exact M.smul_mem _ (hn y)
  exact hle hx

end GlobalTheory.FinitelyGeneratedNatMultiple
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.CommonRef

section

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] [Module E W] [IsScalarTower (𝓞 E) E W]

theorem exists_nat_mul_integral (a : E) : ∃ n : ℕ, 0 < n ∧ ∃ r : 𝓞 E, (n : E) * a = algebraMap (𝓞 E) E r := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_natCast] at this
      rwa [this] at hint
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [this, neg_mul] at hint
      simpa using hint.neg
  exact ⟨⟨_, h2⟩, rfl⟩

theorem full_of_span {M : Submodule (𝓞 E) W} (hM : Submodule.span E (M : Set W) = ⊤) : Full M := by
  intro x
  have hx : x ∈ Submodule.span E (M : Set W) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, r, hr⟩ := exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : 𝓞 E) • a • x = r • (n : 𝓞 E) • x := by
      simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_natCast, ← hr]
      congr 1
      push_cast
      ring
    rw [this]
    exact M.smul_mem _ hx

omit [Module E W] [IsScalarTower (𝓞 E) E W] in
theorem exists_nat_smul_le {M N : Submodule (𝓞 E) W} (hM : Full M) (hN : N.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : 𝓞 E) • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | (apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg ..)

theorem smul_mem_locP {M N : Submodule (𝓞 E) W} {m : ℕ} (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (Q : HeightOneSpectrum (𝓞 E))
    {x : W} (hx : x ∈ localization₂ Q.asIdeal N) : (m : E) • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := h _ hx
  rwa [smul_comm, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem mem_localization_of_inv_smul_mem {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : (m : E)⁻¹ • x ∈ localization₂ Q.asIdeal N) : x ∈ localization₂ Q.asIdeal M := by
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_mem_locP h Q hx
  rwa [smul_smul, mul_inv_cancel₀ hmE, one_smul] at this

theorem dom_twO [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m)
    (h₁ : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (h₂ : ∀ x ∈ M, (m : 𝓞 E) • x ∈ N)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N) :
    Dom S M (twist₂ N m (expS S)) ∧ Dom S (twist₂ N m fun Q => -expS S Q) M := by
  have hb := expS_bound S
  have hb' : ∀ Q, -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := fun Q => by have := hb Q; omega
  refine ⟨⟨fun P hP x hx => ?_, fun Q hS x hx => ?_⟩, fun P hP x hx => ?_, fun Q hS x hx => ?_⟩
  · rw [mem_localization_twist N hm hb] at hx
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_one] at hx
    exact mem_localization_of_inv_smul_mem hm h₁ P hx
  · rw [mem_localization_twist N hm hb]
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, zpow_neg_one, inv_inv]
      exact smul_mem_locP h₂ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, zpow_zero, inv_one, one_smul, ← hQ Q hS hc]
      exact hx
  · rw [mem_localization_twist N hm hb']
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_neg_one, inv_inv]
    exact smul_mem_locP h₂ P hx
  · rw [mem_localization_twist N hm hb'] at hx
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, neg_neg, zpow_one] at hx
      exact mem_localization_of_inv_smul_mem hm h₁ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, neg_zero, zpow_zero, inv_one, one_smul, ← hQ Q hS hc] at hx
      exact hx

end

theorem common_refinement : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (M₁ M₂ : Submodule (𝓞 E) (Sp E n)) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat M₁ → IsSdLat M₂ → (∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M₁ = localization₂ Q.asIdeal M₂) → ∃ F G : Submodule (𝓞 E) (Sp E n), IsSdLat F ∧ IsSdLat G ∧ Dom S M₁ F ∧ Dom S M₂ F ∧ Dom S G M₁ ∧ Dom S G M₂ := by
  intro E _ _ _ n M₁ M₂ S hS h₁ h₂ hQ
  have hfull (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : Full L := by
    apply full_of_span
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra h
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨a, ha, hA⟩ := exists_nat_smul_le (hfull M₁ h₁) h₂.1.fg
  obtain ⟨b, hb, hB⟩ := exists_nat_smul_le (hfull M₂ h₂) h₁.1.fg
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hA' : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₁ := fun x hx => by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact M₁.smul_mem _ (hA x hx)
  have hB' : ∀ x ∈ M₁, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => by
    rw [Nat.cast_mul, mul_smul]; exact M₂.smul_mem _ (hB x hx)
  have hC : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => M₂.smul_mem _ hx
  obtain ⟨hF, hG⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS E n M₂ (a * b) S hS h₂ hm
  obtain ⟨d₁, d₂⟩ := dom_twO S hm hA' hB' hQ
  obtain ⟨d₃, d₄⟩ := dom_twO S hm hC hC fun _ _ _ => rfl
  exact ⟨_, _, hF, hG, d₁, d₃, d₂, d₄⟩

end GlobalTheory.ThetaMove.CommonRef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalIdele
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Ker
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.UnifConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_of_cong (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) (b : 𝓞 E) (hb : b ∈ P.asIdeal)
    (hb2 : b ∉ P.asIdeal ^ 2) (h : Valued.v (x - algebraMap E _ (b : E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ))) :
    Valued.v x = WithZero.exp (-1 : ℤ) := by
  have h1 : P.intValuation b ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [P.intValuation_le_pow_iff_mem]; simpa using hb
  have h2 : WithZero.exp (-((2 : ℕ) : ℤ)) < P.intValuation b := by
    rw [← not_le, P.intValuation_le_pow_iff_mem]; exact hb2
  have h0 : P.intValuation b ≠ 0 := (lt_of_le_of_lt zero_le h2).ne'
  have h3 : P.intValuation b = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log h0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1
    rw [WithZero.exp_lt_exp] at h2
    congr 1
    omega
  have h4 := GlobalTheory.SuppIdele.val_algebraMap P b
  rw [← h3, ← h4]
  exact Valuation.map_eq_of_sub_lt _ (by rw [h4]; exact lt_of_le_of_lt h h2)

section

variable (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (h1 : ∀ x : E, ι (x ⊗ₜ[F] 1) = algebraMap E _ x)
  (h2 : ∀ y, y ∈ RInt F E ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1)
  (h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ),
    y ∈ Formalism.L2.DIV.suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1)

include h1 in
theorem iota_toRInt (b : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) :
    ι (toRInt F E b : AfE F E) P = algebraMap E _ (b : E) := by
  rw [GlobalTheory.SuppIdele.coe_toRInt, h1]; rfl

include h1 h2 in
theorem val_le_of_mem (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : RInt F E)
    (hz : z ∈ (P.asIdeal ^ n).map (toRInt F E)) : Valued.v (ι (z : AfE F E) P) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [iota_toRInt ι h1, GlobalTheory.SuppIdele.val_algebraMap, P.intValuation_le_pow_iff_mem]
    exact hb
  | zero =>
    rw [Subring.coe_zero, map_zero, afsplit_zero_apply, map_zero]; exact zero_le
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _), afsplit_add_apply]
    exact Valuation.map_add_le _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, afsplit_mul_apply, map_mul]
    exact (mul_le_of_le_one_left' ((h2 _).1 a.2 P)).trans hx

include h2 in
theorem eq_of_val {K : Type} [Field K] (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker)
    (y y' : (AfE F E)ˣ) (hy : y ∈ Formalism.L2.DIV.suppAt E v) (hy' : y' ∈ Formalism.L2.DIV.suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι (y : AfE F E) P) = Valued.v (ι (y' : AfE F E) P)) :
    ξ y = ξ y' := by
  have key : ∀ a b : (AfE F E)ˣ,
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι (a : AfE F E) P) = Valued.v (ι (b : AfE F E) P)) →
      ((a * b⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
    intro a b hab
    rw [h2]
    intro P
    rw [Units.val_mul, map_mul, afsplit_mul_apply, map_mul, hab, ← map_mul, ← afsplit_mul_apply, ← map_mul,
      Units.mul_inv, map_one, afsplit_one_apply, map_one]
  have hm : y * y'⁻¹ ∈ inertAt E v := by
    have k2 : (((y * y'⁻¹)⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
      rw [mul_inv_rev, inv_inv]
      exact key y' y fun P => (h P).symm
    exact Subgroup.mem_inf.2 ⟨⟨key y y' h, k2⟩, mul_mem hy (inv_mem hy')⟩
  have := hξ hm
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this

include h1 h2 in
theorem val_of_unif (P : HeightOneSpectrum (𝓞 E)) (y₀ : RInt F E) (b : 𝓞 E) (hb : b ∈ P.asIdeal)
    (hb2 : b ∉ P.asIdeal ^ 2) (hc : y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (hc' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)) :
    Valued.v (ι (y₀ : AfE F E) P) = WithZero.exp (-1 : ℤ) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Valued.v (ι (y₀ : AfE F E) Q) = 1 := by
  constructor
  · have := val_le_of_mem ι h1 h2 P 2 _ hc
    rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, iota_toRInt ι h1] at this
    exact val_of_cong P _ b hb hb2 this
  · intro Q hQ
    have := val_le_of_mem ι h1 h2 Q 1 _ (by rw [pow_one]; exact hc' Q hQ)
    rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, Subring.coe_one, map_one, afsplit_one_apply] at this
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)]
    refine Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt this ?_)
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num


include h1 h2 in
theorem exists_unif {K : Type} [Field K] (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ y ∈ Formalism.L2.DIV.suppAt E v, Valued.v (ι (y : AfE F E) P) = WithZero.exp (-1 : ℤ) ∧
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Valued.v (ι (y : AfE F E) Q) = 1) ∧ unifVal ξ P = ξ y := by
  obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    simpa using this
  obtain ⟨y, y₀, e1, e2, e3, e4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hP
  have hv := val_of_unif ι h1 h2 P y₀ b hb hb2 e3 e4
  rw [e1] at hv
  refine ⟨y, e2, hv.1, hv.2, ?_⟩
  have hex : ∃ k, IsUnifVal ξ P k := by
    refine ⟨ξ y, fun w hw z z₀ c f1 hc hc2 f2 f3 f4 => ?_⟩
    obtain rfl : w = v := HeightOneSpectrum.ext (hw.symm.trans hP)
    have hz := val_of_unif ι h1 h2 P z₀ c hc hc2 f3 f4
    rw [f1] at hz
    refine eq_of_val ι h2 ξ w hξ z y f2 e2 fun Q => ?_
    by_cases hQ : Q = P
    · rw [hQ, hz.1, hv.1]
    · rw [hz.2 Q hQ, hv.2 Q hQ]
  unfold unifVal
  rw [dite_eq_left hex]
  exact (hex.choose_spec v hP y y₀ b e1 hb hb2 e2 e3 e4).symm

end

theorem under_eq (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * J) : P.asIdeal.under (𝓞 F) = v.asIdeal := by
  have hle : v.asIdeal ≤ P.asIdeal.under (𝓞 F) := by
    rw [Ideal.under, ← Ideal.map_le_iff_le_comap, h]; exact fun t ht => (Ideal.mul_le_inf ht).1
  exact (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top hle).symm

theorem unif_notMem (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (a : 𝓞 F) (ha : a ∈ v.asIdeal)
    (ha2 : a ∉ v.asIdeal ^ 2) :
    algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by rw [h]; exact fun t ht => (Ideal.mul_le_inf ht).1
  refine ⟨hle (Ideal.mem_map_of_mem _ ha), fun hm => ?_⟩
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {a} := Ideal.dvd_span_singleton.2 ha
  have hJv : ¬ J ≤ v.asIdeal := fun hh => ha2 (by
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]; exact Ideal.mul_mono_right hh)
  have hE := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hJ
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, h] at hE
  rw [← Ideal.dvd_span_singleton, hE, pow_two, mul_assoc, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at hm
  rcases P.isPrime.mul_le.1 hm with h' | h'
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h')).symm
  · apply hJv
    rw [← under_eq v P _ h]
    exact Ideal.map_le_iff_le_comap.1 h'

theorem exists_local_idele (v : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0) :
    ∃ x : (FiniteAdeleRing (𝓞 F) F)ˣ, (x : FiniteAdeleRing (𝓞 F) F) v = algebraMap F _ a ∧
      ∀ w, w ≠ v → (x : FiniteAdeleRing (𝓞 F) F) w = 1 := by
  have hs : ∀ c : F, (1 + afsplitI v (algebraMap F _ c - 1)) v = algebraMap F _ c := fun c => by
    rw [afsplit_add_apply, afsplitI_self, afsplit_one_apply, add_sub_cancel]
  have hn : ∀ (c : F) w, w ≠ v → (1 + afsplitI v (algebraMap F _ c - 1)) w = 1 := fun c w hw => by
    rw [afsplit_add_apply, afsplitI_ne v w hw, afsplit_one_apply, add_zero]
  have hm : (1 + afsplitI v (algebraMap F _ a - 1)) * (1 + afsplitI v (algebraMap F _ a⁻¹ - 1)) = 1 := by
    refine FiniteAdeleRing.ext _ fun w => ?_
    rw [afsplit_mul_apply, afsplit_one_apply]
    by_cases hw : w = v
    · subst hw
      rw [hs, hs, ← map_mul, mul_inv_cancel₀ ha, map_one]
    · rw [hn _ w hw, hn _ w hw, one_mul]
  exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, hs a, hn a⟩

theorem unifVal_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K]
    (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (hF : (idF F E).range ≤ ξ.ker) (hξ : inertAt E v ≤ ξ.ker) (hne : P ≠ P')
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    unifVal ξ P' = (unifVal ξ P)⁻¹ := by
  obtain ⟨ι, h1, h2, h3, h4⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal := by rw [h, mul_comm]
  have hP := under_eq v P _ h
  have hP' := under_eq v P' _ h'
  obtain ⟨y, y1, y2, y3, y4⟩ := exists_unif ι h1 h2 ξ v hξ P hP
  obtain ⟨z, z1, z2, z3, z4⟩ := exists_unif ι h1 h2 ξ v hξ P' hP'
  obtain ⟨a, ha, ha2⟩ : ∃ b ∈ v.asIdeal, b ∉ v.asIdeal ^ 2 := by
    have := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
    simpa using this
  have ha0 : (a : F) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
    simpa using this
  obtain ⟨x, x1, x2⟩ := exists_local_idele v (a : F) ha0
  have hxs : idF F E x ∈ Formalism.L2.DIV.suppAt E v := by
    simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w ((1 : E) ⊗ₜ[F] (x : FiniteAdeleRing (𝓞 F) F)) = 1
    rw [afsplit_prV_tmul, x2 w hw]; rfl
  have hxv : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal →
      Valued.v (ι (idF F E x : AfE F E) Q) = WithZero.exp (-1 : ℤ) := by
    intro Q Q' hQ hm
    obtain ⟨m1, m2⟩ := unif_notMem v Q Q' hQ hm a ha ha2
    have hu : Q.under (𝓞 F) = v := HeightOneSpectrum.ext (under_eq v Q _ hm)
    refine val_of_cong Q _ _ m1 m2 (h4 x (a : F) Q 2 ?_)
    subst hu
    rw [x1, sub_self, map_zero]; exact zero_le
  have hyz : ξ (y * z) = ξ (idF F E x) := by
    refine eq_of_val ι h2 ξ v hξ _ _ (mul_mem y1 z1) hxs fun Q => ?_
    rw [Units.val_mul, map_mul, afsplit_mul_apply, map_mul]
    by_cases hQ : Q = P
    · subst hQ
      rw [y2, z3 Q hne, mul_one, hxv Q P' hne h]
    by_cases hQ' : Q = P'
    · subst hQ'
      rw [z2, y3 Q hQ, one_mul, hxv Q P hQ h']
    rw [y3 Q hQ, z3 Q hQ', one_mul, (h3 v _).1 hxs Q, map_one]
    intro hu
    have hle : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
      rw [← h, ← hu]; exact Ideal.map_comap_le
    rcases Q.isPrime.mul_le.1 hle with k | k
    · exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm
    · exact hQ' (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm
  have hx1 : ξ (idF F E x) = 1 := hF ⟨x, rfl⟩
  rw [hx1, map_mul] at hyz
  rw [y4, z4]
  exact eq_inv_of_mul_eq_one_right hyz

end GlobalTheory.UnifConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CrdSurjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.IdxHom

open GlobalTheory.CharValCompare Matrix Kronecker

variable {E : Type} [Field E] {a b : ℕ}

def crd (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b →+ (Fin a × Fin b → E) where
  toFun x := (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec
  map_zero' := by simp
  map_add' x y := by
    rw [LinearMap.add_comp, LinearMap.comp_add, map_add (f := _), Matrix.vec_add]

theorem crd_apply (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    crd g g' x = (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec := rfl

theorem crd_injective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Injective (crd g g') := by
  intro x y h
  rw [crd_apply, crd_apply, Matrix.vec_inj] at h
  have h1 := LinearMap.toMatrix'.injective h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h1 (g.symm v)
  simpa using this

theorem crd_surjective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Surjective (crd g g') := by
  intro v
  obtain ⟨A, rfl⟩ := Matrix.vec_bijective.2 v
  refine ⟨(g' : Sp E b →ₗ[E] Sp E b) ∘ₗ Matrix.toLin' A ∘ₗ (g.symm : Sp E a →ₗ[E] Sp E a), ?_⟩
  rw [crd_apply]
  congr 1
  rw [← LinearMap.toMatrix'_toLin' A]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

def chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) : Matrix (Fin a × Fin b) (Fin a × Fin b) E :=
  (LinearMap.toMatrix' ((g₂.symm : Sp E a →ₗ[E] Sp E a) ∘ₗ (g₁ : Sp E a →ₗ[E] Sp E a)))ᵀ ⊗ₖ
    LinearMap.toMatrix' ((g₁'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ (g₂' : Sp E b →ₗ[E] Sp E b))

theorem chg_mulVec (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    chg g₁ g₂ g₁' g₂' *ᵥ crd g₂ g₂' x = crd g₁ g₁' x := by
  rw [chg, crd_apply, crd_apply, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp

theorem det_chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    (chg g₁ g₂ g₁' g₂').det = ((dt g₂)⁻¹ * dt g₁) ^ b * ((dt g₁')⁻¹ * dt g₂') ^ a := by
  rw [chg, Matrix.det_kronecker, Matrix.det_transpose, LinearMap.det_toMatrix', LinearMap.det_toMatrix',
    LinearMap.det_comp, LinearMap.det_comp, LinearEquiv.det_coe_symm, LinearEquiv.det_coe_symm, Fintype.card_fin,
    Fintype.card_fin, dt_eq, dt_eq, dt_eq, dt_eq]

variable [NumberField E]

theorem ordE_chg (P : HeightOneSpectrum (𝓞 E)) (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    ordE P (chg g₁ g₂ g₁' g₂').det =
      (b * ordE P (dt g₁) - a * ordE P (dt g₁')) - (b * ordE P (dt g₂) - a * ordE P (dt g₂')) := by
  have h : ∀ {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n), P.valuation E (dt f) = WithZero.exp (-ordE P (dt f)) := by
    intro n f
    rw [ordE, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 (dt_ne f))]
  rw [det_chg, ordE, map_mul, map_pow, map_pow, map_mul, map_mul, map_inv₀, map_inv₀, h g₁, h g₂, h g₁', h g₂',
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul]
  ring

variable [StarRing E]

theorem mem_homAt_iff {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b} (hg : IsFr P N g) (hg' : IsFr P N' g') (x : HomE E a b) :
    x ∈ homAt {P} N N' ↔ ∀ i, IntAt P (crd g g' x i) := by
  change (∀ Q ∈ ({P} : Finset _), ∀ y ∈ localization₂ Q.asIdeal N, x y ∈ localization₂ Q.asIdeal N') ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro h ⟨j, i⟩
    have h1 := h _ ((hg _).2 (single_mem_stdAt P j))
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice] at h1
    have h2 := h1 i
    simpa [crd_apply, LinearMap.toMatrix'_apply] using h2
  · intro h y hy
    obtain ⟨z, rfl⟩ := g.surjective y
    rw [hg, stdAt, mem_localization_standardLattice] at hy
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice]
    intro i
    have : g'.symm (x (g z)) =
        LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a)) *ᵥ z := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [this, Matrix.mulVec, dotProduct]
    exact intAt_sum _ _ fun j _ => (h (j, i)).mul (hy j)

theorem relIndex_homAt : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' → homAt {P} N₂ N₂' ≤ homAt {P} N₁ N₁' → (((homAt {P} N₂ N₂').toAddSubgroup.relIndex (homAt {P} N₁ N₁').toAddSubgroup : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ (volExp P N₁ N₁' - volExp P N₂ N₂') := by
  intro E _ _ _ a b P N₁ N₂ N₁' N₂' h₁ h₂ h₁' h₂' hle
  obtain ⟨g₁, hg₁⟩ := exists_isFr P h₁
  obtain ⟨g₂, hg₂⟩ := exists_isFr P h₂
  obtain ⟨g₁', hg₁'⟩ := exists_isFr P h₁'
  obtain ⟨g₂', hg₂'⟩ := exists_isFr P h₂'
  have h0 : ∀ x, x ∈ (homAt {P} N₁ N₁').toAddSubgroup.map (crd g₁ g₁') ↔ ∀ i, IntAt P (x i) := by
    intro x
    obtain ⟨y, rfl⟩ := crd_surjective g₁ g₁' x
    rw [AddSubgroup.mem_map_iff_mem (crd_injective _ _), Submodule.mem_toAddSubgroup, mem_homAt_iff hg₁ hg₁']
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (crd_injective g₁ g₁'),
    GlobalTheory.IdxDet.relIndex_mulVec E (Fin a × Fin b) P (chg g₁ g₂ g₁' g₂') _ _ ?_ h0 ?_ (AddSubgroup.map_mono hle),
    ordE_chg, volExp, volExp, ordDet_eq hg₁, ordDet_eq hg₂, ordDet_eq hg₁', ordDet_eq hg₂']
  · rw [det_chg]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
      (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (h0 _).2 ((mem_homAt_iff hg₂ hg₂' y).1 hy), (chg_mulVec _ _ _ _ y).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, rfl⟩ := crd_surjective g₂ g₂' v
      exact ⟨y, (mem_homAt_iff hg₂ hg₂' y).2 ((h0 _).1 hv), (chg_mulVec _ _ _ _ y).symm⟩

end GlobalTheory.IdxHom
end
end
