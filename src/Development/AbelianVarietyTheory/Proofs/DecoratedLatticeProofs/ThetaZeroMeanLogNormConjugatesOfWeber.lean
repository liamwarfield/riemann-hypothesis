module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPeriodLatticeIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedAreaClassInvariant
noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise


open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dite_eq_left (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaZeroNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeanSquareNormalizedThetaTwoTorsion
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.OddThetaNorm
open scoped BigOperators UpperHalfPlane Real
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaNullNormSquares

open GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic (thetaChar IsEvenChar IsPeriodLattice NormTheta0 jacobiTheta₂_half)

theorem normSq1_eq_nrm1Sq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) :
    GlobalTheory.Glob.IntegralWittCoefficients.normSq1 Λ G = nrm1Sq Λ G := by
  unfold GlobalTheory.Glob.IntegralWittCoefficients.normSq1 nrm1Sq
  have : ∀ z : ℂ, -Real.pi * (GlobalTheory.Glob.IntegralWittCoefficients.hf1 Λ z z).re = -Real.pi * ‖z‖ ^ 2 / area Λ := fun z => by
    unfold GlobalTheory.Glob.IntegralWittCoefficients.hf1
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    ring
  simp only [this]

theorem oddTheta_eq (τ : ℍ) (w : ℂ) : oddTheta τ w =
    Complex.exp (π * Complex.I * (τ / 4 + w + 1 / 2)) * jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ :=
  JacobiDeriv.thetaChar_half_half τ w

theorem norm_sq_oddTheta (τ : ℍ) (A B : Fin 2) (M K : ℤ) (u : ℂ)
    (hu : u + ((τ : ℂ) + 1) / 2 = (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2 + (M * τ + K)) :
    ‖oddTheta τ u‖ ^ 2 * Real.exp (-2 * π * u.im ^ 2 / τ.im) = ‖thetaChar A B 0 τ‖ ^ 2 := by
  have hy := τ.im_ne_zero
  have him : u.im = ((A : ℕ) : ℝ) * τ.im / 2 + M * τ.im - τ.im / 2 := by
    have := congrArg Complex.im hu
    simp at this
    linarith
  rw [oddTheta_eq, hu, jacobiTheta₂_add_lattice, jacobiTheta₂_half, norm_mul, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
  set T := ‖thetaChar A B 0 τ‖
  have e : ∀ x y z w : ℝ, 2 * (x + y + z) + w = 0 →
      (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w = T ^ 2 := fun x y z w h => by
    have : (Real.exp x * (Real.exp y * (Real.exp z * T))) ^ 2 * Real.exp w =
        Real.exp (2 * (x + y + z) + w) * T ^ 2 := by
      rw [Real.exp_add, show 2 * (x + y + z) = (x + y + z) + (x + y + z) by ring, Real.exp_add,
        Real.exp_add, Real.exp_add]
      ring
    rw [this, h, Real.exp_zero, one_mul]
  refine e _ _ _ _ ?_
  simp [Complex.mul_re, Complex.mul_im, sq, him]
  field_simp
  ring

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem lat_gen : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨a, a * τ, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Complex.real_smul] at hst
    have e : (s : ℂ) + t * τ = 0 := mul_left_cancel₀ ha (by linear_combination hst)
    have h1 := congrArg Complex.im e
    simp [τ.im_ne_zero] at h1
    simp [h1] at e
    exact ⟨e, h1⟩
  · ext x
    rw [h, AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by simp; ring⟩
    · rintro ⟨n, m, rfl⟩
      exact ⟨m, n, by simp; ring⟩

theorem canTheta_eq : ∃ c : ℂ, c ≠ 0 ∧ ∀ z, canTheta a τ z = c * sgStar Λ z := by
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  have hu := huniq _ (differentiable_canTheta a τ) (thetaTranslation_canonicalOddTheta_lattice ha h)
  refine ⟨_, fun h0 => ?_, hu⟩
  have k := odd_theta_norm_canonical ha h
  rw [show canTheta a τ = fun z => (0 : ℂ) * sgStar Λ z from funext fun z => by rw [hu z, h0],
    odd_theta_norm_smul] at k
  have hy := τ.im_pos
  have : 0 < (Real.sqrt (2 * τ.im))⁻¹ := by positivity
  rw [← k] at this
  simp at this

theorem jacobiTheta₂_eq_zero_iff (w : ℂ) :
    jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ = 0 ↔ a * w ∈ Λ := by
  obtain ⟨-, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  obtain ⟨c, hc, hC⟩ := canTheta_eq ha h
  rw [← hz]
  have := hC (a * w)
  rw [canTheta, mul_div_cancel_left₀ _ ha, oddTheta_eq] at this
  constructor
  · intro h0
    rw [h0, mul_zero, mul_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hc
  · intro h0
    rw [h0, mul_zero] at this
    simpa [Complex.exp_ne_zero] using this

theorem meanSquare_normalizedThetaTwoTorsion {t : ℂ} (ht : t ∉ Λ) :
    0 < nrm1Sq Λ (GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t) ∧
    (nrm1Sq Λ (GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t))⁻¹ = Real.sqrt (2 * τ.im) *
      (‖oddTheta τ (t / a)‖ ^ 2 * Real.exp (-2 * π * (t / a).im ^ 2 / τ.im)) := by
  obtain ⟨⟨-, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (lat_gen ha h)
  obtain ⟨c, hc, hC⟩ := canTheta_eq ha h
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have k := odd_theta_norm_canonical ha h
  rw [show canTheta a τ = fun z => c * sgStar Λ z from funext hC, odd_theta_norm_smul] at k
  have th : GlobalTheory.Glob.IntegralWittCoefficients.th0 Λ t = fun z => (U1 Λ t (sgStar Λ) 0)⁻¹ * U1 Λ t (sgStar Λ) z :=
    funext fun z => div_eq_inv_mul _ _
  rw [th, odd_theta_norm_smul, odd_theta_norm_translate ha h hU, norm_inv, inv_pow]
  have hS : sgStar Λ t ≠ 0 := fun h0 => ht ((hz t).1 h0)
  have hU0 : U1 Λ t (sgStar Λ) 0 ≠ 0 := by
    simp [U1, hS, Complex.exp_ne_zero]
  have hval := thetaTranslation_weighted_normSq_mul Λ t (sgStar Λ) 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at hval
  have hct := hC t
  rw [canTheta] at hct
  have hnorm : ‖c‖ ^ 2 * ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 =
      ‖oddTheta τ (t / a)‖ ^ 2 * Real.exp (-2 * π * (t / a).im ^ 2 / τ.im) := by
    have e1 := congrArg (fun x => ‖x‖ ^ 2) hct
    simp only [norm_mul, mul_pow, Complex.norm_exp] at e1
    have ht' : t = a * (t / a) := by field_simp
    have hre : (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re =
        π * ((t / a).re ^ 2 - (t / a).im ^ 2) / (2 * τ.im) := by
      rw [show (2 * (τ.im : ℂ)) = ((2 * τ.im : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
      simp [sq]
    have hnt : ‖t‖ ^ 2 = ‖a‖ ^ 2 * ((t / a).re ^ 2 + (t / a).im ^ 2) := by
      conv_lhs => rw [ht']
      rw [norm_mul, mul_pow, Complex.sq_norm (t / a), Complex.normSq_apply]
      ring
    have eX : Real.exp (π * (t / a) ^ 2 / (2 * τ.im) : ℂ).re ^ 2 *
        Real.exp (-π * ‖t‖ ^ 2 / area Λ) = Real.exp (-2 * π * (t / a).im ^ 2 / τ.im) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, hre, hnt, LatticeAreaBound.area_eq ha h]
      congr 1
      field_simp
      ring
    rw [hval, ← mul_assoc, ← e1, ← eX]
    ring
  have hNpos : 0 < nrm1Sq Λ (sgStar Λ) := by
    have h1 : 0 < ‖c‖ ^ 2 * nrm1Sq Λ (sgStar Λ) := by rw [k]; positivity
    exact (pos_iff_pos_of_mul_pos h1).1 (by positivity)
  have hP : 0 < ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [← hnorm]
  have hs : 0 < Real.sqrt (2 * τ.im) := by positivity
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  set N := nrm1Sq Λ (sgStar Λ)
  set P := ‖U1 Λ t (sgStar Λ) 0‖ ^ 2
  set s := Real.sqrt (2 * τ.im)
  set C := ‖c‖ ^ 2
  rw [mul_inv, inv_inv, show N⁻¹ = C * s by
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv]
    field_simp at k ⊢
    linarith]
  ring

theorem thetaChar_eq_zero_iff (A B : Fin 2) (m n : ℤ) :
    thetaChar A B ((m * (τ : ℂ) + n) / 2) τ = 0 ↔
      Even (m + ((A : ℕ) : ℤ) - 1) ∧ Even (n + ((B : ℕ) : ℤ) - 1) := by
  have e : thetaChar A B ((m * (τ : ℂ) + n) / 2) τ = 0 ↔
      jacobiTheta₂ ((m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2) τ = 0 := by
    simp [thetaChar, Complex.exp_ne_zero]
  have e2 : (m * (τ : ℂ) + n) / 2 + (((A : ℕ) : ℂ) * τ + ((B : ℕ) : ℂ)) / 2 =
      (((m + ((A : ℕ) : ℤ) - 1 : ℤ) : ℂ) * τ + ((n + ((B : ℕ) : ℤ) - 1 : ℤ) : ℂ)) / 2 +
        ((τ : ℂ) + 1) / 2 := by
    push_cast
    ring
  rw [e, e2, jacobiTheta₂_eq_zero_iff ha h, ← mul_div_assoc, half_mem_iff ha h]
  generalize m + ((A : ℕ) : ℤ) - 1 = p
  generalize n + ((B : ℕ) : ℤ) - 1 = q
  simp only [parity_simps]
  tauto

end

theorem existsUnique_char (m n : ℤ) (hnot : ¬ (Even m ∧ Even n)) :
    ∃! c : Fin 2 × Fin 2, IsEvenChar c.1 c.2 ∧
      Even (m + ((c.1 : ℕ) : ℤ) - 1) ∧ Even (n + ((c.2 : ℕ) : ℤ) - 1) := by
  have huniq : ∀ A B A' B' : Fin 2, Even (m + ((A : ℕ) : ℤ) - 1) → Even (n + ((B : ℕ) : ℤ) - 1) →
      Even (m + ((A' : ℕ) : ℤ) - 1) → Even (n + ((B' : ℕ) : ℤ) - 1) → (A', B') = (A, B) := by
    intro A B A' B' h1 h2 h3 h4
    rw [Int.even_iff] at h1 h2 h3 h4
    have := A.isLt
    have := B.isLt
    have := A'.isLt
    have := B'.isLt
    rw [Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]
    omega
  have hex : ∃ A B : Fin 2, IsEvenChar A B ∧ Even (m + ((A : ℕ) : ℤ) - 1) ∧
      Even (n + ((B : ℕ) : ℤ) - 1) := by
    rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
    · exact absurd ⟨hm, hn⟩ hnot
    · exact ⟨1, 0, by simp [IsEvenChar], by simpa using hm, by simpa [parity_simps] using hn⟩
    · exact ⟨0, 1, by simp [IsEvenChar], by simpa [parity_simps] using hm, by simpa using hn⟩
    · exact ⟨0, 0, by simp [IsEvenChar], by simpa [parity_simps] using hm,
        by simpa [parity_simps] using hn⟩
  obtain ⟨A, B, h0, h1, h2⟩ := hex
  exact ⟨(A, B), ⟨h0, h1, h2⟩, fun c hc => huniq A B c.1 c.2 h1 h2 hc.2.1 hc.2.2⟩

theorem normTheta0 : NormTheta0 := by
  intro Λ ω₁ τ t₀ hω hτ hP h2 ht
  let τ' : ℍ := ⟨τ, hτ⟩
  have hτ' : (τ' : ℂ) = τ := rfl
  have h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, ω₁ * (m * (τ' : ℂ) + n) = x := fun x => by
    rw [hP x]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by rw [hτ']; ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by rw [hτ']; ring⟩
  obtain ⟨m, n, hmn⟩ := (h _).1 h2
  have hu : t₀ / ω₁ = (m * (τ' : ℂ) + n) / 2 := by
    rw [div_eq_iff hω]
    linear_combination (-1 / 2 : ℂ) * hmn
  have hnot : ¬ (Even m ∧ Even n) := by
    intro hp
    apply ht
    have hm := (half_mem_iff hω h m n).2 (by
      obtain ⟨hm, hn⟩ := hp
      simp [parity_simps, hm, hn])
    rwa [hmn, mul_div_cancel_left₀ _ (two_ne_zero)] at hm
  rw [normSq1_eq_nrm1Sq]
  obtain ⟨hpos, hinv⟩ := meanSquare_normalizedThetaTwoTorsion hω h ht
  refine ⟨?_, hpos, ?_⟩
  · rw [hu]
    simp only [show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h]
    exact existsUnique_char m n hnot
  · intro A B _ hz
    rw [hu, show τ = (τ' : ℂ) from rfl, thetaChar_eq_zero_iff hω h] at hz
    obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := hz
    rw [hinv]
    refine congrArg (fun x => Real.sqrt (2 * τ.im) * x) (norm_sq_oddTheta τ' A B
      (r + 1 - ((A : ℕ) : ℤ)) (s + 1 - ((B : ℕ) : ℤ)) _ ?_)
    have hm : (m : ℂ) = 2 * r + 1 - ((A : ℕ) : ℂ) := by
      have : m = 2 * r + 1 - ((A : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    have hn : (n : ℂ) = 2 * s + 1 - ((B : ℕ) : ℂ) := by
      have : n = 2 * s + 1 - ((B : ℕ) : ℤ) := by omega
      rw [this]
      push_cast
      ring
    rw [hu, hm, hn]
    push_cast
    ring

end GlobalTheory.ThetaNullNormSquares
end
end

noncomputable section

namespace GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation

theorem normTheta0 : GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic.NormTheta0 := GlobalTheory.ThetaNullNormSquares.normTheta0

end GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEq
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEqStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_covolume_conjugateLattices_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  first | exact @GlobalTheory.MeanLogArea.mean_log_area | exact GlobalTheory.MeanLogArea.mean_log_area | (intros; apply GlobalTheory.MeanLogArea.mean_log_area <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralThetaEtaTwelfthPowerConjugates
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralThetaEtaTwelfthPowerConjugates
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IntegralXCore

theorem exists_integral_theta_ratio : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  intro hL hT D hJ cc δ M _ t hS
  obtain ⟨e, g, hg, hval, hρ⟩ := GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj D cc δ M t hS
  have crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hS.1, hS.2.1⟩
  have hYρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ ((12 * e ^ 2 - g) / 4) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) ^ 2 - g2 (lamConj M ρ (lamOf D cc δ))) / 4 := by
    intro ρ
    obtain ⟨-, h2, -, h4⟩ := hρ ρ
    rw [h2, h4]
    simp only [map_div₀, map_sub, map_mul, map_pow, map_ofNat]
  obtain ⟨d0, -, n0, -⟩ := hρ M.val
  have h20 := (hS.2.2.2 M.val).1
  have hY0 : (((12 * e ^ 2 - g) / 4 : M) : ℂ) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamOf D cc δ) (t M.val) ^ 2 - g2 (lamOf D cc δ)) / 4 := by
    have h := hYρ M.val
    rw [hval] at h
    exact h
  rw [hval] at d0 n0 h20
  obtain ⟨L, hLL⟩ := (GlobalTheory.ThetaConj.isLat_lamOf crv).exists_periodPair
  obtain ⟨ω, τ, hω, hτ⟩ := GlobalTheory.exists_lattice_eq_mul_tau L
  have hP : JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D cc δ) ω (τ : ℂ) := fun x => by
    rw [hLL, hτ]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
  obtain ⟨a, b, hab, hz⟩ := GlobalTheory.IntegralX.exists_char hω hP (hT τ).2.1 h20 n0
  obtain ⟨hne, s, hs, hX⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω τ _ hω hP d0 h20 n0 a b hab hz
  rw [← hY0] at hne hX
  have hYne : ((12 * e ^ 2 - g) / 4 : M) ≠ 0 := fun h => hne (by rw [h]; simp)
  refine ⟨1 / ((12 * e ^ 2 - g) / 4) ^ 3, one_div_ne_zero (pow_ne_zero _ hYne), ?_, ?_⟩
  · have e1 : ((1 / ((12 * e ^ 2 - g) / 4) ^ 3 : M) : ℂ) = 1 / (((12 * e ^ 2 - g) / 4 : M) : ℂ) ^ 3 := by
      push_cast
      rfl
    rw [e1, hX]
    exact GlobalTheory.IntegralX.integral hT _ ω τ hω hP d0 (hJ cc δ hS.1 hS.2.1) a b hab s hs
  · intro ρ ω₁ τ' hω₁ hτ' hP' a' b' hab' hz'
    obtain ⟨dρ, -, nρ, -⟩ := hρ ρ
    obtain ⟨-, s', hs', hX'⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω₁ ⟨τ', hτ'⟩ (t ρ) hω₁ hP' dρ
      (hS.2.2.2 ρ).1 nρ a' b' hab' hz'
    rw [map_div₀, map_one, map_pow, hYρ, hX']
    have hs1 : ‖s'‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    rw [norm_mul, hs1, one_mul, norm_pow, norm_div]

end GlobalTheory.IntegralXCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralThetaEtaTwelfthPowerConjugatesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_thetaEta_twelfth_power_conjugates : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  first | exact @GlobalTheory.IntegralXCore.exists_integral_theta_ratio | exact GlobalTheory.IntegralXCore.exists_integral_theta_ratio | (intros; apply GlobalTheory.IntegralXCore.exists_integral_theta_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdeal
noncomputable section

namespace GlobalTheory.ConjLatticeCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem conj_lattice_core :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hC := GlobalTheory.ConjLattice.containsData hM
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := hC.1
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => GlobalTheory.ConjLattice.lamConj_spec GlobalTheory.ConjLattice.uniformization_holds M ρ'
    (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  have hfix : ∀ ρ' : M →ₐ[ℚ] ℂ, EquidistributedConjugates.FixesK D M ρ' → ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ,
      x ≠ 0 ∧ lamConj M ρ' (lamOf D cc δ) = lamOf D c x := by
    intro ρ' hρ'
    obtain ⟨cc', δ', hc', -, he⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ ⟨hcc, hδ⟩ M ρ'
      (GlobalTheory.ConjEquidistrib.fixK_of_fixesK D M ρ' hm hρ') h2 h3 1 one_pos
    exact ⟨cc', hc'.1.1, δ', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc' hc'.1 δ' hc'.2, he⟩
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · exact hfix ρ hρ
  · have hρ' : EquidistributedConjugates.FixesK D M (EquidistributedConjugates.conjEmb M ρ) :=
      (GlobalTheory.ConjEquidistrib.fixesK_conjEmb_iff D M ρ hm).2 hρ
    obtain ⟨c, hc, x, hx, hxe⟩ := hfix _ hρ'
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds
        GlobalTheory.ConjLattice.uniformization_holds
    have hmap : (lamConj M ρ (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj =
        lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [GlobalTheory.ConjLattice.discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [GlobalTheory.ConjLattice.eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [GlobalTheory.ConjLattice.eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj := by
      rw [← hmap, GlobalTheory.ConjLattice.map_cj_map_cj]
    refine ⟨c.map (GlobalTheory.ConjLattice.conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx,
      by rw [hback, hxe, GlobalTheory.ConjLattice.lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (GlobalTheory.ConjLattice.conjO D).injective] at hbot
    exact hc hbot

end GlobalTheory.ConjLatticeCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdealStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧ lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  first | exact @GlobalTheory.ConjLatticeCore.conj_lattice_core | exact GlobalTheory.ConjLatticeCore.conj_lattice_core | (intros; apply GlobalTheory.ConjLatticeCore.conj_lattice_core <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.Theta0MeanCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
open scoped nonZeroDivisors
open GlobalTheory.Theta0MeanProof (lemA lemD log_normSq log_area sum_log_nonneg bound_le_half log_d_le half_le_log_v)

theorem core (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hth : ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀)
    (D : D7) (hJ : Formalism.MainNotions.GL3Theta.admJ D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ) (hS : SignedLogMeans.HidaSetting D cc δ M t) :
    SignedLogMeans.meanLog M (lamOf D cc δ) t ≤ SignedLogMeans.bound D ∧
      SignedLogMeans.meanPosLog M (lamOf D cc δ) t ≤
        SignedLogMeans.meanLog M (lamOf D cc δ) t + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
  classical
  have hArea := GlobalTheory.T.mean_log_covolume_conjugateLattices_eq D cc δ M t hS
  obtain ⟨X, hX0, hXi, hXρ⟩ := GlobalTheory.T.exists_integral_thetaEta_twelfth_power_conjugates hP hW D hJ cc δ M t hS
  have hInt := sum_log_nonneg M X hX0 hXi
  have hB := GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal D cc δ M t hS
  have hT0 := hS.2.2.2
  set Λ := lamOf D cc δ with hΛ
  choose hdisc c hc x hx hΛeq using hB
  have hA := fun ρ => lemA D (c ρ) (hc ρ) (x ρ) (hx ρ)
  choose hstab ω τ hω hτ hLat hy1 hy2 using hA
  have hLat' : ∀ ρ, JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ Λ) (ω ρ) (τ ρ) := by
    intro ρ; rw [hΛeq ρ]; exact hLat ρ
  have htn : ∀ ρ, t ρ ∉ lamConj M ρ Λ := by
    intro ρ ht
    apply (hT0 ρ).2.1
    rw [hΛeq ρ] at ht ⊢
    exact hstab ρ _ ht
  have hNρ := fun ρ => GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation.normTheta0 _ (ω ρ) (τ ρ) (t ρ) (hω ρ) (hτ ρ) (hLat' ρ) (hT0 ρ).1 (htn ρ)
  have hex : ∀ ρ, ∃ ab : Fin 2 × Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar ab.1 ab.2 ∧
      JacobiThetaHalfCharacteristic.thetaChar ab.1 ab.2 (t ρ / ω ρ) (τ ρ) = 0 := fun ρ => (hNρ ρ).1.exists
  choose ab hab0 hab1 using hex
  set th : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖JacobiThetaHalfCharacteristic.thetaChar (ab ρ).1 (ab ρ).2 0 (τ ρ)‖ with hthdef
  set et : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖ModularForm.eta (τ ρ)‖ with hetdef
  have F1 : ∀ ρ, 0 < th ρ ∧ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log (τ ρ).im - 2 * Real.log (th ρ) :=
    fun ρ => log_normSq (hNρ ρ).2.1 (hτ ρ) ((hNρ ρ).2.2 _ _ (hab0 ρ) (hab1 ρ))
  have F2 := fun ρ => log_area hP (hω ρ) (hτ ρ) (hLat' ρ) (hdisc ρ)
  have F3 : ∀ ρ, Real.log ‖ρ X‖ = 12 * (Real.log (th ρ) - Real.log (et ρ)) := by
    intro ρ
    rw [hXρ ρ (ω ρ) (τ ρ) (hω ρ) (hτ ρ) (hLat' ρ) _ _ (hab0 ρ) (hab1 ρ), Real.log_pow,
      Real.log_div (F1 ρ).1.ne' (F2 ρ).1.ne']
    push_cast; ring

  set n : ℝ := (Module.finrank ℚ M : ℝ) with hn
  have hcard : (Finset.univ : Finset (M →ₐ[ℚ] ℂ)).card = Module.finrank ℚ M := by
    rw [Finset.card_univ]; exact AlgHom.card ℚ M ℂ
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  set St := ∑ ρ, Real.log (th ρ)
  set Se := ∑ ρ, Real.log (et ρ)
  set Sy := ∑ ρ, Real.log (τ ρ).im
  have e1 : ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) = -(1 / 2) * Real.log 2 * n - (1 / 2) * Sy - 2 * St := by
    rw [Finset.sum_congr rfl fun ρ _ => (F1 ρ).2]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e2 : ∑ ρ, Real.log (area (lamConj M ρ Λ)) = (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se := by
    rw [Finset.sum_congr rfl fun ρ _ => (F2 ρ).2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e3 : 0 ≤ St - Se := by
    have : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ = 12 * (St - Se) := by
      rw [Finset.sum_congr rfl fun ρ _ => F3 ρ, ← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  rw [e2] at hArea
  have hA2 : (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se = (Real.log Real.pi + ClassMeanPeriods.classMeanValue D) * n := by
    rw [← hArea]; field_simp
  have hsd : 0 < Real.sqrt (D.host.d : ℝ) := Real.sqrt_pos.2 (by
    have := GlobalTheory.Theta0MeanCompare.one_le_d D; linarith)
  have hcmv : ClassMeanPeriods.classMeanValue D = Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi -
      Real.log (Real.sqrt D.host.d) - logDerivativeAtOne D := by
    unfold ClassMeanPeriods.classMeanValue
    rw [Real.log_div (by positivity) hsd.ne', Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  constructor
  · unfold SignedLogMeans.meanLog
    rw [div_le_iff₀ hnpos]
    change ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) ≤ _
    rw [e1]
    unfold SignedLogMeans.bound
    rw [hcmv, hl4] at hA2
    nlinarith
  ·
    have hK : ∀ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) ≤
        Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
      intro ρ
      have hd1 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_nonneg (GlobalTheory.Theta0MeanCompare.one_le_d D)
      have hm := le_max_right 0 (2 * Real.log C₀)
      have hm0 := le_max_left 0 (2 * Real.log C₀)
      have h1 := (F1 ρ).2
      have h2 : Real.log (th ρ) ≤ Real.log C₀ :=
        Real.log_le_log (F1 ρ).1 (hth _ _ _ (hy1 ρ))
      have h3 : Real.log (2 * (τ ρ).im) ≤ Real.log (Real.sqrt D.host.d) :=
        Real.log_le_log (by linarith [hτ ρ]) (hy2 ρ)
      rw [Real.log_mul two_ne_zero (hτ ρ).ne'] at h3
      have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
        rw [Real.log_sqrt (by positivity)]; ring
      apply max_le
      · change _ ≤ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + _
        rw [h1]; linarith
      · linarith
    set K := (1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)
    have hs := Finset.sum_le_sum fun ρ (_ : ρ ∈ (Finset.univ : Finset (M →ₐ[ℚ] ℂ))) => hK ρ
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hs
    unfold SignedLogMeans.meanPosLog SignedLogMeans.meanLog
    change (∑ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)))) / n ≤
      (∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) / n + K
    rw [div_add' _ _ _ hnpos.ne', div_le_div_iff_of_pos_right hnpos]
    rw [hn]; linarith

theorem theta0Mean (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) :
    SignedLogMeans.Theta0Mean := by
  have hJ : ∀ D : D7, Formalism.MainNotions.GL3Theta.admJ D := fun D =>
    (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D ⟨GlobalTheory.InducedType.restrict_K D, GlobalTheory.InducedType.sum_eq_trace D⟩).1
  obtain ⟨C₀, hC₀, hth⟩ := lemD
  set C := max 0 (2 * Real.log C₀) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  refine ⟨⟨fun D cc δ M _ t hS => (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1,
    fun D cc δ M _ t hS L hL => ?_, ⟨1 / 2, by norm_num, fun D cc δ M _ t hS L hL => ?_⟩⟩,
    ⟨C, hC0, fun D cc δ M _ t hS => ?_⟩, ⟨1 + 2 * C, by linarith, fun D cc δ M _ t hS L hL => ?_⟩⟩
  · have := (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1
    rw [GlobalTheory.Theta0MeanCompare.bound_eq] at this
    exact this.trans (GlobalTheory.Theta0MeanCompare.kronBound_le D hL)
  · exact (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1.trans (bound_le_half D hL)
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    linarith
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    have a1 := bound_le_half D hL
    have a2 := log_d_le D hL
    have a3 : 1 / 2 ≤ L := by have := half_le_log_v D; have := abs_nonneg (logDerivativeAtOne D); linarith
    have a4 : C ≤ 2 * C * L := by nlinarith
    linarith

end GlobalTheory.Theta0MeanCore
