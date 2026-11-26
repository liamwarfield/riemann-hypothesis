module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberField

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSum
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSum
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocalSum

theorem finsum_linear_combination_four {α : Type} {f g h i : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (hh : {x | h x ≠ 0}.Finite) (hi : {x | i x ≠ 0}.Finite)
    (a b c d : ℝ) :
    (∑ᶠ x, (a * f x + (b * g x + (c * h x + d * i x)))) =
      a * (∑ᶠ x, f x) + (b * (∑ᶠ x, g x) + (c * (∑ᶠ x, h x) + d * ∑ᶠ x, i x)) := by
  have sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite →
      (Function.support fun x => c * u x).Finite :=
    fun c u hu => hu.subset fun x hx h => hx (by simp [h])
  have sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite →
      (Function.support fun x => u x + v x).Finite :=
    fun u v hu hv => (hu.union hv).subset (Function.support_add u v)
  rw [finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))),
    finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)),
    finsum_add_distrib (sm c h hh) (sm d i hi)]
  simp only [mul_finsum]

theorem two_log_norm {E A : Type} [Field E] [NormedField A] (j : E →+* A) {r : E} {d : ℕ}
    (hr : r ^ 2 = -(d : E)) : 2 * Real.log ‖j r‖ = Real.log ‖(d : A)‖ := by
  have h1 : (j r) ^ 2 = -(d : A) := by rw [← map_pow, hr]; simp
  have h2 : ‖j r‖ ^ 2 = ‖(d : A)‖ := by rw [← norm_pow, h1, norm_neg]
  rw [← h2, Real.log_pow]
  norm_num

theorem deg_of_local_formulas : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN
  have hm : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef
  set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef

  have hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖
      - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
      + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
    intro ℓ j
    have h1 := hN ℓ j
    have h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := two_log_norm (j.comp τ) hr
    linear_combination h1 + (((p : ℝ) - q) / 2) * h2
  constructor
  · have S1 := GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ
    have S4 := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
    have S3 := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
    refine (((S1.union S4).union S3).union hfin).subset ?_
    rintro ℓ ⟨j, hj⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h
    obtain ⟨⟨⟨h1, h4⟩, h3⟩, h2⟩ := h
    apply hj
    have e1 : Real.log ‖j ρ‖ = 0 := h1 j
    have e2 : Real.log ‖j (τ (t ℓ))‖ = 0 := h2 (j.comp τ)
    have e3 := h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))
    have e4 : Real.log ‖j (d : k)‖ = 0 := h4 j
    rw [map_natCast] at e4
    rw [hloc, e1, e2, e3, e4]
    simp
  ·
    have hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m := fun ℓ => by
      rw [hmdef, Embeddings.card]
    have hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m := by rw [hmdef, Embeddings.card]
    have hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
      intro ℓ
      simp only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
    have hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ
        + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (LogNorms.ofElt (d : k)).finSum ℓ)) := by
      intro ℓ
      have f1 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)
      have f2 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ
        (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
      have g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) =
          ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
        Finset.sum_congr rfl fun j _ => htt ℓ j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum] at g1
      have h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖
          - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
          + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
        have c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ =
            ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
        rw [← c1, Finset.mul_sum]
        simp only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f1
      have hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f2
      have hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖ := rfl
      rw [h0, hDd, hT, hD, hae]
      linear_combination (-(m / e) / 2) * g1
    have hA := GlobalTheory.T.product_formula_log_norms k ρ hρ
    have hE := GlobalTheory.T.product_formula_log_norms E a ha
    have hG := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
    have hΔ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ)
        + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ)
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (∑ᶠ ℓ, (LogNorms.ofElt (d : k)).finSum ℓ))) := by
      rw [finsum_congr hsum]
      exact finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _
    have hlogn : ∑ s, Real.log (n s) = -(m * x) := by
      rw [← hx]; field_simp
    have hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖)
        + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2))
        + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2 := by
      simp only [hinf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC, ← Finset.sum_div]
    have hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖ := by
      rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
      exact GlobalTheory.T.sum_embeddings_base_change E k ℂ τ (fun i => Real.log ‖i a‖)
    have hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d := by
      simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC]
    have h1 := hA.2
    have h2 := hE.2
    have h3 := hG.2
    have h4 := hΔ.2
    rw [hdinf] at h3
    have hme : m / e * e = m := div_mul_cancel₀ _ he
    have key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ =
        m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E)
          - ((p : ℝ) + q) / 2 * Real.log d) := by
      rw [hI, hfs, hlogn, hAτ, h4]
      linear_combination h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3
        + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme
    have hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y := fun Y => by field_simp
    rw [LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]
    ring

end GlobalTheory.CompanionTheory.Ar.Fl.LocalSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSumStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_log_norm_local_sum : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas | exact GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormula
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem deg_eq_of_local_two_curves : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n n' : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → -(∑ s, Real.log (n' s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) / 2 * (Real.log (n s) + Real.log d / 2) - (q : ℝ) / 2 * (Real.log (n' s) + Real.log d / 2)) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n n' x t t' hρ ha hd hr hn hn' hinf ht ht2 hfin hloc
  let N' : LogNorms k :=
    ⟨fun s => N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)), N.fin⟩
  have h := GlobalTheory.T.hermitian_log_norm_local_sum k E τ N' ρ a r p q d n x t t' hρ ha hd hr hn
    (fun s => by
      change N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)) = _
      rw [hinf s]
      ring)
    ht ht2 hfin (fun ℓ j => hloc ℓ j)
  have hf : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hs : ∑ s, Real.log (n' s) = ∑ s, Real.log (n s) := by
    have e := hn'.trans hn.symm
    rw [div_left_inj' hf] at e
    linarith
  have hsum : ∑ s, N'.inf s = ∑ s, N.inf s := by
    change ∑ s, (N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s))) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs]
    simp
  have hdeg : N'.deg = N.deg := by
    unfold LogNorms.deg
    rw [hsum]
    rfl
  exact ⟨h.1, hdeg ▸ h.2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormulaStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_metric_log_norm_formula : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n n' : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → -(∑ s, Real.log (n' s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) / 2 * (Real.log (n s) + Real.log d / 2) - (q : ℝ) / 2 * (Real.log (n' s) + Real.log d / 2)) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves | exact GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.deg_eq_of_local_two_curves <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg

theorem finite_fieldRange {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    FiniteDimensional ℚ τ.toRatAlgHom.fieldRange :=
  (AlgEquiv.ofInjectiveField τ.toRatAlgHom).toLinearEquiv.finiteDimensional

theorem const_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) →
    IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ →
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧
      (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ hty hrt hmem hline he hconst
  obtain ⟨P, hP, x, hx, X, v, w, hk, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ τ.toRatAlgHom.fieldRange (finite_fieldRange τ) hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, -, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hT0 : T.det ≠ 0 := hdet hloc.1
  have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
    (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
  have hG0 := (GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ⟨2, Nat.prime_two⟩ hloc horth).1
  obtain ⟨hfm, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt hmem hline he
    hconst hloc.1 hT hfr
  have hφ : φ X.K X.y v w ≠ 0 := hline.ne X.K X.β X.y v w hfm
  have hmemK : ∀ t : E, τ t ∈ X.K := fun t => hk (τ.toRatAlgHom.mem_fieldRange.2 ⟨t, rfl⟩)
  set G := gramE (FU.Di i) (x ∘ Sum.inr) with hGdef
  let a : X.K := ⟨τ T.det, hmemK _⟩
  let b : X.K := ⟨τ G.det, hmemK _⟩
  have ha : a ≠ 0 := fun h => hT0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hb : b ≠ 0 := fun h => hG0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hbC : τ G.det ≠ 0 := (map_ne_zero τ).2 hG0
  refine ⟨X.K, inferInstance, φ X.K X.y v w * a / b, X.hc, X.hM, div_ne_zero (mul_ne_zero hφ ha) hb, ?_⟩
  have hcoe : ((φ X.K X.y v w * a / b : X.K) : ℂ) = ((φ X.K X.y v w : X.K) : ℂ) * τ T.det / τ G.det := rfl
  rw [hcoe]
  field_simp
  linear_combination hval

end GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_cm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧ (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | exact GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg.const_algebraic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriod
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_curve0_hasPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) →
    ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧
      (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro E _ _ _ H _ χ hχ ρ hρ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hU := GlobalTheory.thetaUnifAV_closed
  have hX := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  obtain ⟨M, _, ω, C, x, hω, hpr, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period GlobalTheory.T.exists_cmEllipticCurve_withPeriod hU hL hX E H χ hχ ρ hρ
  obtain ⟨C', π, c'⟩ := exists_ellMap hL.polBaseChange E H _ ω C ℂ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P π c'.2.1 u
  obtain ⟨Hm, χ', Ef, h1, h2, h3⟩ := id hu
  obtain ⟨w, hw, -⟩ := h2 C'.v (C'.basis.1 0)
  have hd := C'.dim
  let Z : Curve0 H ρ := ⟨M, ω, C, hω, C', π, c', u, hu, c, hc, hΛ, w ⟨0, by omega⟩ / c, by
    convert hw using 1
    funext j
    rw [mul_div_cancel₀ _ hc]
    congr 1
    apply Fin.ext
    have := j.2
    simp only
    omega⟩
  exact ⟨Z, x, GlobalTheory.T.curve_z_ne_zero E H ρ Z, hper, hx⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowla_selberg_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM

theorem flatDegree_mean_ext {M k : Type} [Field M] [NumberField M] [Field k] [NumberField k] (f : M →+* k)
    (F : (M →+* ℂ) → ℝ) :
    (∑ s : k →+* ℂ, F (s.comp f)) / Module.finrank ℚ k = (∑ s, F s) / Module.finrank ℚ M := by
  have h := GlobalTheory.T.sum_embeddings_base_change M k ℂ f F
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [div_eq_div_iff hk hM]
  linear_combination h

theorem flatDegree_sum_conj {E A : Type} [Field E] [NumberField E] [IsCMField E] [Field A] [CharZero A]
    (F : A → ℝ) (t : E) :
    ∑ j : E →+* A, F (j (IsCMField.complexConj E t)) = ∑ j : E →+* A, F (j t) := by
  let c : E →+* E := RingHomClass.toRingHom (IsCMField.complexConj E)
  let σ : (E →+* A) ≃ (E →+* A) :=
    { toFun := fun j => j.comp c
      invFun := fun j => j.comp c
      left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x)
      right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }
  exact Equiv.sum_comp σ (fun j => F (j t))

theorem flatDegree_logOm_re (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {x : ℝ}
    (hx : (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) -
      deriv χ.LFunction 1 / χ.LFunction 1) :
    (logOm E χ).re = x - Real.log (rootDiscr E) + Real.log (Real.sqrt d) := by
  have hrd : 0 < rootDiscr E := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : 0 < √(d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : deriv χ.LFunction 1 / χ.LFunction 1 =
      ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x := by
    rw [hx]; ring
  unfold GlobalTheory.CM.logOm
  rw [hL]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']
  ring

theorem flatDegree : FlatDegree := by
  unfold FlatDegree
  intro E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN
  obtain ⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩ := hflat
  obtain ⟨hNinf, hNfin⟩ := hN
  have hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ) := by
    intro b
    cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]
  choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)
  have hx : x false = x true := Complex.ofReal_injective ((hxv false).trans (hxv true).symm)
  haveI := (Z true).nf
  haveI := (Z false).nf
  obtain ⟨n₁, hn₁, hm₁⟩ := hper true
  obtain ⟨n₀, hn₀, hm₀⟩ := hper false
  obtain ⟨k, hkfd, r, hc, hM, hr0, hrz⟩ :=
    GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm
  haveI := hkfd
  haveI : NumberField k := ⟨⟩
  choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes =>
    GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz
  have hgram := GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli
  have hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hmean₁ := flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom
    (fun σ => Real.log (n₁ σ))
  have hmean₀ := flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom
    (fun σ => Real.log (n₀ σ))
  have hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite := by
    apply hgram.2.subset
    intro ℓ hℓ hloc
    obtain ⟨j, hj⟩ := hℓ
    exact hj (ht2 ℓ hloc j)
  have key := GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ))
    (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det
    (H.rt : E) D.p D.q H.d
    (fun s => n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
    (fun s => n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
    (x true) t (fun ℓ => IsCMField.complexConj E (t ℓ))
    hr0 hgram.1 (Nat.Prime.pos H.d_prime) hrt2
    (by rw [neg_div, hmean₁, ← hm₁]; rfl)
    (by rw [neg_div, hmean₀, ← hx, ← hm₀]; rfl)
    (fun s => GlobalTheory.T.frame_function_cm_number_field E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r s
      (n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
      (n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
      (N.inf (s.comp (IntermediateField.inclusion hc).toRingHom))
      hty hrt mem line hli hcm hr0 hrz
      (hn₁ _).1 (hn₀ _).1 (((hn₁ _).2 _).mpr rfl) (((hn₀ _).2 _).mpr rfl)
      (hNinf _))
    (fun ℓ => flatDegree_sum_conj (fun z : ℂ_[ℓ] => Real.log ‖z‖) (t ℓ))
    (fun ℓ j => ht1 ℓ j) hfinite
    (fun ℓ j => ht3 ℓ j _ (hNfin ℓ (j.comp (IntermediateField.inclusion hc).toRingHom)))
  obtain ⟨hAd, hdeg⟩ := key
  obtain ⟨hdeg', hAd'⟩ := GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k)
    (IntermediateField.inclusion hc).toRingHom N
  refine ⟨hAd'.mp hAd, ?_⟩
  rw [← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | exact GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatDegree <;> assumption)
end
