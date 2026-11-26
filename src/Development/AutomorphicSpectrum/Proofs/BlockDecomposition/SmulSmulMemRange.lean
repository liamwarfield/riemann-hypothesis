module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulSmulMemRange
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem smul_smul_mem_range {A B D K₁ K₀ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup D] [Module A D] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (ρ : B →ₗ[A] D) (hρ : Function.Surjective ρ) (h1 : ρ 1 = 0) (d : K₁ →ₗ[A] K₀) (s : A)
    (hGood : ∀ x : D ⊗[A] K₁, d.lTensor D x = 0 →
      ∃ v : D ⊗[A] LinearMap.ker d, (LinearMap.ker d).subtype.lTensor D v = s • x)
    (hK₁ : ∀ w : B ⊗[A] K₁, ρ.rTensor K₁ w = 0 → ∃ a : K₁, w = (1 : B) ⊗ₜ[A] a)
    (hK₀ : ∀ a : K₀, (1 : B) ⊗ₜ[A] a = 0 → s • a = 0)
    (z : K₀) (w : B ⊗[A] K₁) (hw : (1 : B) ⊗ₜ[A] z = d.lTensor B w) :
    s • s • z ∈ LinearMap.range d := by
  have comm₁ : ∀ t : B ⊗[A] K₁, d.lTensor D (ρ.rTensor K₁ t) = ρ.rTensor K₀ (d.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₂ : ∀ t : B ⊗[A] LinearMap.ker d,
      (LinearMap.ker d).subtype.lTensor D (ρ.rTensor _ t)
        = ρ.rTensor K₁ ((LinearMap.ker d).subtype.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have dker : ∀ t : B ⊗[A] LinearMap.ker d,
      d.lTensor B ((LinearMap.ker d).subtype.lTensor B t) = 0 := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  have hw' : d.lTensor D (ρ.rTensor K₁ w) = 0 := by
    rw [comm₁, ← hw]; simp [h1]
  obtain ⟨v', hv'⟩ := hGood _ hw'
  obtain ⟨v, rfl⟩ := LinearMap.rTensor_surjective (LinearMap.ker d) hρ v'
  obtain ⟨u, hu⟩ := hK₁ (s • w - (LinearMap.ker d).subtype.lTensor B v) (by
    rw [map_sub, map_smul, ← comm₂, hv', sub_self])
  have key : (1 : B) ⊗ₜ[A] (d u - s • z) = 0 := by
    have := congrArg (d.lTensor B) hu
    rw [map_sub, map_smul, dker, sub_zero, ← hw, LinearMap.lTensor_tmul] at this
    rw [TensorProduct.tmul_sub, ← this, TensorProduct.tmul_smul, sub_self]
  have h := hK₀ _ key
  refine ⟨s • u, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at h
  exact h

theorem pow_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    {p : ℕ} (hp : 2 ≤ p) (s : A) (z : M) (h : s • s • z ∈ N) : s ^ p • z ∈ N := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have : s ^ (2 + q) • z = s ^ q • s • s • z := by
    simp only [smul_smul]; congr 1; ring
  rw [this]
  exact N.smul_mem _ h

theorem mv_cov : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ : B →ₗ[A] D), IsRt p r → Pf p D → Function.Surjective ρ → ρ 1 = 0 → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ w : B ⊗[A] K, ρ.rTensor K w = 0 → ∃ a : K, w = (1 : B) ⊗ₜ[A] a) → Cov p r B := by
  intro p _ A _ B _ _ D _ _ r ρ hr hD hρ h1 hK K₁ K₀ _ _ _ _ hp₁ hp₀ d hG z hz k
  obtain ⟨w, hw⟩ := hz
  have hmem : r (k + 1) • r (k + 1) • z ∈ LinearMap.range d :=
    smul_smul_mem_range ρ hρ h1 d (r (k + 1))
      (fun x hx => by
        obtain ⟨v, hv⟩ := hG D hD x hx (k + 1)
        exact ⟨v, hv⟩)
      (hK K₁ hp₁).2
      (fun a ha => (hK K₀ hp₀).1 a ha (k + 1))
      z w hw.symm
  rw [← hr k]
  exact pow_smul_mem _ (Fact.out : p.Prime).two_le _ _ hmem

end GlobalTheory.CompanionTheory.SnakeCov
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss
noncomputable section

namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz

variable {m n : ℕ}

def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth

theorem eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)

def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))

theorem norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

theorem exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid m n)
    (GroundTheory.Global.gaussianSchwartz (PiLp 2 (fun _ : Fin m × Fin n => ℂ))), fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_toEuclid_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem exists_schwartz_poly_mul_gauss (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
        Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := exists_gauss (m := m) (n := n)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => coord k u) P) g, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (eval_temperate P), hg, smul_eq_mul]
  rfl

end GlobalTheory.CompanionTheory.PolyGaussSchwartz
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotient
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.RootsUpToUnits

theorem subsingleton_of_mul_eq_one {S : Type} [CommRing S] {ϖ c : S}
    (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (h : ϖ * c = 1) : Subsingleton S := by
  have hu := (Ideal.mem_jacobson_bot.mp hJ) (-c)
  rw [mul_neg, h, neg_add_cancel] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

theorem normal_form {S : Type} [CommRing S] (ϖ : S) (h : ∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) (f : S) (M : ℕ) :
    ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  induction M generalizing f with
  | zero => left; simp
  | succ M ih =>
    rcases h f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', rfl, hf'⟩
      · left; rw [pow_succ']; exact mul_dvd_mul_left ϖ hg
      · right; exact ⟨j + 1, f', by ring, hf'⟩
    · right; exact ⟨0, f, by simp, hf⟩

theorem root_of_dvd {S : Type} [CommRing S] {ϖ g : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hA : Aic (S := S ⧸ Ideal.span {ϖ ^ 2})) (hg : g ∣ ϖ) {i : ℕ} (hi : 0 < i) :
    ∃ (r : S) (u : Sˣ), g = u * r ^ i := by
  obtain ⟨h, hh⟩ := hg
  by_cases hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})
  · haveI := hn
    obtain ⟨x, hx⟩ := hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g))
      (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hi)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0 := by
      simpa using hx
    have hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact hx'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hu := (Ideal.mem_jacobson_bot.mp hJ) (t * h)
    have key : r ^ i = g * (ϖ * (t * h) + 1) := by
      have e1 : r ^ i = g + t * ϖ ^ 2 := by rw [ht]; ring
      rw [e1, hh]; ring
    refine ⟨r, hu.unit⁻¹, ?_⟩
    rw [key]
    calc g = ((↑hu.unit⁻¹ : S) * (ϖ * (t * h) + 1)) * g := by rw [hu.val_inv_mul, one_mul]
      _ = (↑hu.unit⁻¹ : S) * (g * (ϖ * (t * h) + 1)) := by ring
  · have hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2}) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)
    exact ⟨1, 1, Subsingleton.elim _ _⟩

theorem roots_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  intro S _ ϖ hJ hϖ hD hA f N i hf hi
  have hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ := fun g =>
    hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩
  rcases normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩
  · obtain ⟨k, hk⟩ := dvd_trans hM hf
    have e0 : (1 - ϖ * k) * ϖ ^ N = 0 := by linear_combination hk
    have e1 : 1 - ϖ * k = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  · obtain ⟨r0, u0, h0⟩ := root_of_dvd hJ hA (dvd_refl ϖ) hi
    obtain ⟨r, u, hr⟩ := root_of_dvd hJ hA hf' hi
    refine ⟨r0 ^ j * r, u0 ^ j * u, ?_⟩
    rw [hr, h0]; push_cast; ring

end GlobalTheory.CompanionTheory.RootsUpToUnits
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotientStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_roots_of_closed_quotient : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  first | exact @GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | exact GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | (intros; apply GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValIntClosed

theorem exists_eq_of_isIntegral : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  intro S _ ϖ hϖ hV x hx
  obtain ⟨P, hm, hP⟩ := hx
  obtain ⟨N, f, hf⟩ := IsLocalization.Away.surj ϖ x
  set a := algebraMap S (Localization.Away ϖ) with ha
  have hinj : Function.Injective a :=
    IsLocalization.injective (Localization.Away ϖ) (Submonoid.powers_le.2 hϖ)
  have hwnz : ϖ ^ N ∈ nonZeroDivisors S := pow_mem hϖ N
  have hwu : IsUnit (a (ϖ ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).pow N
  obtain ⟨e, he, ⟨b, hb⟩, ⟨h, hh⟩⟩ := (by
    obtain ⟨e, he, h1, h2⟩ := hV f (ϖ ^ N) ⟨N, Ideal.subset_span (by simp)⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩ :
      ∃ e : S, IsIdempotentElem e ∧ ϖ ^ N ∣ e * f ∧ f ∣ (1 - e) * ϖ ^ N)
  set u := 1 - e with hu
  have hui : IsIdempotentElem u := he.one_sub
  set d := P.natDegree with hd

  have hhx : a h * x = a u := by
    apply hwu.mul_left_cancel
    calc a (ϖ ^ N) * (a h * x) = a h * (x * a (ϖ ^ N)) := by ring
      _ = a h * a f := by rw [map_pow, hf]
      _ = a u * a (ϖ ^ N) := by rw [← map_mul, ← map_mul, hh]; ring_nf
      _ = a (ϖ ^ N) * a u := by ring
  have hUi : a u * a u = a u := by rw [← map_mul, hui.eq]
  have hUp : ∀ i : ℕ, a u * a u ^ i = a u := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hUi]
  set k : S := ∑ i ∈ Finset.range d, P.coeff i * h ^ (d - 1 - i) with hk
  have hrel : a (u * (1 + h * k)) = 0 := by
    have h0 : a u * a h ^ d * Polynomial.eval₂ a x P = 0 := by
      have : Polynomial.eval₂ a x P = 0 := hP
      rw [this, mul_zero]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum] at h0
    have hlead : P.coeff d = 1 := hm
    have t1 : a u * a h ^ d * (a (P.coeff d) * x ^ d) = a u := by
      rw [hlead, map_one, one_mul, mul_assoc, ← mul_pow, hhx, hUp]
    have t2 : ∀ i ∈ Finset.range d, a u * a h ^ d * (a (P.coeff i) * x ^ i)
        = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
      intro i hi
      have hi' : i < d := Finset.mem_range.1 hi
      have hd' : d = i + (1 + (d - 1 - i)) := by omega
      have : a h ^ d = a h ^ i * (a h * a h ^ (d - 1 - i)) := by
        conv_lhs => rw [hd', pow_add, pow_add, pow_one]
      rw [this]
      calc a u * (a h ^ i * (a h * a h ^ (d - 1 - i))) * (a (P.coeff i) * x ^ i)
          = (a u * (a h * x) ^ i) * (a h * (a (P.coeff i) * a h ^ (d - 1 - i))) := by
            rw [mul_pow]; ring
        _ = a u * (a h * a (P.coeff i * h ^ (d - 1 - i))) := by
            rw [hhx, hUp, map_mul, map_pow]
    rw [t1, Finset.sum_congr rfl t2, ← Finset.mul_sum, ← Finset.mul_sum] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_add (f := _), map_one, map_mul, hk, map_sum]
    rw [mul_add, mul_one, add_comm]
    exact h0
  have hrel' : u * (1 + h * k) = 0 := hinj (by rw [hrel, map_zero])
  have hu' : u = - (u * h * k) := by linear_combination hrel'
  have hdiv : ϖ ^ N ∣ f := by
    have hfe : f = e * f + u * f := by rw [hu]; ring
    have huf : u * f = ϖ ^ N * (-(k * u)) := by
      calc u * f = - (u * h * k) * f := by rw [← hu']
        _ = - (k * u * (f * h)) := by ring
        _ = - (k * u * (u * ϖ ^ N)) := by rw [hh]
        _ = - (k * (u * u) * ϖ ^ N) := by ring
        _ = ϖ ^ N * (-(k * u)) := by rw [hui.eq]; ring
    exact ⟨b + -(k * u), by rw [hfe, hb, huf]; ring⟩
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨y, ?_⟩
  apply hwu.mul_left_cancel
  rw [← map_mul, ← hy, ← hf, map_pow, mul_comm]

end GlobalTheory.CompanionTheory.ValIntClosed
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRingStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localization_away_in_ring : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  first | exact @GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | exact GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | (intros; apply GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftIdempotentAdicComplete
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.IdemLift

theorem sub_pow_three_eq {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : (a - b) ^ 3 = a - b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'

theorem eq_of_isNilpotent_sub {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : IsNilpotent (a - b)) : a = b := by
  obtain ⟨n, hn⟩ := h
  have h3 := sub_pow_three_eq ha hb
  have hpow : ∀ m : ℕ, (a - b) ^ (2 * m + 1) = a - b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (a - b) ^ (2 * (m + 1) + 1) = (a - b) ^ (2 * m + 1) * (a - b) ^ 2 := by ring
        _ = (a - b) ^ 3 := by rw [ih]; ring
        _ = a - b := h3
  have h0 : a - b = 0 := by
    rw [← hpow n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]
  exact sub_eq_zero.1 h0

theorem eq_of_sub_mem_jacobson {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a - b ∈ Ideal.jacobson (⊥ : Ideal R)) : a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h3 := sub_pow_three_eq ha hb
  have hz : (a - b) * ((a - b) * (-(a - b)) + 1) = 0 := by
    linear_combination -h3
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hz)

theorem existsUnique_idempotent_lift {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (k : ℕ) (hk : k ≠ 0)
    (e : S ⧸ Ideal.span {ϖ ^ k}) (he : IsIdempotentElem e) :
    ∃! e' : S, IsIdempotentElem e' ∧ Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) e' = e := by
  have hJI : Ideal.span {ϖ ^ k} ≤ Ideal.span {ϖ} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self ϖ hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  have haJ : a * a - a ∈ Ideal.span {ϖ ^ k} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    have he' : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) a * Ideal.Quotient.mk _ a
        = Ideal.Quotient.mk _ a := he
    rw [map_sub, map_mul, he', sub_self]
  have haI : a * a - a ∈ Ideal.span {ϖ} := hJI haJ
  have hH : HenselianRing S (Ideal.span {ϖ}) := IsAdicComplete.henselianRing S _
  have hmon : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).Monic := by
    apply Polynomial.monic_X_pow_sub
    simpa using lt_of_le_of_lt Polynomial.degree_X_le (by norm_num : (1 : WithBot ℕ) < 2)
  have heval : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a ∈ Ideal.span {ϖ} := by
    have : ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X).eval a = a * a - a := by
      simp [sq]
    rwa [this]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ})
      (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X) |>.eval a)) := by
    have hd : (Polynomial.derivative ((Polynomial.X : Polynomial S) ^ 2 - Polynomial.X)).eval a
        = 2 * a - 1 := by
      simp
      ring
    rw [hd]
    have hsq : Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1)
        * Ideal.Quotient.mk (Ideal.span {ϖ}) (2 * a - 1) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ}))]
      apply Ideal.Quotient.eq.2
      have : (2 * a - 1) * (2 * a - 1) - 1 = 4 * (a * a - a) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ haI
    exact IsUnit.of_mul_eq_one _ hsq
  obtain ⟨y, hy, hya⟩ := hH.is_henselian _ hmon a heval hunit
  have hyid : IsIdempotentElem y := by
    have : y ^ 2 - y = 0 := by simpa [Polynomial.IsRoot] using hy
    have h2 : y * y - y = 0 := by rw [← sq]; exact this
    exact sub_eq_zero.1 h2
  have hlift : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) y = Ideal.Quotient.mk _ a := by
    apply eq_of_isNilpotent_sub (hyid.map (Ideal.Quotient.mk _)) he
    refine ⟨k, ?_⟩
    rw [← map_sub, ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hya
    rw [hc, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨y, ⟨hyid, hlift⟩, ?_⟩
  rintro z ⟨hz, hza⟩
  apply eq_of_sub_mem_jacobson hz hyid
  apply IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ})
  apply hJI
  apply Ideal.Quotient.eq.1
  rw [hza, hlift]

end GlobalTheory.CompanionTheory.IdemLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistence
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonSlope

theorem exists_dvd_all {S ι : Type} [CommRing S] (T : Finset ι) (hT : T.Nonempty) (r : ι → S)
    (hc : ∀ i ∈ T, ∀ j ∈ T, r i ∣ r j ∨ r j ∣ r i) :
    ∃ i₀ ∈ T, ∀ j ∈ T, r j ∣ r i₀ := by
  classical
  revert hT hc
  refine Finset.induction_on T ?_ ?_
  · intro hT
    exact absurd hT Finset.not_nonempty_empty
  · intro a s ha ih hT hc
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_refl _
      · exact absurd hj (Finset.notMem_empty j)
    · obtain ⟨i₀, hi₀, hmax⟩ := ih hs (fun i hi j hj =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      rcases hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h
      · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact (hmax j hj).trans h

theorem dich_of_dvd {S : Type} [CommRing S] {ϖ : S} (hD : Dich ϖ) {a b : S} {M : ℕ}
    (h : a ∣ ϖ ^ M) : b ∣ a ∨ a ∣ b := by
  obtain ⟨k, hk⟩ := h
  refine hD a b ⟨M, ?_⟩
  rw [hk]
  exact Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))

theorem first_slope : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ),
    0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧
      ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  intro S _ ϖ hD hR q d M hd hqd h0
  classical
  have hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ q j ∣ q 0
    · obtain ⟨t, ht⟩ := hj.2
      have htd : t ∣ ϖ ^ M := (Dvd.intro_left (q j) ht.symm).trans h0
      obtain ⟨r, u, hru⟩ := hR t M j htd (by omega)
      exact ⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose s hs using hex
  set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef
  have hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0 := by
    intro j
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc]
  have hdT : d ∈ T := (hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩
  have hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M := by
    intro j hj
    obtain ⟨⟨hj1, _⟩, hjq⟩ := (hmemT j).mp hj
    obtain ⟨u, hu⟩ := hs j hj1 hjq
    have h1 : s j ^ j ∣ q 0 := ⟨q j * ↑u, by rw [hu]; ring⟩
    exact ((dvd_pow_self (s j) (by omega)).trans h1).trans h0
  have hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i := by
    intro i hi j _
    exact (dich_of_dvd hD (b := s j) (hsdvd i hi)).symm
  obtain ⟨i₀, hi₀T, hmax⟩ := exists_dvd_all T ⟨d, hdT⟩ s hcomp
  obtain ⟨⟨hi₀1, hi₀d⟩, hi₀q⟩ := (hmemT i₀).mp hi₀T
  refine ⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩
  · intro i hi1 hid
    rcases dich_of_dvd hD (b := q i) h0 with h | h
    · have hiT : i ∈ T := (hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩
      obtain ⟨u, hu⟩ := hs i hi1 h
      have h2 : q 0 ∣ q i * s i ^ i := by
        rw [hu, mul_left_comm, Units.mul_left_dvd]
      obtain ⟨k, hk⟩ := hmax i hiT
      exact h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩
    · exact dvd_mul_of_dvd_left h _
  · obtain ⟨u, hu⟩ := hs i₀ hi₀1 hi₀q
    exact ⟨↑u, by rw [hu]; ring⟩

end GlobalTheory.CompanionTheory.NewtonSlope
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistenceStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_polygon_slope_existence : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ), 0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧ ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  first | exact @GlobalTheory.CompanionTheory.NewtonSlope.first_slope | exact GlobalTheory.CompanionTheory.NewtonSlope.first_slope | (intros; apply GlobalTheory.CompanionTheory.NewtonSlope.first_slope <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Iwa
noncomputable def UpperTheory.Reformulated.B.DYhc7.Iwa :
    {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → Prop :=
    fun {G : Type} [Group G] (P K : Subgroup G) ↦ ∀ (g : G), ∃ p ∈ P, ∃ k ∈ K, g = p * k

theorem UpperTheory.Reformulated.B.DYhc7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {K P : Subgroup G},
      IsCompact (↑K : Set G) →
        IsClosed (↑P : Set G) →
          UpperTheory.Reformulated.B.DYhc7.Iwa P K → Topology.IsQuotientMap fun (x : ↥P × ↥K) ↦ (↑x.1 : G) * (↑x.2 : G) := by
  intro G _ _ _ K P hK hP hI
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h : G × K ≃ₜ G × K :=
    { toFun := fun y => (y.1 * (y.2 : G), y.2)
      invFun := fun y => (y.1 * (y.2 : G)⁻¹, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : P → G) (id : K → K)) :=
    hP.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  have hcl : IsClosedMap (fun x : ↥P × ↥K ↦ (x.1 : G) * (x.2 : G)) := by
    have h1 : IsClosedMap (Prod.fst : G × K → G) := isClosedMap_fst_of_compactSpace
    exact h1.comp (h.isClosedMap.comp hι.isClosedMap)
  refine hcl.isQuotientMap (by fun_prop) ?_
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisSec

variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI

theorem sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by
  have h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P := ⟨k, by simpa using hp⟩
  rw [sec, dite_eq_left h]
  obtain ⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose := ⟨_, rfl⟩
  have h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P := hk0 ▸ h.choose_spec
  rw [← hk0]
  have hr : ((k0 * k⁻¹ : K) : G) ∈ P := by
    have : ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p := by simp [mul_assoc]
    rw [this]
    exact P.mul_mem (P.inv_mem h0) hp
  have hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w := hw _ hr
  have hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G) := by
    rw [← hch.mul _ h0 _ hr]
    congr 1
    simp [mul_assoc]
  have hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹) := by
    rw [← map_mul]
    congr 1
    simp
  calc (c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹) w
      = c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹ (c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w) := by
        rw [hrw]; rfl
    _ = c p • ρ k⁻¹ w := by
        rw [hcp, hρ, map_smul, mul_smul]; rfl

theorem sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)

theorem sec_bound {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dite_eq_left h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))

theorem secLaw : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩

end GlobalTheory.CompanionTheory.RgEisSec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_law_holds : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulProdCongr
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.RootNear

theorem mul_prod_congr {B ι : Type} [CommRing B] (u : B) (x y : ι → B) (S : Finset ι)
    (h : ∀ j ∈ S, u * x j = u * y j) : u * ∏ j ∈ S, x j = u * ∏ j ∈ S, y j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : u * x a = u * y a := h a (Finset.mem_insert_self a s)
    have h2 : u * ∏ j ∈ s, x j = u * ∏ j ∈ s, y j :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc u * (x a * ∏ j ∈ s, x j) = (u * x a) * ∏ j ∈ s, x j := by ring
      _ = (u * y a) * ∏ j ∈ s, x j := by rw [h1]
      _ = y a * (u * ∏ j ∈ s, x j) := by ring
      _ = y a * (u * ∏ j ∈ s, y j) := by rw [h2]
      _ = u * (y a * ∏ j ∈ s, y j) := by ring

theorem exists_shift {B ι : Type} [CommRing B] (I : Ideal B) (c f : ι → B) (S : Finset ι)
    (hf : ∀ j ∈ S, IsIdempotentElem (f j)) (hc : ∀ j ∈ S, f j * c j ∈ I) :
    ∃ s ∈ I, (∏ j ∈ S, (1 - f j)) ∣ ∏ j ∈ S, (c j - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, htI, hdvd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hfa : f a * f a = f a := hf a (Finset.mem_insert_self a s)
    have hca : f a * c a ∈ I := hc a (Finset.mem_insert_self a s)
    refine ⟨(1 - f a) * t + f a * c a, I.add_mem (I.mul_mem_left _ htI) hca, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcong : (1 - f a) * ∏ j ∈ s, (c j - ((1 - f a) * t + f a * c a)) =
        (1 - f a) * ∏ j ∈ s, (c j - t) :=
      mul_prod_congr (1 - f a) _ _ s (fun j _ => by linear_combination (c a - t) * hfa)
    have hfirst : c a - ((1 - f a) * t + f a * c a) = (1 - f a) * (c a - t) := by ring
    rw [hfirst, mul_comm (1 - f a) (c a - t), mul_assoc, hcong]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left (1 - f a) hdvd) _

theorem root_near (B : Type) [CommRing B] (π : B) (hπ : π ∈ nonZeroDivisors B) (hV : VAL π)
    (d M : ℕ) (b : Fin d → B) (a : B) (hd : 0 < d)
    (hprod : ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)}) :
    ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := by
  classical
  have key : ∀ j : Fin d, ∃ e : B, IsIdempotentElem e ∧ e * (a - b j) ∈ Ideal.span {π ^ M} ∧
      (1 - e) * π ^ M ∈ Ideal.span {a - b j} := fun j =>
    hV (a - b j) (π ^ M) ⟨M, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  choose e he1 he2 he3 using key
  have hee : ∀ j, e j * e j = e j := fun j => he1 j
  have hr : ∀ j, ∃ r : B, (1 - e j) * π ^ M = (a - b j) * r := fun j =>
    Ideal.mem_span_singleton.mp (he3 j)
  choose r hr using hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨j0, -⟩ : ∃ j : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨E, hEdef⟩ : ∃ E : B, E = ∏ j, (1 - e j) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hEdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by linear_combination hee j)
  have hEj : ∀ j, E * (1 - e j) = E := by
    intro j
    have hsplit : (1 - e j) * ∏ i ∈ Finset.univ.erase j, (1 - e i) = E := by
      rw [hEdef]; exact Finset.mul_prod_erase _ (fun i => 1 - e i) (Finset.mem_univ j)
    rw [← hsplit]
    linear_combination (∏ i ∈ Finset.univ.erase j, (1 - e i)) * hee j
  have hT : ∀ j, (a - b j) * (E * r j) = E * π ^ M := by
    intro j
    calc (a - b j) * (E * r j) = E * ((a - b j) * r j) := by ring
      _ = E * ((1 - e j) * π ^ M) := by rw [← hr j]
      _ = (E * (1 - e j)) * π ^ M := by ring
      _ = E * π ^ M := by rw [hEj j]
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hEE]
  have hEd : E ^ d = E := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', hEpow]
  have hmain : π ^ (d * M) * (q * ∏ j, (E * r j)) = π ^ (d * M) * E := by
    calc π ^ (d * M) * (q * ∏ j, (E * r j)) = (∏ j, (a - b j)) * ∏ j, (E * r j) := by
          rw [hq]; ring
      _ = ∏ j, ((a - b j) * (E * r j)) := Finset.prod_mul_distrib.symm
      _ = ∏ _j : Fin d, (E * π ^ M) := Finset.prod_congr rfl (fun j _ => hT j)
      _ = π ^ (d * M) * E := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, hEd, ← pow_mul,
            mul_comm M d]
          ring
  have hpow : π ^ (d * M) ∈ nonZeroDivisors B := pow_mem hπ _
  have hET : E = q * ∏ j, (E * r j) := by
    have h0 : (q * ∏ j, (E * r j) - E) * π ^ (d * M) = 0 := by linear_combination hmain
    exact (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpow).2 _ h0)).symm
  have hEa : E * (a - b j0) ∈ Ideal.span {π ^ M} := by
    rw [Ideal.mem_span_singleton]
    have hsplit : (E * r j0) * ∏ i ∈ Finset.univ.erase j0, (E * r i) = ∏ i, (E * r i) :=
      Finset.mul_prod_erase _ (fun i => E * r i) (Finset.mem_univ j0)
    refine ⟨q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E, ?_⟩
    calc E * (a - b j0) = q * (∏ i, (E * r i)) * (a - b j0) := by rw [← hET]
      _ = q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * ((a - b j0) * (E * r j0)) := by
          rw [← hsplit]; ring
      _ = π ^ M * (q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E) := by rw [hT j0]; ring
  obtain ⟨s, hs, w, hw⟩ := exists_shift (Ideal.span {π ^ M}) (fun j => a - b j) e Finset.univ
    (fun j _ => he1 j) (fun j _ => he2 j)
  have hw' : ∏ j, (a - b j - s) = E * w := by rw [hEdef]; exact hw
  obtain ⟨a₁, ha₁⟩ : ∃ x : B, x = (1 - E) * (a - s) + E * b j0 := ⟨_, rfl⟩
  refine ⟨a₁, ?_, ?_⟩
  · have h1 : a₁ - a = (E - 1) * s - E * (a - b j0) := by rw [ha₁]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hs) hEa
  · have hsplit2 : (a₁ - b j0) * ∏ i ∈ Finset.univ.erase j0, (a₁ - b i) = ∏ i, (a₁ - b i) :=
      Finset.mul_prod_erase _ (fun i => a₁ - b i) (Finset.mem_univ j0)
    have hE0 : E * ∏ i, (a₁ - b i) = 0 := by
      rw [← hsplit2]
      linear_combination E * (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * ha₁ +
        (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * (b j0 - (a - s)) * hEE
    have hcong : (1 - E) * ∏ i, (a₁ - b i) = (1 - E) * ∏ i, (a - b i - s) :=
      mul_prod_congr (1 - E) _ _ Finset.univ
        (fun j _ => by linear_combination (1 - E) * ha₁ + (a - s - b j0) * hEE)
    calc ∏ i, (a₁ - b i) = E * ∏ i, (a₁ - b i) + (1 - E) * ∏ i, (a₁ - b i) := by ring
      _ = 0 + (1 - E) * ∏ i, (a - b i - s) := by rw [hE0, hcong]
      _ = 0 := by rw [hw']; linear_combination (-w) * hEE

end GlobalTheory.CompanionTheory.RootNear
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormRpowTwoNeTop
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.SchurKernel

theorem lintegral_enorm_rpow_two_ne_top {α : Type} [MeasurableSpace α] {ν : Measure α} {g : α → ℂ}
    (hg : MemLp g 2 ν) : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    hg.eLpNorm_lt_top
  simpa using h.ne

theorem schurInt_of_schurL : SchurL → SchurInt := by
  intro hS α _ ν _ k A hk hA hrow hcol g f hg hf
  have hkm : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (ν.prod ν) :=
    hk.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun p : α × α => g p.1) (ν.prod ν) := hg.aestronglyMeasurable.comp_fst
  have hfm : AEStronglyMeasurable (fun p : α × α => f p.2) (ν.prod ν) := hf.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (fun p : α × α => g p.1 * k p.1 p.2 * f p.2) (ν.prod ν) :=
    (hgm.mul hkm).mul hfm
  refine ⟨hm, ?_⟩
  set K : α → α → ℝ≥0∞ := fun x y => ‖k x y‖ₑ with hK
  have hKm : Measurable (Function.uncurry K) := hk.enorm
  have hFm : AEMeasurable (fun y => ‖f y‖ₑ) ν := hf.aestronglyMeasurable.aemeasurable.enorm
  set h : α → ℝ≥0∞ := fun x => ∫⁻ y, K x y * ‖f y‖ₑ ∂ν with hh
  have hprod : AEMeasurable (fun p : α × α => K p.1 p.2 * ‖f p.2‖ₑ) (ν.prod ν) :=
    hKm.aemeasurable.mul hfm.enorm
  have hhm : AEMeasurable h ν := hprod.lintegral_prod_right'
  have hsch : ∫⁻ x, h x ^ 2 ∂ν ≤ A ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν :=
    hS α ν K A (fun y => ‖f y‖ₑ) hKm hFm hrow hcol
  have heq : ∫⁻ p, ‖g p.1 * k p.1 p.2 * f p.2‖ₑ ∂(ν.prod ν) = ∫⁻ x, ‖g x‖ₑ * h x ∂ν := by
    rw [lintegral_prod _ hm.enorm]
    refine lintegral_congr fun x => ?_
    simp only [hh, hK]
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_congr fun y => ?_
    simp only [enorm_mul, mul_assoc]
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two)
    hg.aestronglyMeasurable.aemeasurable.enorm hhm
  have hG : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := lintegral_enorm_rpow_two_ne_top hg
  have hF : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := lintegral_enorm_rpow_two_ne_top hf
  have hH : ∫⁻ x, h x ^ (2 : ℝ) ∂ν ≠ ⊤ := by
    simp only [ENNReal.rpow_two] at hF ⊢
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) hF) hsch
  rw [HasFiniteIntegral, heq]
  refine lt_of_le_of_lt hhold (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hH

end GlobalTheory.CompanionTheory.SchurKernel
end
