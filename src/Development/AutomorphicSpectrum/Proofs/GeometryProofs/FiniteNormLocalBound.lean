module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnits
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.Conj

open UniformSpace Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem exists_padicAlgCl_factor {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ_[p]) :
    ∃ φ : K →+* PadicAlgCl p, ∀ a, ((φ a : PadicAlgCl p) : ℂ_[p]) = κ a := by
  let j : PadicAlgCl p →+* ℂ_[p] := UniformSpace.Completion.coeRingHom
  have hjinj : Function.Injective j := j.injective
  let _ : Algebra (PadicAlgCl p) ℂ_[p] := j.toAlgebra
  have hmem : ∀ a : K, ∃ y, j y = κ a := by
    intro a
    have ha : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
    have hκ : aeval (κ a) (minpoly ℚ a) = κ (aeval a (minpoly ℚ a)) :=
      Polynomial.aeval_algHom_apply κ.toRatAlgHom a _
    have hint : IsIntegral (PadicAlgCl p) (κ a) := by
      refine ⟨(minpoly ℚ a).map (algebraMap ℚ (PadicAlgCl p)), (minpoly.monic ha).map _, ?_⟩
      rw [eval₂_map]
      have hc : (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℚ (PadicAlgCl p)) =
          algebraMap ℚ ℂ_[p] := RingHom.ext_rat _ _
      rw [hc, ← aeval_def, hκ, minpoly.aeval, map_zero]
    exact RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (PadicAlgCl p) (κ a)
      (IsAlgClosed.degree_eq_one_of_irreducible (PadicAlgCl p) (minpoly.irreducible hint)))
  choose f hf using hmem
  refine ⟨{ toFun := f
            map_one' := hjinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hjinj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hjinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hjinj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, fun a => hf a⟩

theorem norm_aeval_monomial_sub (x : PadicAlgCl p) (n : ℕ) (r : ℚ) (c : ℚ_[p]) :
    ‖aeval x (monomial n r) - aeval x (monomial n c)‖ = ‖(r : ℚ_[p]) - c‖ * ‖x‖ ^ n := by
  rw [aeval_monomial, aeval_monomial, ← sub_mul, norm_mul, norm_pow,
    eq_ratCast (algebraMap ℚ (PadicAlgCl p)) r,
    ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r, ← map_sub, PadicAlgCl.norm_extends]

theorem exists_rat_poly_approx (x y : PadicAlgCl p) (e : ℚ_[p][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℚ[X], ‖aeval x u - aeval x e‖ < ε ∧ ‖aeval y u - aeval y e‖ < ε := by
  obtain ⟨N, hN⟩ : ∃ N, e.natDegree < N := ⟨_, Nat.lt_succ_self _⟩
  have hSx : 0 ≤ ∑ i ∈ Finset.range N, ‖x‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  have hSy : 0 ≤ ∑ i ∈ Finset.range N, ‖y‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδx, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ∑ i ∈ Finset.range N, ‖x‖ ^ i < ε ∧
      δ * ∑ i ∈ Finset.range N, ‖y‖ ^ i < ε := by
    have hD : 0 < ∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1 := by linarith
    refine ⟨ε / (∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1),
      div_pos hε hD, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSy]
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSx]
  have hr' : ∀ i, ∃ r : ℚ, ‖e.coeff i - (r : ℚ_[p])‖ < δ := fun i => Padic.rat_dense p (e.coeff i) hδ0
  choose r hr using hr'
  have key : ∀ z : PadicAlgCl p, ‖aeval z (∑ i ∈ Finset.range N, monomial i (r i)) - aeval z e‖ ≤
      δ * ∑ i ∈ Finset.range N, ‖z‖ ^ i := by
    intro z
    conv_lhs => rw [e.as_sum_range' N hN]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_aeval_monomial_sub, norm_sub_rev]
    exact mul_le_mul_of_nonneg_right (hr i).le (by positivity)
  exact ⟨_, (key x).trans_lt hδx, (key y).trans_lt hδy⟩

theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem minpoly_eq_of_unit_ball {K : Type} [Field K] [NumberField K] (φ ψ : K →+* PadicAlgCl p)
    (h : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1) (θ : K) :
    minpoly ℚ_[p] (φ θ) = minpoly ℚ_[p] (ψ θ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm : ∀ (χ : K →+* PadicAlgCl p) (j : ℕ), ‖χ ((p : K) ^ j)⁻¹‖ = ((p : ℝ)⁻¹ ^ j)⁻¹ := by
    intro χ j
    rw [map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_natCast_prime]
  have core : ∀ φ₁ ψ₁ : K →+* PadicAlgCl p, (∀ a, ‖φ₁ a‖ ≤ 1 → ‖ψ₁ a‖ ≤ 1) →
      aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) = 0 := by
    intro φ₁ ψ₁ h₁
    have hφ : ∀ v : ℚ[X], aeval (φ₁ θ) v = φ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply φ₁.toRatAlgHom θ v
    have hψ : ∀ v : ℚ[X], aeval (ψ₁ θ) v = ψ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply ψ₁.toRatAlgHom θ v
    by_contra hne
    have hz : 0 < ‖aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ))‖ := norm_pos_iff.mpr hne
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (half_pos hz) (inv_lt_one_of_one_lt₀ hp1)
    have ht : 0 < (p : ℝ)⁻¹ ^ j := pow_pos (inv_pos.mpr (by linarith)) j
    obtain ⟨u, hux, huy⟩ := exists_rat_poly_approx (φ₁ θ) (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) ht
    rw [minpoly.aeval, sub_zero, hφ] at hux
    have h1 : ‖φ₁ (((p : K) ^ j)⁻¹ * aeval θ u)‖ ≤ 1 := by
      rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one]
      exact hux.le
    have h2 := h₁ _ h1
    rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one, ← hψ] at h2
    have h4 := norm_sub_le (aeval (ψ₁ θ) u) (aeval (ψ₁ θ) u - aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)))
    rw [sub_sub_cancel] at h4
    linarith
  have hx : IsIntegral ℚ_[p] (φ θ) := Algebra.IsIntegral.isIntegral _
  have hy : IsIntegral ℚ_[p] (ψ θ) := Algebra.IsIntegral.isIntegral _
  have hPQ : minpoly ℚ_[p] (φ θ) ∣ minpoly ℚ_[p] (ψ θ) :=
    minpoly.dvd _ _ (core ψ φ fun a => (h a).mpr)
  refine minpoly.unique' ℚ_[p] (ψ θ) (minpoly.monic hx) (core φ ψ fun a => (h a).mp) fun q hq => ?_
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · refine Or.inr fun hqy => ?_
    have h3 := Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hqy) hq0
    have h4 := Polynomial.natDegree_le_of_dvd hPQ (minpoly.ne_zero hy)
    have h5 := Polynomial.natDegree_lt_natDegree hq0 hq
    omega

theorem exists_extension (σ : PadicAlgCl p ≃+* PadicAlgCl p) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧
      ∀ x : PadicAlgCl p, g (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) := by
  have hσs : ∀ x, ‖σ.symm x‖ = ‖x‖ := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  have hσi : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσ
  have hτi : Isometry σ.symm := AddMonoidHomClass.isometry_of_norm σ.symm hσs
  let F : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ : PadicAlgCl p →+* PadicAlgCl p) hσi.continuous
  let G : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ.symm : PadicAlgCl p →+* PadicAlgCl p) hτi.continuous
  have hF : ∀ x : PadicAlgCl p, F x = (σ x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hσi.continuous x
  have hG : ∀ x : PadicAlgCl p, G x = (σ.symm x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hτi.continuous x
  have hFc : Continuous F := UniformSpace.Completion.continuous_extension
  have hGc : Continuous G := UniformSpace.Completion.continuous_extension
  have hGF : ∀ z, G (F z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hGc.comp hFc) continuous_id) fun x => ?_
    rw [hF, hG, RingEquiv.symm_apply_apply]
  have hFG : ∀ z, F (G z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hFc.comp hGc) continuous_id) fun x => ?_
    rw [hG, hF, RingEquiv.apply_symm_apply]
  have hFn : ∀ z, ‖F z‖ = ‖z‖ := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (continuous_norm.comp hFc) continuous_norm) fun x => ?_
    rw [hF, PadicComplex.norm_extends, PadicComplex.norm_extends, hσ]
  refine ⟨{ toFun := fun z => F z
            invFun := fun z => G z
            left_inv := hGF
            right_inv := hFG
            map_mul' := map_mul F
            map_add' := map_add F }, hFn, hF⟩

theorem exists_isometry_conj_of_unit_ball (K : Type) [Field K] [NumberField K] (p : Nat.Primes)
    (κ κ' : K →+* ℂ_[p]) (h : ∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  obtain ⟨φ, hφ⟩ := exists_padicAlgCl_factor κ
  obtain ⟨ψ, hψ⟩ := exists_padicAlgCl_factor κ'
  have hb : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1 := fun a => by
    rw [← PadicComplex.norm_extends, ← PadicComplex.norm_extends, hφ, hψ]
    exact h a
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ K
  have hm := minpoly_eq_of_unit_ball φ ψ hb θ
  have : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal _ _
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).mp hm.symm)
  have hτ' : τ (φ θ) = ψ θ := by rw [← AlgEquiv.smul_def]; exact hτ
  have hτn : ∀ x, ‖τ.toRingEquiv x‖ = ‖x‖ := fun x => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_eq]
  obtain ⟨g, hgn, hg⟩ := exists_extension τ.toRingEquiv hτn
  have hv : ∀ v : ℚ[X], τ (φ (aeval θ v)) = ψ (aeval θ v) := by
    intro v
    have e1 : φ (aeval θ v) = aeval (φ θ) v := (Polynomial.aeval_algHom_apply φ.toRatAlgHom θ v).symm
    have e2 : ψ (aeval θ v) = aeval (ψ θ) v := (Polynomial.aeval_algHom_apply ψ.toRatAlgHom θ v).symm
    have e3 : τ (aeval (φ θ) v) = aeval (τ (φ θ)) v :=
      (Polynomial.aeval_algHom_apply (τ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).toRatAlgHom
        (φ θ) v).symm
    rw [e1, e2, e3, hτ']
  refine ⟨g, hgn, fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin ℚ {θ} := by
    rw [hθ]
    exact IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ a).mp ha
  have key : τ (φ a) = ψ a := by
    rw [hrs, map_div₀, map_div₀, map_div₀, hv, hv]
  rw [← hφ, ← hψ, hg]
  exact congrArg _ key

end GlobalTheory.CompanionTheory.Ar.Br.Conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_embeddings_conjugate_of_units : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (κ κ' : K →+* ℂ_[p]), (∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) → ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | exact GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br.FinPlace

section Valued

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {N : Type*} [NormedField N]

theorem val_lt_one_iff (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) (a : F) :
    v a < 1 ↔ ‖κ a‖ < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hv : 0 < v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha)
  have hn : 0 < ‖κ a‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr ha)
  have e := h a⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv, inv_le_one₀ hn] at e
  rw [← not_le, ← not_le, e]

theorem norm_le_of_val_le (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a ≤ v b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have hv : 0 < v b := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hb)
  have hn : 0 < ‖κ b‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr hb)
  have e := (h (a / b)).mp (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le)
  rw [map_div₀, norm_div] at e
  exact (div_le_one hn).mp e

theorem norm_eq_of_val_eq (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a = v b) : ‖κ a‖ = ‖κ b‖ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact (Valuation.ne_zero_iff v).mpr hb hab.symm
  exact le_antisymm (norm_le_of_val_le v κ h hb hab.le) (norm_le_of_val_le v κ h ha hab.ge)

end Valued

theorem norm_natCast_lt_one_iff (q : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[q])‖ < 1 ↔ (q : ℕ) ∣ n := by
  have e : ‖(n : ℂ_[q])‖ = ‖(n : ℚ_[q])‖ := by
    have h1 := PadicComplex.norm_extends (q : ℕ) ((n : ℚ_[q]) : PadicAlgCl q)
    have h2 := PadicAlgCl.norm_extends (q : ℕ) (n : ℚ_[q])
    simpa using h1.trans h2
  rw [e]
  exact Padic.norm_natCast_lt_one_iff

theorem prime_eq {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {p q : Nat.Primes} (κ : F →+* ℂ_[p]) (κ₀ : F →+* ℂ_[q]) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h₀ : ∀ a, v a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) : p = q := by
  have h1 : ‖κ ((p : ℕ) : F)‖ < 1 := by
    rw [map_natCast, norm_natCast_lt_one_iff]
  have h2 : ‖κ₀ ((p : ℕ) : F)‖ < 1 := (val_lt_one_iff v κ₀ h₀ _).mp ((val_lt_one_iff v κ h _).mpr h1)
  rw [map_natCast, norm_natCast_lt_one_iff] at h2
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h2).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem hasFinNorm_of_isometry {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {p : Nat.Primes}
    {κ κ' : c.F →+* ℂ_[p]} {t : ℝ} (g : ℂ_[p] ≃+* ℂ_[p]) (hg : ∀ z, ‖g z‖ = ‖z‖) (hκ : ∀ a, g (κ a) = κ' a)
    (h : HasFinNorm U τ φ p κ t) : HasFinNorm U τ φ p κ' t := by
  have hs : ∀ z, ‖g.symm z‖ = ‖z‖ := fun z => by
    rw [← hg (g.symm z), RingEquiv.apply_symm_apply]
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hF hv hw
  have e := h V K ((g.symm : ℂ_[p] →+* ℂ_[p]).comp j) β y v w T tK m m'
    (fun a => by
      rw [← hj a]
      simp only [RingHom.comp_apply, RingHom.coe_coe, hs])
    (by
      ext a
      have h1 : j (β a) = κ' a := by rw [← hjβ]; rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ← hκ, RingEquiv.symm_apply_apply]) hF hv hw
  simpa only [RingHom.comp_apply, RingHom.coe_coe, hs] using e

theorem exists_rho_at (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F]
    (hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t)
    (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ r : ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (π : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) →
      HasFinNorm U τ φ p κ (r * Real.log ‖κ π‖) := by
  by_cases hex : ∃ (p₀ : Nat.Primes) (κ₀ : c.F →+* ℂ_[p₀]) (π₀ : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) ∧ la.valuation c.F π₀ = WithZero.exp (-1 : ℤ)
  · obtain ⟨p₀, κ₀, π₀, hκ₀, hπ₀⟩ := hex
    obtain ⟨t₀, ht₀⟩ := hfin p₀ κ₀
    have hne : π₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ₀
      exact WithZero.exp_ne_zero hπ₀.symm
    have hlt : ‖κ₀ π₀‖ < 1 := (val_lt_one_iff _ κ₀ hκ₀ π₀).mp (by
      rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have hpos : 0 < ‖κ₀ π₀‖ := norm_pos_iff.mpr ((map_ne_zero κ₀).mpr hne)
    have hlog : Real.log ‖κ₀ π₀‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
    refine ⟨t₀ / Real.log ‖κ₀ π₀‖, fun p κ π hκ hπ => ?_⟩
    have hp : p = p₀ := prime_eq (la.valuation c.F) κ κ₀ hκ hκ₀
    subst hp
    obtain ⟨g, hg, hgκ⟩ := GlobalTheory.T.padic_embeddings_conjugate_of_units c.F p κ₀ κ (fun a => (hκ₀ a).symm.trans (hκ a))
    have e : ‖κ π‖ = ‖κ₀ π₀‖ := by
      rw [norm_eq_of_val_eq _ κ hκ hne (hπ.trans hπ₀.symm), ← hgκ, hg]
    rw [e, div_mul_cancel₀ _ hlog]
    exact hasFinNorm_of_isometry g hg hgκ ht₀
  · exact ⟨0, fun p κ π h1 h2 => (hex ⟨p, κ, π, h1, h2⟩).elim⟩

theorem exists_rho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  intro E _ _ _ H D l Xo c _ U τ φ hfin
  choose ρ hρ using exists_rho_at U τ φ hfin
  exact ⟨ρ, fun p κ la π h1 h2 => hρ la p κ π h1 h2⟩

end GlobalTheory.CompanionTheory.Ar.Br.FinPlace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | exact GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho <;> assumption)
end
