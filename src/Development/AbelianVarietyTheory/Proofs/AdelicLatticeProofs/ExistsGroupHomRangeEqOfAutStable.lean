module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem IsPre.exists_group_range :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ →
      ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  intro ι _ _ Γ hΓ
  let H : Subgroup (Matrix.SpecialLinearGroup ι ℂ) :=
    { carrier := {g | (g : Matrix ι ι ℂ) ∈ Γ}
      one_mem' := hΓ.one_mem
      mul_mem' := fun {a b} ha hb => hΓ.mul_mem _ ha _ hb
      inv_mem' := fun {a} ha => hΓ.adj_mem _ ha }
  let ρ : H →* Matrix ι ι ℂ :=
    { toFun := fun g => ((g : Matrix.SpecialLinearGroup ι ℂ) : Matrix ι ι ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨H, inferInstance, ρ, ?_⟩
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hg
    exact ⟨⟨⟨g, hΓ.det_eq g hg⟩, hg⟩, rfl⟩

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStableStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_hom_range_eq_of_isPre : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  first | exact @GlobalTheory.ClassFin.IsPre.exists_group_range | exact GlobalTheory.ClassFin.IsPre.exists_group_range | (intros; apply GlobalTheory.ClassFin.IsPre.exists_group_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts

lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl

theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePointsStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_mem_ratZariskiClosurePoints : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ pts Γ R := by
  first | exact @GlobalTheory.ClassFin.RatPts.rat_mem_pts | exact GlobalTheory.ClassFin.RatPts.rat_mem_pts | (intros; apply GlobalTheory.ClassFin.RatPts.rat_mem_pts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma exists_pos_nat_clearing_rat_denominators {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]

theorem _root_.GlobalTheory.ClassFin.adelicPair_elementary : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → (∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a) ∧ (∀ (κ : Type) [Fintype κ] (r : κ → R), ∃ M : ℕ, 0 < M ∧ ∀ k, (M : R) * r k ∈ R₀) ∧ Function.Injective (algebraMap ℚ R) := by
  intro R _ _ R₀ hR
  refine ⟨fun M hM r hr => ?_, fun κ _ r => ?_, ?_⟩
  · obtain ⟨q, a, ha, hra⟩ := hR.approx M hM r
    have hq : algebraMap ℚ R q ∈ R₀ := by
      have h : algebraMap ℚ R q = r - (M : R) * a := by rw [hra]; ring
      rw [h]
      exact R₀.sub_mem hr (R₀.mul_mem (natCast_mem R₀ M) ha)
    obtain ⟨z, rfl⟩ := hR.int_of_mem q hq
    exact ⟨z, a, ha, by rw [hra, map_intCast]⟩
  · choose q a ha hra using fun k => hR.approx 1 one_pos (r k)
    obtain ⟨M, hM, hMq⟩ := exists_pos_nat_clearing_rat_denominators q
    refine ⟨M, hM, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hMq k
    have h : (M : R) * r k = (z : R) + (M : R) * a k := by
      rw [hra k, Nat.cast_one, one_mul, mul_add, ← map_natCast (algebraMap ℚ R) M, ← map_mul, hz,
        map_intCast]
    rw [h]
    exact R₀.add_mem (intCast_mem R₀ z) (R₀.mul_mem (natCast_mem R₀ M) (ha k))
  · have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := hR.int_of_mem (1 / 2)
        (by rw [Subsingleton.elim (algebraMap ℚ R (1 / 2)) 0]; exact R₀.zero_mem)
      have h2 : (1 : ℚ) = 2 * z := by rw [← hz]; norm_num
      have h3 : (1 : ℤ) = 2 * z := by exact_mod_cast h2
      omega
    exact (algebraMap ℚ R).injective

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSubSqLtOneOfTwoLtOne
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_sub_sq_mem_of_two_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (a : 𝓞 F) :
    ∃ b : 𝓞 F, a - b ^ 2 ∈ v.asIdeal := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI := v.isPrime
  have h0 : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 h2
    rwa [map_ofNat] at this
  have hinj : Function.Injective (fun t : 𝓞 F ⧸ v.asIdeal => t ^ 2) := by
    intro s t hst
    have hst' : s ^ 2 = t ^ 2 := hst
    have : (s - t) ^ 2 = 0 := by
      linear_combination hst' + (t ^ 2 - s * t) * h0
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj (Ideal.Quotient.mk v.asIdeal a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨b, Ideal.Quotient.eq.1 ?_⟩
  rw [map_pow]
  exact ht.symm

theorem exists_sub_sq_lt_one_of_two_lt_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by
  intro F _ _ v h2 x hx
  set φ := algebraMap F (v.adicCompletion F) with hφ
  have hval : ∀ k : F, Valued.v (φ k) = v.valuation F k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal :=
    fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r

  have h2' : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hmem, ← hval, map_ofNat, map_ofNat]
    exact h2

  obtain ⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by
    have hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun y hy => ?_⟩
      have hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1 := by simpa using hy
      simpa using Valued.v.restrict_lt_iff.mp hy'
    exact (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← hval]
    have e : φ k = (φ k - x) + x := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le hx)

  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
    obtain ⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧
        k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by
      obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k
      · exact ⟨d, n, d.2, h⟩
      · refine ⟨n, d, fun hn => d.2 ?_, h⟩
        show (d : 𝓞 F) ∈ v.asIdeal
        rw [← hmem, ← h, map_mul]
        exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)
    obtain ⟨t, i, hi, hti⟩ := (Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs
    refine ⟨t * m, ?_⟩
    have hi' : i = 1 - t * s := by rw [← hti]; ring
    have e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i := by
      rw [hi', map_mul, ← hsm, map_sub, map_one, map_mul]; ring
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)

  obtain ⟨b, hb⟩ := exists_sub_sq_mem_of_two_mem F v h2' r
  refine ⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩
  · rw [hval]
    exact HeightOneSpectrum.valuation_le_one v b
  · have e : x - φ (algebraMap (𝓞 F) F b) ^ 2 =
        -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2))) := by
      simp only [map_sub, map_pow]; ring
    rw [e]
    refine Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)
    · rw [hval]; exact hr
    · rw [hval]; exact (hmem _).2 hb

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpow
open scoped Topology BigOperators

namespace GlobalTheory

private lemma continuous_circle_toUnits' : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  have : Continuous (fun w : Circle => ((w⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp continuous_inv
  convert this using 2 with w
  simp

private lemma div_norm_sq_eq_div_conj_of_ne_zero (x : ℂ) (hx : x ≠ 0) :
    (x / ‖x‖) ^ 2 = x / starRingEnd ℂ x := by
  have h : x * starRingEnd ℂ x = ((‖x‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc : starRingEnd ℂ x ≠ 0 := by simpa using hx
  rw [div_pow, ← h]
  field_simp

theorem _root_.GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  intro ι _ f hf hreal
  classical
  let g : ι → Circle →* Circle := fun i =>
    f.comp ((MonoidHom.mulSingle (fun _ => ℂˣ) i).comp Circle.toUnits)
  have hg : ∀ i, Continuous (g i) := fun i =>
    hf.comp ((continuous_mulSingle i).comp continuous_circle_toUnits')
  choose n hn using fun i => _root_.GlobalTheory.circle_hom_eq_zpow (g i) (hg i)
  have heven : ∀ i, Even (n i) := by
    intro i
    have h1 : g i (Circle.exp Real.pi) = 1 := by
      apply hreal
      intro j
      by_cases hj : j = i
      · subst hj
        simp [Circle.coe_exp, Complex.exp_pi_mul_I]
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hn] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I] at h2
    rcases Int.even_or_odd (n i) with h | h
    · exact h
    · rw [h.neg_one_zpow] at h2
      norm_num at h2
  choose k hk using heven
  refine ⟨k, fun z => ?_⟩
  have hne : ∀ i, ((‖(z i : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun i => by simp
  set u : ι → Circle := fun i => Circle.exp (Complex.arg (z i)) with hu_def
  have hu : ∀ i, ((u i : Circle) : ℂ) = (z i : ℂ) / ‖(z i : ℂ)‖ := by
    intro i
    rw [eq_div_iff (hne i), mul_comm]
    simpa [u, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (z i : ℂ)
  have hz : z = (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) *
      fun i => Circle.toUnits (u i) := by
    funext i
    ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
    simp [hu, mul_div_cancel₀ _ (hne i)]
  have hr : f (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) = 1 :=
    hreal _ fun i => by simp
  have hv : f (fun i => Circle.toUnits (u i)) = ∏ i, g i (u i) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (fun i => Circle.toUnits (u i))]
    rw [map_prod]
    rfl
  have hfz : f z = ∏ i, g i (u i) := by
    conv_lhs => rw [hz]
    rw [map_mul, hr, one_mul, hv]
  rw [hfz]
  refine (map_prod Circle.coeHom (fun i => g i (u i)) Finset.univ).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ((g i (u i) : Circle) : ℂ) = _
  rw [hn, Circle.coe_zpow, hu, hk i, ← two_mul, zpow_mul, zpow_ofNat,
    div_norm_sq_eq_div_conj_of_ne_zero _ (z i).ne_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpowStatement
open scoped Topology BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zpow_prod_div_conj_of_continuous_trivial_on_real : ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  first | exact @GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | exact GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | (intros; apply GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivApplyNeOfIsAlgebraic
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_apply_ne_of_isAlgebraic :
    ∀ z : ℂ, IsAlgebraic ℚ z → (∀ q : ℚ, z ≠ q) → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z _ hz
  by_contra h
  have hfix : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z := fun σ => by_contra fun hne => h ⟨σ.toRingEquiv, hne⟩
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := ℚ) z hfix
  exact hz q (hq.symm.trans (by simp))

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivNeOfTranscendental
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_ne_of_transcendental :
    ∀ z : ℂ, Transcendental ℚ z → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z hz
  have hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ) := by
    show AlgebraicIndependent ℚ _
    exact algebraicIndependent_unique_type_iff.2 hz
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  let v : t → ℂ := (↑)
  let i0 : t := ⟨z, hzt rfl⟩
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v ht
  let f : t → MvPolynomial t ℚ := fun i => if i = i0 then -MvPolynomial.X i else MvPolynomial.X i
  have hcomp : (MvPolynomial.aeval f).comp (MvPolynomial.aeval f) =
      AlgHom.id ℚ (MvPolynomial t ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases h : i = i0 <;> simp [f, h]
  let neg := AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f) hcomp hcomp
  let e : Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v) :=
    ht.1.aevalEquiv.symm.toRingEquiv.trans (neg.toRingEquiv.trans ht.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩
  have h1 : algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ (ht.1.aevalEquiv (MvPolynomial.X i0)) = z := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have key : IsAlgClosure.equivOfEquiv ℂ ℂ e z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.symm_apply_apply]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [neg, f, v, i0]
  rw [key]
  intro h
  have h0 : z = 0 := by linear_combination (-1 / 2 : ℂ) * h
  rw [h0] at hz
  exact hz isAlgebraic_zero

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem _root_.GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed :
    ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  intro z hz
  by_contra h
  push_neg at h
  by_cases ha : IsAlgebraic ℚ z
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_apply_ne_of_isAlgebraic z ha h
    exact hσ (hz σ)
  · obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.ClassFin.exists_ringEquiv_ne_of_transcendental z ha
    exact hσ (hz σ)

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixedStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed : ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  first | exact @GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | exact GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitMulSqQuadraticDefectStep
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_unit_mul_sq_sub_one_lt :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (δ π : K) (k : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) → w δ = 1 → w 4 < w (δ - 1) → w (δ - 1) = WithZero.exp (-(2 * (k : ℤ))) → ∃ c : K, w c = 1 ∧ w (δ * c ^ 2 - 1) < w (δ - 1) := by
  intro K _ w δ π k hπ hres hδ h4 hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have hδ0 : δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hδ
      exact zero_ne_one hδ
    have hinv : w δ⁻¹ = 1 := by rw [map_inv₀, hδ, inv_one]
    obtain ⟨y, hy1, hy⟩ := hres δ⁻¹ hinv.le
    have hy2 : w (y ^ 2) = 1 := by
      have e : y ^ 2 = δ⁻¹ - (δ⁻¹ - y ^ 2) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rwa [hinv]), hinv]
    refine ⟨y, le_antisymm hy1 (not_lt.mp fun hlt => ?_), ?_⟩
    · rw [map_pow] at hy2
      exact (pow_lt_one₀ zero_le' hlt two_ne_zero).ne hy2
    · have e : δ * y ^ 2 - 1 = -(δ * (δ⁻¹ - y ^ 2)) := by
        rw [mul_sub, mul_inv_cancel₀ hδ0]
        ring
      rw [e, Valuation.map_neg, map_mul, hδ, one_mul, hk]
      simpa using hy
  ·

    set t := π ^ k with ht
    set g := w (δ - 1) with hg
    have hgpos : 0 < g := lt_of_le_of_lt zero_le' h4
    have htt : w t * w t = g := by
      show w t * w t = g
      rw [hk, ht, map_pow, hπ, ← pow_add, ← WithZero.exp_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      ring
    have hwt0 : w t ≠ 0 := fun h => hgpos.ne (by simpa [h] using htt)
    have hwtpos : 0 < w t := zero_lt_iff.mpr hwt0
    have ht0 : t ≠ 0 := fun h => hwt0 (by rw [h, map_zero])
    have ht1 : w t < 1 := by
      rw [ht, map_pow, hπ]
      refine pow_lt_one₀ zero_le' ?_ hkpos.ne'
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hg1 : g < 1 := by
      rw [← htt]
      calc w t * w t ≤ w t * 1 := mul_le_mul' le_rfl ht1.le
        _ = w t := mul_one _
        _ < 1 := ht1
    have h2t : w 2 < w t := by
      refine lt_of_not_ge fun h => ?_
      have hle : g ≤ w 4 := by
        rw [← htt, show (4 : K) = 2 * 2 by norm_num, map_mul]
        exact mul_le_mul' h h
      exact absurd h4 (not_lt.mpr hle)
    set x := (δ - 1) * (t ^ 2)⁻¹ with hxdef
    have hx : t ^ 2 * x = δ - 1 := by
      rw [hxdef, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ht0), mul_one]
    have hwx : w (-x) = 1 := by
      rw [Valuation.map_neg, hxdef, map_mul, map_inv₀, map_pow, ← hg, ← htt, sq,
        mul_inv_cancel₀ (mul_ne_zero hwt0 hwt0)]
    obtain ⟨y, hy1, hy⟩ := hres (-x) hwx.le
    refine ⟨1 + t * y, ?_, ?_⟩
    · apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc w t * w y ≤ w t * 1 := mul_le_mul' le_rfl hy1
        _ = w t := mul_one _
        _ < 1 := ht1
    · have e : δ * (1 + t * y) ^ 2 - 1
          = -(t ^ 2 * (-x - y ^ 2)) + 2 * t * y + (δ - 1) * (2 * t * y + t ^ 2 * y ^ 2) := by
        linear_combination (-1 : K) * hx
      rw [e]
      have hA : w (-(t ^ 2 * (-x - y ^ 2))) < g := by
        rw [Valuation.map_neg, map_mul, map_pow, sq, htt]
        calc g * w (-x - y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hy hgpos
          _ = g := mul_one g
      have hB : w (2 * t * y) < g := by
        rw [map_mul, map_mul, ← htt]
        calc w 2 * w t * w y ≤ w 2 * w t * 1 := mul_le_mul' le_rfl hy1
          _ = w 2 * w t := mul_one _
          _ < w t * w t := mul_lt_mul_of_pos_right h2t hwtpos
      have hC : w ((δ - 1) * (2 * t * y + t ^ 2 * y ^ 2)) < g := by
        have hD : w (2 * t * y + t ^ 2 * y ^ 2) < 1 := by
          apply Valuation.map_add_lt
          · exact hB.trans hg1
          · rw [map_mul, map_pow w t, map_pow w y, sq (w t), htt]
            calc g * w y ^ 2 ≤ g * 1 := mul_le_mul' le_rfl (pow_le_one₀ zero_le' hy1)
              _ = g := mul_one g
              _ < 1 := hg1
        rw [map_mul, ← hg]
        calc g * w (2 * t * y + t ^ 2 * y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hD hgpos
          _ = g := mul_one g
      exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hA hB) hC

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

private lemma neg_one_le_re_pow_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (k : ℕ) : -1 ≤ (c ^ k).re := by
  have h1 : ‖c ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have h2 := Complex.abs_re_le_norm (c ^ k)
  linarith [(abs_le.mp (h2.trans h1)).1]

theorem _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ¬ Summable fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) := by
  intro h
  set f := fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) with hf
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one hc (k + 1)]) (by positivity)
  have hkey : ∀ k : ℕ, 3 / 2 * (1 / ((k : ℝ) + 1)) ≤ f k + f (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hn : ‖c ^ (k + 1)‖ ^ 2 ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    have hz : c ^ (2 * k + 1 + 1) = c ^ (k + 1) * c ^ (k + 1) := by ring
    have hsum : f k + f (2 * k + 1) = (3 + 2 * (c ^ (k + 1)).re +
        ((c ^ (k + 1)).re * (c ^ (k + 1)).re - (c ^ (k + 1)).im * (c ^ (k + 1)).im)) /
        ((k : ℝ) + 1) := by
      simp only [hf, hz, Complex.mul_re]
      push_cast
      field_simp
      ring
    rw [hsum, mul_one_div]
    exact (div_le_div_iff_of_pos_right hk).mpr (by nlinarith [sq_nonneg ((c ^ (k + 1)).re + 1 / 2)])
  have hs2 : Summable fun k : ℕ => f k + f (2 * k + 1) :=
    h.add (h.comp_injective (fun a b hab => by simpa using hab))
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    have h3 : Summable fun k : ℕ => 3 / 2 * (1 / ((k : ℝ) + 1)) :=
      hs2.of_nonneg_of_le (fun k => by positivity) hkey
    exact (summable_mul_left_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).mp h3
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ?_)
  simpa using hharm

private lemma norm_mul_natCast_cpow_neg_le {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : ‖c‖ ≤ 1) (s : ℂ) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (by positivity) hc

private lemma natCast_rpow_neg_le_half {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hn

theorem _root_.GlobalTheory.conj_neg_log_euler_factor (n : ℕ) (hn : 2 ≤ n) (c : ℂ) (hc : ‖c‖ ≤ 1) (s : ℂ)
    (hs : 1 < s.re) :
    starRingEnd ℂ (-Complex.log (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s)))) =
      -Complex.log (1 - starRingEnd ℂ c * (n : ℂ) ^ (-s)) := by
  have hlt : ‖c * (n : ℂ) ^ (-(starRingEnd ℂ s))‖ < 1 :=
    ((norm_mul_natCast_cpow_neg_le hn hc (starRingEnd ℂ s)).trans
      (natCast_rpow_neg_le_half hn (by simpa using hs))).trans_lt (by norm_num)
  have hre : 0 < (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).re := by
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm (c * (n : ℂ) ^ (-(starRingEnd ℂ s)))]
  have harg : (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).arg ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hconj : starRingEnd ℂ ((n : ℂ) ^ (-(starRingEnd ℂ s))) = (n : ℂ) ^ (-s) := by
    have := Complex.cpow_conj (n : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
    rw [map_neg] at this
    rw [this, Complex.conj_conj, Complex.conj_natCast]
  rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hconj]

theorem _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z L : ℂ → ℂ, Differentiable ℂ Z → Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → (∀ s : ℂ, 1 < s.re → L s = Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))) → L 1 ≠ 0 := by
  intro ι N c hN hc hsum hne Z L hZ hL hZs hLs h1
  set L' : ℂ → ℂ := fun s => starRingEnd ℂ (L (starRingEnd ℂ s)) with hL'
  have hdL' : Differentiable ℂ L' := fun s => by
    have := (hL (starRingEnd ℂ s)).conj_conj
    simpa [hL', Function.comp_def] using this
  have hL'1 : L' 1 = 0 := by simp [hL', h1]
  have hds : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ (dslope f 1) := fun f hf =>
    differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
  have ha : ∀ p : ι × ℕ, 0 ≤ (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) := fun p =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one (hc p.1) (p.2 + 1)]) (by positivity)
  have key := _root_.GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s ^ 2 * dslope L 1 s * dslope L' 1 s) ha
    (fun p => mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by have := hN p.1; omega : 1 ≤ N p.1))))
    (((hZ.pow 2).mul (hds L hL)).mul (hds L' hdL')) (by
      intro s hs
      refine ⟨_, _root_.GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hL's : L' s = Complex.exp (∑' i, -Complex.log
          (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s))) := by
        simp only [hL']
        rw [hLs _ (by simpa using hs), ← Complex.exp_conj, Complex.conj_tsum]
        congr 1
        exact tsum_congr fun i => _root_.GlobalTheory.conj_neg_log_euler_factor (N i) (hN i) (c i) (hc i) s hs
      simp only [dslope_of_ne _ hs1, slope_def_field, h1, hL'1, sub_zero]
      rw [hZs s hs, hLs s hs, hL's, two_mul, Complex.exp_add, Complex.exp_add, Complex.exp_add]
      field_simp)
  obtain ⟨i⟩ := hne
  exact _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c i) (hc i)
    (((summable_prod_of_nonneg (fun p => ha p)).mp key).1 i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectors
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UTrans.IsoBasis

variable {E : Type} [Field E] {n : ℕ}

def hfL (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf σ G x y
  map_add' u v := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hfL_apply (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    hfL σ G y x = hf σ G x y := rfl

theorem hf_symm {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hG.invol, hG.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hfL_ne {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) {y : Fin n → E}
    (hy : y ≠ 0) : ∃ x, hfL σ G y x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hy
  have h0 : G.mulVec (fun b => σ (y b)) = 0 := by
    funext a
    have := h (Pi.single a 1)
    simpa [hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel] using this
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0
  funext b
  have := congrFun h1 b
  simpa using this

theorem hf_comb {σ : E →+* E} (G : Matrix (Fin n) (Fin n) E) (a b : E) (u w : Fin n → E) :
    hf σ G (a • u + b • w) (a • u + b • w) =
      a * σ a * hf σ G u u + a * σ b * hf σ G u w + b * σ a * hf σ G w u + b * σ b * hf σ G w w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem exists_isotropic_avoid [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by
  obtain ⟨w, hw0, hw⟩ := hz
  obtain ⟨c, hc⟩ := hG.ne_id
  set δ := c - σ c with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hc.symm
  have hδσ : σ δ = -δ := by simp [hδ, hG.invol]
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun o : Option ι => o.elim (hfL σ G w) f) (by
      rintro (_ | i)
      · exact hfL_ne hG hw0
      · exact hf0 i)
  have huw : hf σ G u w ≠ 0 := hu none
  have hui : ∀ i, f i u ≠ 0 := fun i => hu (some i)
  set a := hf σ G w u with ha
  have hσa : σ a = hf σ G u w := hf_symm hG _ _
  have ha0 : a ≠ 0 := by
    intro h; apply huw; rw [← hσa, h, map_zero]
  have huu : σ (hf σ G u u) = hf σ G u u := hf_symm hG _ _
  let bad : ι → E := fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ
  have hfin : (Set.range bad).Finite := Set.finite_range bad
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by
    by_contra h
    push_neg at h
    exact (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin
  refine ⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩
  · rw [hf_comb, hw, ← ha, ← hσa]
    simp only [map_add (f := _), map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]
    ring
  · rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases h : f i w = 0
    · simp [h, ha0, hui i]
    · intro h'
      apply ht
      refine ⟨i, ?_⟩
      simp only [bad]
      field_simp
      linear_combination (-2 : E) * h'

theorem exists_isotropic_basis (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) (x y : Fin n → E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧
      ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  let S : Set (Fin n → E) := {z | hf σ G z z = 0 ∧ hf σ G x z ≠ 0 ∧ hf σ G y z ≠ 0}
  have hspan : Submodule.span E S = ⊤ := by
    by_contra h
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨z, hz0, hz1⟩ := exists_isotropic_avoid hG hz ![g, hfL σ G x, hfL σ G y] (by
      intro i
      fin_cases i
      · by_contra h
        push_neg at h
        exact hg0 (LinearMap.ext h)
      · exact hfL_ne hG hx
      · exact hfL_ne hG hy)
    have hzS : z ∈ S := by
      refine ⟨hz0, fun h => hz1 1 ?_, fun h => hz1 2 ?_⟩
      · show hf σ G z x = 0
        rw [← hf_symm hG, h, map_zero]
      · show hf σ G z y = 0
        rw [← hf_symm hG, h, map_zero]
    exact hz1 0 (hg (Submodule.subset_span hzS))
  obtain ⟨v, hvS, -, hv⟩ := Submodule.exists_fun_fin_finrank_span_eq E S
  have hn : n = Module.finrank E (Submodule.span E S) := by
    rw [hspan]; simp
  exact ⟨v ∘ Fin.cast hn, hv.comp _ (Fin.cast_injective hn), fun i => hvS _⟩

end GlobalTheory.UTrans.IsoBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 → ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧ ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  first | exact @GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | exact GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | (intros; apply GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis <;> assumption)
end
end
