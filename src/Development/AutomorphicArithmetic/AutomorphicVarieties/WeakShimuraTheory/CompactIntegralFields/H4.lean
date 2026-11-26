module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegCosetFour
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharpolyOfNotIrreducibleRestricti
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.NonComm

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemPowerSeriesCharRatiosNotIsOfFinOrder
open IsLocalRing Polynomial Matrix UpperTheory.V

private lemma power_series_unit_eq_one_of_torsion (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l]
    (y : (PowerSeries K)ˣ) (m : ℕ) (hm : m ≠ 0)
    (hc : PowerSeries.constantCoeff (y : PowerSeries K) = 1) (hy : y ^ m = 1) : y = 1 := by
  have : CharP (PowerSeries K) l :=
    charP_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective l
  apply Units.ext
  refine UpperTheory.V.Pr.T.oneUnitTF l (y : PowerSeries K) m hm ?_ ?_
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp [hc]
  · rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]

theorem UpperTheory.V.Ws.exists_mem_powerSeries_char_ratios_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H K : Type) [Group H] [Field K] [Finite K] [CharP K l] (n : ℕ)
      (ψ : Fin n → H →* (PowerSeries K)ˣ) (N : Subgroup H),
      (∀ i j, i ≠ j → ∃ g ∈ N, PowerSeries.constantCoeff (ψ i g : PowerSeries K) = PowerSeries.constantCoeff (ψ j g : PowerSeries K) ∧
        ψ i g ≠ ψ j g) → ∃ g ∈ N, ∀ i j, i ≠ j → ¬ IsOfFinOrder (ψ i g / ψ j g) := by
  intro l _ H K _ _ _ _ n ψ N h
  classical
  have := Fintype.ofFinite K
  have hpos : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hunit : ∀ y : (PowerSeries K)ˣ, PowerSeries.constantCoeff (y : PowerSeries K) ≠ 0 := fun y =>
    (y.isUnit.map PowerSeries.constantCoeff).ne_zero
  have key := UpperTheory.V.Pr.commonFree N (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2}
    (fun p => (ψ p.1.1 / ψ p.1.2).comp N.subtype) (Fintype.card K - 1) hpos ?_ ?_
  · obtain ⟨g, hg⟩ := key
    refine ⟨g, g.2, fun i j hij hf => ?_⟩
    obtain ⟨m, hm, he⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact hg ⟨(i, j), hij⟩ m hm (by simpa using he)
  · intro p g m hm he
    refine power_series_unit_eq_one_of_torsion l K _ m hm.ne' ?_ ?_
    · rw [Units.val_pow_eq_pow_val, map_pow]
      exact FiniteField.pow_card_sub_one_eq_one _ (hunit _)
    · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · intro p
    obtain ⟨g, hg, hc, hne⟩ := h p.1.1 p.1.2 p.2
    refine ⟨⟨g, hg⟩, fun he => hne ?_⟩
    have h1 : ψ p.1.1 g / ψ p.1.2 g = 1 := by
      refine power_series_unit_eq_one_of_torsion l K _ _ hpos.ne' ?_ (by simpa using he)
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) * ψ p.1.2 g = ψ p.1.1 g := div_mul_cancel _ _
      have h3 := congrArg (fun y : (PowerSeries K)ˣ => PowerSeries.constantCoeff (y : PowerSeries K)) h2
      simp only [Units.val_mul, map_mul] at h3
      rw [hc] at h3
      exact mul_right_cancel₀ (hunit (ψ p.1.2 g)) (h3.trans (one_mul _).symm)
    exact div_eq_one.1 h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.IsClosedZeroLocusMvPolynomialEvalAdicContinuous
open IsLocalRing Polynomial Matrix UpperTheory.V

open Filter Topology in
theorem UpperTheory.V.Ws.isClosed_zeroLocus_mvPolynomial_eval_adicContinuous :
    ∀ (G A κ ι : Type) [TopologicalSpace G] [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [Field κ]
      (j : A →+* κ), Function.Injective j → ∀ a : ι → G → A, (∀ s, Alg.AdicCont (maximalIdeal A) (a s)) →
      ∀ f : MvPolynomial ι κ, IsClosed {g | MvPolynomial.eval (fun s => j (a s g)) f = 0} := by
  intro G A κ ι _ _ _ _ _ _ j _ a ha f
  classical
  letI : Algebra A κ := j.toAlgebra
  let L : (f.support → A) →ₗ[A] κ :=
    { toFun := fun v => ∑ d : f.support, f.coeff d.1 * j (v d)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        change ∑ d : f.support, f.coeff d.1 * j (c * x d) = j c * ∑ d : f.support, f.coeff d.1 * j (x d)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_mul]; ring }
  let m : G → f.support → A := fun g d => ∏ i ∈ d.1.support, a i g ^ d.1 i
  have hL : ∀ g, L (m g) = MvPolynomial.eval (fun s => j (a s g)) f := fun g => by
    rw [MvPolynomial.eval_eq, ← Finset.sum_coe_sort]
    change ∑ d : f.support, f.coeff d.1 * j (m g d) = _
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [m, map_prod, map_pow]
  let K := LinearMap.ker L
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (f.support → A) ⧸ K) (maximalIdeal A)
    (maximalIdeal.isMaximal A).ne_top
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : K.mkQ (m x) ≠ 0 := fun h => hx (by
    have h2 : L (m x) = 0 := (Submodule.Quotient.mk_eq_zero K).1 h
    rw [hL] at h2
    exact h2)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K.mkQ (m x) ∉ (maximalIdeal A ^ N • ⊤ : Submodule A ((f.support → A) ⧸ K)) := by
    by_contra h
    push Not at h
    apply hx'
    rw [← Submodule.mem_bot A, ← hK]
    exact (Submodule.mem_iInf _).2 h
  have hev : ∀ᶠ y in 𝓝 x, ∀ d, m x d - m y d ∈ maximalIdeal A ^ N := by
    rw [eventually_all]; intro d
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i ∈ d.1.support,
        Ideal.Quotient.mk (maximalIdeal A ^ N) (a i y) = Ideal.Quotient.mk (maximalIdeal A ^ N) (a i x) := by
      rw [eventually_all_finset]; intro i _
      exact (ha i N).eventually_eq x
    filter_upwards [h1] with y hy
    refine Ideal.Quotient.eq.1 ?_
    simp only [m, map_prod, map_pow]
    exact Finset.prod_congr rfl fun i hi => by rw [hy i hi]
  filter_upwards [hev] with y hy hy0
  apply hN
  have h0 : K.mkQ (m y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 (by
    change L (m y) = 0
    rw [hL]; exact hy0)
  have h1 : K.mkQ (m x) = K.mkQ (m x - m y) := by rw [map_sub, h0, sub_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, pi_eq_sum_univ' (m x - m y), map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (hy s) Submodule.mem_top
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharEqOfCharpolyTwistInvariant
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem charpoly_neg_roots_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (a i))) : (-M).charpoly = ∏ i, (X - C (-a i)) := by
  have h1 : (-M).charmatrix = -((compRingHom (-X : R[X])).mapMatrix M.charmatrix) := by
    ext i j : 1
    by_cases e : i = j
    · subst e
      simp [Matrix.charmatrix_apply_eq]
      ring
    · simp [Matrix.charmatrix_apply_ne _ _ _ e]
  have h2 := congrArg (compRingHom (-X : R[X])) h
  rw [Matrix.charpoly, RingHom.map_det, map_prod] at h2
  rw [Matrix.charpoly, h1, Matrix.det_neg, h2]
  have h3 : (-1 : R[X]) ^ Fintype.card (Fin n) = ∏ _i : Fin n, (-1 : R[X]) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
  ring

theorem UpperTheory.V.Ws.exists_sign_twist_char_eq_of_charpoly_twist_invariant :
    ∀ (K k k' B G : Type) [Field K] [Field k] [Field k'] [CommRing B] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) B)
      (j : B →+* K) (φ : B →+* k') (ι : k →+* k') (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j →
      (∀ g, (r g).charpoly.map φ = ∏ i, (X - C (ι (χ i g)))) →
      (∀ g, ((r g).map j).charpoly = ((((η g : ℤˣ) : ℤ) : K) • (r g).map j).charpoly) →
      ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k k' B G _ _ _ _ _ n r j φ ι χ η hj h1 h2 i
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly (fun i => W.pushCh (Int.castRingHom k) η * χ i) g := by
    intro g
    have hv : ∀ i, (((W.pushCh (Int.castRingHom k) η * χ i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * (χ i g : k) := by
      intro i
      rfl
    unfold Pr.chPoly
    simp only [hv]
    rcases Int.units_eq_one_or (η g) with e | e
    · simp only [e, Units.val_one, Int.cast_one, one_mul]
    · have h3 : (r g).charpoly = (-r g).charpoly := by
        apply Polynomial.map_injective j hj
        rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, h2 g, e]
        congr 1
        ext a b
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Matrix.smul_apply, Matrix.map_apply,
          Matrix.neg_apply, map_neg, smul_eq_mul, neg_mul, one_mul]
      have h4 : ((r g).map φ).charpoly = ∏ i, (X - C (ι (χ i g))) := by rw [Matrix.charpoly_map, h1 g]
      have h5 := charpoly_neg_roots_neg _ _ h4
      have h6 : -((r g).map φ) = (-r g).map φ := by
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      rw [h6, Matrix.charpoly_map, ← h3, h1 g] at h5
      apply Polynomial.map_injective ι ι.injective
      simp only [Polynomial.map_prod, e, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_neg, map_neg] at h5 ⊢
      exact h5
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n _ _ key
  exact ⟨σ i, hσ i⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CharpolyFlag
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((W.GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (W.GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [W.GDet.repAlg, h]
  · simp [W.GDet.repAlg, h, hij]

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

theorem UpperTheory.V.Ws.h4Cp :
    ∀ (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ)
      (r : W.Resid F O n) (x : W.Point r),
      (∀ g, (W.mat x.ρ g).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) =
        ∏ i, ((X : Polynomial x.K) - C (algebraMap (ResidueField O) x.K ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)))) ∧
      ∀ v g, (W.mat x.ρ (F.φ v g)).charpoly = ∏ i, ((X : Polynomial x.A) - C ((x.ψ v i g : x.Aˣ) : x.A)) := by
  intro l _ F O _ _ _ n r x
  refine ⟨fun g => ?_, fun v g => ?_⟩
  · have h := congrArg (fun D => W.GDet.chi D (MonoidAlgebra.single g 1)) x.red
    simp only [W.Resid.Dbar, chi_map_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly.map _ = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · apply Polynomial.map_injective (algebraMap x.A x.Fr) (IsFractionRing.injective x.A x.Fr)
    rw [← Matrix.charpoly_map, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact charpoly_flag _ _ (x.flag v) g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.SignCharEqOneOfCyclotomicSubOneNotIsUnit
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem UpperTheory.V.Ws.tendsto_pow_prime_pow_one (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (hx : ¬ IsUnit (x - 1)) :
    Filter.Tendsto (fun n : ℕ => x ^ l ^ n) Filter.atTop (nhds 1) := by
  have hd : (l : ℤ_[l]) ∣ x - 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr hx))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖x ^ l ^ n - 1‖ ≤ ((l : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hd n
    rw [one_pow] at hc
    rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
    calc _ ≤ (l : ℝ)⁻¹ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
      _ = _ := mul_one _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    exact this.comp (Filter.tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun n => norm_nonneg _) hb h0

theorem UpperTheory.V.Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      (ε : G →* ℤ_[l]ˣ), Continuous ε → ∀ η : G →* ℤˣ, IsOpen (η.ker : Set G) → ε.ker ≤ η.ker →
      ∀ g, ¬ IsUnit ((ε g : ℤ_[l]) - 1) → η g = 1 := by
  intro l _ hl2 G _ _ _ _ ε hε η hopen hker g hg
  rcases Int.units_eq_one_or (η g) with h | h
  · exact h
  exfalso
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  let C : Set G := ((η.ker : Set G))ᶜ
  have hCc : IsCompact C := (isClosed_compl_iff.mpr hopen).isCompact
  let f : G → ℤ_[l] := fun h => (ε h : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp hε
  have hK : IsClosed (f '' C) := (hCc.image hf).isClosed
  have hmem : ∀ n : ℕ, f (g ^ l ^ n) ∈ f '' C := by
    intro n
    refine ⟨g ^ l ^ n, ?_, rfl⟩
    show g ^ l ^ n ∉ η.ker
    rw [MonoidHom.mem_ker, map_pow, h, (hodd.pow).neg_one_pow]
    decide
  have hlim : Filter.Tendsto (fun n : ℕ => f (g ^ l ^ n)) Filter.atTop (nhds 1) := by
    have := tendsto_pow_prime_pow_one l (ε g : ℤ_[l]) hg
    refine this.congr fun n => ?_
    simp [f, map_pow]
  have h1 : (1 : ℤ_[l]) ∈ f '' C := hK.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  obtain ⟨k, hkC, hk1⟩ := h1
  apply hkC
  apply hker
  rw [MonoidHom.mem_ker]
  exact Units.ext hk1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.PowSep
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder :
    ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ), M.charpoly = ∏ i, (X - C (a i : K)) →
      (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) → ∀ d : ℕ, 0 < d → (M ^ d).charpoly.Separable := by
  intro K _ n M a hM ha d hd
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨d, hd, ?_⟩
    rw [div_pow, div_eq_one]
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have heq : (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
  rw [heq]
  exact Polynomial.separable_prod_X_sub_C_iff.2 hinj
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.StabClosed
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.isClosed_setOf_matrix_stabilizes_submodule :
    ∀ (G κ : Type) [TopologicalSpace G] [Field κ] (n : ℕ) (a : G → Matrix (Fin n) (Fin n) κ), Pr.LinClosed a →
      ∀ W : Submodule κ (Fin n → κ), IsClosed {g | ∀ v ∈ W, a g *ᵥ v ∈ W} := by
  intro G κ _ _ n a ha W
  have hset : {g | ∀ v ∈ W, a g *ᵥ v ∈ W} =
      ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator, {g | φ (a g *ᵥ v) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (fun φ hφ => h v hv φ hφ)
  rw [hset]
  refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
  let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
    { toFun := fun M => φ (M *ᵥ v)
      map_add' := by
        intro M N
        simp [Matrix.add_mulVec]
      map_smul' := by
        intro c M
        simp only [Matrix.smul_mulVec, map_smul, smul_eq_mul, RingHom.id_apply] }
  exact ha f
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsStabilizerIndexDvdOfNotIrreducibleRestrict
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CoordSub
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.coordSub :
    ∀ (C ι : Type) [CommRing C] [Fintype ι] [DecidableEq ι] (d : ι → C), (∀ i j, i ≠ j → IsUnit (d i - d j)) →
      ∀ W : Submodule C (ι → C), (∀ w ∈ W, diagonal d *ᵥ w ∈ W) → ∀ w ∈ W, ∀ i, Pi.single i (w i) ∈ W := by
  intro C ι _ _ _ d hd W hD w hw i
  have key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using hw
    · intro j S hj ih
      have h2 := W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)
      convert h2 using 1
      funext k
      simp only [Finset.prod_insert hj, Pi.sub_apply, Matrix.mulVec_diagonal,
        Pi.smul_apply, smul_eq_mul, mul_assoc, sub_mul]
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j)) :=
    IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm
  have h3 := W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))
  convert h3 using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · have hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp [Pi.single_eq_of_ne hk, hz]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.InvariantSubmoduleEqSpanEigenbasisOfSeparable
open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem exists_eigenbasis_of_separable_charpoly {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Module.finrank_fintype_fun_eq_card])
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem UpperTheory.V.Ws.invariant_submodule_eq_span_eigenbasis_of_separable :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K), M.charpoly.Separable →
      ∃ b : Module.Basis (Fin n) K (Fin n → K), ∀ W : Submodule K (Fin n → K), (∀ v ∈ W, M *ᵥ v ∈ W) →
        W = Submodule.span K (b '' {i | b i ∈ W}) := by
  classical
  intro K _ _ n M hM
  obtain ⟨b, l, hl, hb⟩ := exists_eigenbasis_of_separable_charpoly M hM
  refine ⟨b, fun W hW => le_antisymm ?_ ?_⟩
  · have hcomm : ∀ x : Fin n → K, b.equivFun.symm (diagonal l *ᵥ x) = M *ᵥ b.equivFun.symm x := by
      intro x
      rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hb, mulVec_diagonal, smul_smul, mul_comm]
    have key := UpperTheory.V.AlgebraTools.coordSub K (Fin n) l
      (fun i j h => (sub_ne_zero.mpr (fun h' => h (hl h'))).isUnit)
      (W.comap b.equivFun.symm.toLinearMap)
      (fun w hw => by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
        rw [hcomm]
        exact hW _ hw)
    intro v hv
    have h1 : ∀ i, b.repr v i • b i ∈ W := by
      intro i
      have h2 := key (b.equivFun v) (by
        rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]; exact hv) i
      rw [Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
        Finset.sum_eq_single i (fun j _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
          (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, Module.Basis.equivFun_apply] at h2
      exact h2
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : b.repr v i = 0
    · rw [h, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (W.smul_mem_iff h).mp (h1 i), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CardDvdOfPartitionEqualSize
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf hf' using hu
  have hfib : ∀ q, T q = {i | f i = q} := by
    intro q
    ext i
    constructor
    · intro h
      exact (hf' i q h).symm
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [← h]
      exact hf i
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty ι := ⟨fun i => by
      have h := hT (f i)
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h
      have hi : i ∈ T (f i) := hf i
      rw [h] at hi
      simp at hi⟩
    rw [Nat.card_of_isEmpty (α := ι)]
    exact dvd_zero _
  · have hne : ∀ q, (T q).Nonempty := fun q =>
      Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega)
    choose g hg using hne
    have ginj : Function.Injective g := by
      intro q q' h
      calc q = f (g q) := hf' _ _ (hg q)
        _ = f (g q') := by rw [h]
        _ = q' := (hf' _ _ (hg q')).symm
    haveI : Finite Q := Finite.of_injective g ginj
    letI : Fintype Q := Fintype.ofFinite Q
    have hc : ∀ q, Nat.card {x // f x = q} = d := fun q => by
      rw [← hT q, hfib q, ← Nat.card_coe_set_eq]
      rfl
    have key : Nat.card ι = Nat.card Q * d := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [key]
    exact dvd_mul_right _ _
end

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), U3.MatIrr ⊤ r →
      ∀ N : Subgroup G, commutator G ≤ N → (∃ u ∈ N, (r u).charpoly.Separable) → ¬ U3.MatIrr N r →
      ∃ (W : Submodule K (Fin n → K)) (S : Subgroup G), W ≠ ⊥ ∧ W ≠ ⊤ ∧ N ≤ S ∧ (∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W) ∧
        S.index ∣ n := by
  intro K G _ _ _ n r hirr N hN hu hnot
  classical
  obtain ⟨u, huN, hsep⟩ := hu
  have hconj : ∀ g h : G, h ∈ N → g⁻¹ * h * g ∈ N := by
    intro g h hh
    have hc : h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ ∈ N :=
      hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have e : g⁻¹ * h * g = h * (h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹) := by
      group
    rw [e]
    exact N.mul_mem hh hc
  have hr1 : ∀ g : G, r g * r g⁻¹ = 1 := by
    intro g
    rw [← map_mul, mul_inv_cancel, map_one]
  have hr2 : ∀ g : G, r g⁻¹ * r g = 1 := by
    intro g
    rw [← map_mul, inv_mul_cancel, map_one]
  let Inv : Submodule K (Fin n → K) → Prop := fun X => ∀ g ∈ N, ∀ v ∈ X, r g *ᵥ v ∈ X
  let tr : G → Submodule K (Fin n → K) → Submodule K (Fin n → K) :=
    fun g X => X.map (Matrix.toLin' (r g))
  have mem_tr : ∀ g X v, v ∈ tr g X ↔ r g⁻¹ *ᵥ v ∈ X := by
    intro g X v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hx
    · intro hv
      refine Submodule.mem_map.2 ⟨_, hv, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
  have tr_inv : ∀ g X, Inv X → Inv (tr g X) := by
    intro g X hX h hh v hv
    rw [mem_tr] at hv ⊢
    have e : r g⁻¹ *ᵥ (r h *ᵥ v) = r (g⁻¹ * h * g) *ᵥ (r g⁻¹ *ᵥ v) := by
      simp only [Matrix.mulVec_mulVec, map_mul, mul_assoc, hr1, mul_one]
    rw [e]
    exact hX _ (hconj g h hh) _ hv
  have htr_mul : ∀ g h X, tr (g * h) X = tr g (tr h X) := by
    intro g h X
    ext v
    rw [mem_tr, mem_tr, mem_tr, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec]
  have htr_one : ∀ X, tr 1 X = X := by
    intro X
    ext v
    rw [mem_tr, inv_one, map_one, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := Ws.invariant_submodule_eq_span_eigenbasis_of_separable K n (r u) hsep
  have hspan : ∀ X, Inv X → X = Submodule.span K (b '' {i | b i ∈ X}) :=
    fun X hX => hb X (hX u huN)
  have hrank : ∀ X, Inv X → Module.finrank K X = {i | b i ∈ X}.ncard := by
    intro X hX
    have e := hspan X hX
    calc Module.finrank K X = Module.finrank K (Submodule.span K (b '' {i | b i ∈ X})) := by
          rw [← e]
      _ = {i | b i ∈ X}.ncard := by
          have hli := b.linearIndependent.comp
            (Subtype.val : {i // i ∈ {i | b i ∈ X}} → Fin n) Subtype.val_injective
          rw [Set.image_eq_range]
          rw [finrank_span_eq_card (R := K) (b := fun x : {i // i ∈ {i | b i ∈ X}} => b x) hli,
            ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨W0, hW0i, hW0b, hW0t⟩ : ∃ W, Inv W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    unfold U3.MatIrr at hnot
    push_neg at hnot
    exact hnot
  have hex : ∃ k, ∃ X, Inv X ∧ X ≠ ⊥ ∧ Module.finrank K X = k := ⟨_, W0, hW0i, hW0b, rfl⟩
  obtain ⟨W, hWi, hWb, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ X, Inv X → X ≠ ⊥ → Module.finrank K W ≤ Module.finrank K X := by
    intro X hX hXb
    rw [hWk]
    exact Nat.find_min' hex ⟨X, hX, hXb, rfl⟩
  have hWt : W ≠ ⊤ := by
    intro h
    have h1 := hmin W0 hW0i hW0b
    have h2 := Submodule.finrank_lt hW0t
    rw [h, finrank_top] at h1
    omega
  have tr_ne : ∀ g X, X ≠ ⊥ → tr g X ≠ ⊥ := by
    intro g X hX h
    apply hX
    rw [eq_bot_iff]
    intro v hv
    have hm : r g *ᵥ v ∈ tr g X := by
      rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hv
    rw [h, Submodule.mem_bot] at hm
    have e := congrArg (fun w => r g⁻¹ *ᵥ w) hm
    simp only [Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec, Matrix.mulVec_zero] at e
    rw [e]
    exact Submodule.zero_mem _
  have trW_rank : ∀ g, Module.finrank K (tr g W) = Module.finrank K W := fun g =>
    le_antisymm (Submodule.finrank_map_le _ _) (hmin _ (tr_inv g W hWi) (tr_ne g W hWb))
  have key : ∀ g, (∀ v ∈ W, r g *ᵥ v ∈ W) → tr g W = W := by
    intro g hg
    apply Submodule.eq_of_le_of_finrank_le
    · intro v hv
      rw [mem_tr] at hv
      have e : v = r g *ᵥ (r g⁻¹ *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
      rw [e]
      exact hg _ hv
    · rw [trW_rank]
  let S : Subgroup G :=
    { carrier := {g | tr g W = W}
      mul_mem' := by
        intro a c ha hc
        simp only [Set.mem_setOf_eq] at ha hc ⊢
        rw [htr_mul, hc, ha]
      one_mem' := htr_one W
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← htr_mul, inv_mul_cancel, htr_one] }
  have hS : ∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W := by
    intro g
    constructor
    · intro hg v hv
      have hm : r g *ᵥ v ∈ tr g W := by
        rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hv
      have hg' : tr g W = W := hg
      rw [hg'] at hm
      exact hm
    · exact key g
  refine ⟨W, S, hWb, hWt, fun g hg => (hS g).2 (hWi g hg), hS, ?_⟩
  have huniq : ∀ g1 g2 i, b i ∈ tr g1 W → b i ∈ tr g2 W → tr g1 W = tr g2 W := by
    intro g1 g2 i h1 h2
    have hI : Inv (tr g1 W ⊓ tr g2 W) := fun h hh v hv =>
      ⟨tr_inv g1 W hWi h hh v hv.1, tr_inv g2 W hWi h hh v hv.2⟩
    have hne : tr g1 W ⊓ tr g2 W ≠ ⊥ := by
      intro h
      have hm : b i ∈ tr g1 W ⊓ tr g2 W := ⟨h1, h2⟩
      rw [h, Submodule.mem_bot] at hm
      exact b.ne_zero i hm
    have hm := hmin _ hI hne
    have e1 : tr g1 W ⊓ tr g2 W = tr g1 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [trW_rank]; exact hm)
    have e2 : tr g1 W ⊓ tr g2 W = tr g2 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [trW_rank]; exact hm)
    exact e1.symm.trans e2
  have hcover : ∀ i, ∃ g, b i ∈ tr g W := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi⟩ := hc
    have hUi : ∀ g ∈ (⊤ : Subgroup G), ∀ v ∈ ⨆ h, tr h W, r g *ᵥ v ∈ ⨆ h, tr h W := by
      intro g _ v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => r g *ᵥ v ∈ ⨆ h, tr h W) hv ?_ ?_ ?_
      · intro h x hx
        refine Submodule.mem_iSup_of_mem (g * h) ?_
        rw [htr_mul, mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hx
      · show r g *ᵥ 0 ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        show r g *ᵥ (x + y) ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_add]
        exact add_mem hx hy
    have hU := hirr _ hUi
    have hUb : (⨆ h, tr h W) ≠ ⊥ := by
      intro h
      apply hWb
      rw [eq_bot_iff, ← h]
      have := le_iSup (fun h => tr h W) 1
      rw [htr_one] at this
      exact this
    have hUt := hU.resolve_left hUb
    have hbi : b i ∈ ⨆ h, tr h W := by
      rw [hUt]
      exact Submodule.mem_top
    have hz : ∀ v ∈ ⨆ h, tr h W, b.repr v i = 0 := by
      intro v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => b.repr v i = 0) hv ?_ ?_ ?_
      · intro g x hx
        have hx' : x ∈ tr g W := hx
        rw [hspan _ (tr_inv g W hWi), Module.Basis.mem_span_image] at hx'
        by_contra h0
        exact hi g (hx' (Finsupp.mem_support_iff.2 h0))
      · simp
      · intro x y hx hy
        simp only [map_add (f := _), Finsupp.add_apply]
        rw [hx, hy, add_zero]
    have := hz _ hbi
    simp at this
  let T : G ⧸ S → Set (Fin n) := fun q => {i | b i ∈ tr q.out W}
  have hT1 : ∀ q, (T q).ncard = Module.finrank K W := by
    intro q
    rw [← trW_rank q.out, hrank _ (tr_inv _ W hWi)]
  have hT2 : ∀ i, ∃! q, i ∈ T q := by
    intro i
    obtain ⟨g, hg⟩ := hcover i
    refine ⟨(g : G ⧸ S), ?_, ?_⟩
    · show b i ∈ tr (g : G ⧸ S).out W
      obtain ⟨a, ha⟩ : ∃ a, a = (g : G ⧸ S).out := ⟨_, rfl⟩
      rw [← ha]
      have hm : a⁻¹ * g ∈ S := by
        rw [ha]
        exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ S))
      have hm' : tr (a⁻¹ * g) W = W := hm
      have e : tr (a * (a⁻¹ * g)) W = tr a W := by
        rw [htr_mul, hm']
      rw [mul_inv_cancel_left] at e
      rw [← e]
      exact hg
    · intro q hq
      have e := huniq _ _ i hq hg
      have hm : q.out⁻¹ * g ∈ S := by
        show tr _ W = W
        rw [htr_mul, ← e, ← htr_mul, inv_mul_cancel, htr_one]
      exact (QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hm)
  have hc := Ws.card_dvd_of_partition_equal_size (Fin n) (G ⧸ S) T (Module.finrank K W) hT1 hT2
  have hn : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  rw [hn] at hc
  exact hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemOpenInterSubgroupOfCosetwiseFiniteIndex
open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
      (Z : Subgroup G) (P : G → Prop), (∀ V : Subgroup Z, V.FiniteIndex → ∀ σ : Z, ∃ g ∈ V, P (σ * g : Z)) →
      ∀ U : Set G, IsOpen U → (U ∩ (Z : Set G)).Nonempty → ∃ σ ∈ U ∩ (Z : Set G), P σ := by
  intro G _ _ _ _ _ Z P h U hU hne
  obtain ⟨σ, hσU, hσZ⟩ := hne
  have hW : IsOpen ((fun x : G => σ * x) ⁻¹' U) := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ ((fun x : G => σ * x) ⁻¹' U) := by simpa using hσU
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  have hfi : (N.toSubgroup).FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hP⟩ := h (N.toSubgroup.subgroupOf Z) inferInstance ⟨σ, hσZ⟩
  refine ⟨_, ⟨?_, ((⟨σ, hσZ⟩ : Z) * g).2⟩, hP⟩
  exact hN (show (g : G) ∈ N.toSubgroup from hg)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.h4 :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
      (r : W.Resid F O 4) (x : W.Point r), Nonempty F.Vl → (∀ v i, Alg.AdicCont (maximalIdeal x.A) fun g => ((x.ψ v i g : x.Aˣ) : x.A)) →
      (∀ v i j, i ≠ j → ∃ g, F.φ v g ∈ F.G' ∧ r.psib v i g = r.psib v j g ∧ x.ψ v i g ≠ x.ψ v j g) →
      U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) →
      (∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) →
      (∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (r.chib i / r.chib j) ^ n ≠ 1) → x.N1 ∧ x.TypeI ∧ x.N3 := by
  intro l _ hl F O _ _ _ _ _ r x ⟨v⟩ _ ha hb hc hd
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharP x.K l := charP_of_injective_algebraMap (algebraMap (ResidueField O) x.K).injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  let j : x.A →+* x.Fb := (algebraMap x.Fr x.Fb).comp (algebraMap x.A x.Fr)
  have hj : Function.Injective j := (algebraMap x.Fr x.Fb).injective.comp (IsFractionRing.injective x.A x.Fr)
  let ρ : F.G₀ →* Matrix (Fin 4) (Fin 4) x.Fb := W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)
  have hρ : ∀ g, ρ g = (W.mat x.ρ g).map j := fun g => rfl
  have two : ∀ (k : Type) [Field k] [CharP k l], (2 : k) ≠ 0 := fun k _ _ h =>
    hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast h)))
  haveI : CharP x.Fb l := charP_of_injective_ringHom (j.comp (PowerSeries.C : x.K →+* x.A)).injective l
  obtain ⟨cpR, cpL⟩ := h4Cp l F O 4 r x

  obtain ⟨g, hg, hfree⟩ := exists_mem_powerSeries_char_ratios_not_isOfFinOrder l (F.Gv v) x.K 4 (x.ψ v) (F.G'.comap (F.φ v)) fun a b hab => by
    obtain ⟨s, h1, h2, h3⟩ := ha v a b hab
    refine ⟨s, h1, ?_, h3⟩
    have h4 : ∀ i, PowerSeries.constantCoeff (x.ψ v i s : PowerSeries x.K) =
        algebraMap (ResidueField O) x.K (r.psib v i s) := fun i =>
      congrArg Units.val (DFunLike.congr_fun (x.ψ_red v i) s)
    rw [h4, h4, h2]
  let a : Fin 4 → x.Fbˣ := fun i => Units.map (j : x.A →* x.Fb) (x.ψ v i g)
  have hu : (ρ (F.φ v g)).charpoly = ∏ i, (X - C (a i : x.Fb)) := by
    rw [hρ, Matrix.charpoly_map, cpL, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => hfree s t hst <| by
    rw [← _root_.map_div] at h
    exact (Function.Injective.isOfFinOrder_iff (Units.map_injective (f := (j : x.A →* x.Fb)) hj)).1 h
  have hsep := charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _

  have hI : x.TypeI := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := exists_stabilizer_index_dvd_of_not_irreducible_restriction x.Fb F.G₀ 4 ρ hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := exists_sign_twist_charpoly_of_not_irreducible_restriction x.Fb F.G₀ (two _) ρ hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := isClosed_setOf_matrix_stabilizes_submodule F.G₀ x.Fb 4 _ (Pr.linClosedOfAdic F.G₀ x.A x.Fb j hj 4 (W.mat x.ρ) x.cont) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (exists_sign_twist_char_eq_of_charpoly_twist_invariant x.Fb (ResidueField O) x.K x.A F.G₀ 4 (W.mat x.ρ) j _ _ r.chib η hj cpR hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) (two (ResidueField O))
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨fun w => ⟨fun s t hst h => ?_, fun s t hst h => ?_⟩, hI, ?_⟩
  · obtain ⟨y, -, -, h3⟩ := ha w s t hst
    exact h3 (by rw [h])
  · obtain ⟨y, h1, -, h3⟩ := ha w s t hst.ne
    have h4 : (F.ε.comp F.η.ker.subtype) (F.φ w y) = 1 := h1
    refine h3 ?_
    rw [h, MonoidHom.mul_apply, MonoidHom.comp_apply, W.GFrame.eps, MonoidHom.comp_apply, h4, map_one, mul_one]
  · have hsp : Submodule.span x.Fb (Set.range (ρ.comp F.G'.subtype)) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
    have hsp' : Submodule.span x.Fb (Set.range ρ) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
    have hnc := exists_noncommuting_images_in_finiteIndex_normal_subgroup x.Fb x.K x.A F.G₀ ρ j PowerSeries.constantCoeff
      (fun i => W.pushCh (algebraMap (ResidueField O) x.K) (r.chib i)) hj
      (fun s => ⟨(W.mat x.ρ s).charpoly, by rw [hρ, Matrix.charpoly_map], cpR s⟩) hsp' (by
        obtain ⟨s, t, h⟩ := hd
        refine ⟨s, t, fun n h0 h4 he => h n h0 h4 (MonoidHom.ext fun y => ?_)⟩
        apply Units.map_injective (f := (algebraMap (ResidueField O) x.K : ResidueField O →* x.K)) (RingHom.injective _)
        simpa using DFunLike.congr_fun he y) F.G' _ hg hsep
    refine exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat x.ρF s).charpoly.Separable) fun V hV σ => ?_
    obtain ⟨y, hy, hs⟩ := AlgebraTools.regCosetFour x.Fb F.G' (two _) (ρ.comp F.G'.subtype)
      (fun f => (isClosed_zeroLocus_mvPolynomial_eval_adicContinuous F.G₀ x.A x.Fb (Fin 4 × Fin 4) j hj (fun p s => W.mat x.ρ s p.1 p.2) (fun p => x.cont p.1 p.2) f).preimage
        continuous_subtype_val) hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
    refine ⟨y, hy, (Polynomial.separable_map (algebraMap x.Fr x.Fb)).1 ?_⟩
    rw [← Matrix.charpoly_map]
    exact hs
