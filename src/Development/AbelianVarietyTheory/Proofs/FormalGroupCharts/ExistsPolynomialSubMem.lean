module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
open MvPowerSeries IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.CompleteBaseChange

theorem mem_smul_top_pi {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) (x : ι → M) :
    x ∈ (J • ⊤ : Submodule R (ι → M)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R M) := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => M) i) h
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  · obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
    have key : ∀ m ∈ (J • ⊤ : Submodule R M), ∃ y : Fin n → M, ∑ l, a l • y l = m := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) ?_
      · rw [← ha] at hr
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
        exact ⟨fun l => c l • m, by simp [Finset.sum_smul, smul_smul, mul_comm]⟩
      · rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
        exact ⟨y + z, by simp [Finset.sum_add_distrib]⟩
    choose y hy using fun i => key _ (h i)
    have : x = ∑ l, a l • fun i => y i l := by
      funext i
      simp [hy]
    rw [this]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem_smul (ha ▸ Submodule.subset_span ⟨l, rfl⟩) trivial

theorem isPrecomplete_pi {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsPrecomplete J M] : IsPrecomplete J (ι → M) := by
  refine ⟨fun u hu => ?_⟩
  have h1 : ∀ i, ∃ L : M, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R M)] :=
    fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
      SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hu hab)) i)
  choose L hL using h1
  exact ⟨L, fun k => SModEq.sub_mem.2
    ((mem_smul_top_pi hJ.pow _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩

theorem isHausdorff_pi {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsHausdorff J M] : IsHausdorff J (ι → M) := by
  refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩
  exact SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hx n)) j)

theorem mem_of_coeff_eq_zero {R σ : Type*} [CommRing R] [Finite σ] (N : ℕ)
    (K : Ideal (MvPowerSeries σ R))
    (hK : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : R) : MvPowerSeries σ R) ∈ K)
    (g : MvPowerSeries σ R) (hg : ∀ d : σ →₀ ℕ, d.degree < N → coeff d g = 0) : g ∈ K := by
  classical
  have h1 : ∀ d : σ →₀ ℕ, ∃ α : σ →₀ ℕ, N ≤ d.degree → α ≤ d ∧ α.degree = N := fun d => by
    by_cases hd : N ≤ d.degree
    · obtain ⟨α, h⟩ := Finsupp.exists_le_degree_eq d N hd
      exact ⟨α, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose A hA using h1
  let S := (Finsupp.finite_of_degree_eq (σ := σ) N).toFinset
  have hS : ∀ α, α ∈ S ↔ α.degree = N := fun α => by simp [S]
  let G : (σ →₀ ℕ) → MvPowerSeries σ R := fun α e => if A (α + e) = α then coeff (α + e) g else 0
  have hG : ∀ α e, coeff e (G α) = if A (α + e) = α then coeff (α + e) g else 0 := fun _ _ => rfl
  have : g = ∑ α ∈ S, monomial α 1 * G α := by
    ext d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_monomial_mul, one_mul, hG]
    by_cases hd : N ≤ d.degree
    · rw [Finset.sum_eq_single_of_mem (A d) ((hS _).2 (hA d hd).2)]
      · simp [(hA d hd).1, add_tsub_cancel_of_le (hA d hd).1]
      · intro α _ hα
        split_ifs with h2 h3
        · rw [add_tsub_cancel_of_le h2] at h3
          exact absurd h3.symm hα
        · rfl
        · rfl
    · rw [hg d (not_le.1 hd)]
      refine (Finset.sum_eq_zero fun α _ => ?_).symm
      split_ifs with h2 h3
      · rw [add_tsub_cancel_of_le h2]
        exact hg d (not_le.1 hd)
      · rfl
      · rfl
  rw [this]
  exact K.sum_mem fun α hα => K.mul_mem_right _ (hK α ((hS α).1 hα))

theorem exists_polynomial_sub_mem {O σ τ : Type*} [CommRing O] [Finite σ] [Fintype τ]
    {J : Ideal O} (hJ : J.FG) [IsAdicComplete J O] (f : τ → MvPowerSeries σ O) (N : ℕ)
    (hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O))
    (g : MvPowerSeries σ O) :
    ∃ p : MvPolynomial σ O, g - p ∈ Ideal.span (Set.range f) := by
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  rw [← hx]
  exact (add_sub_cancel_left _ _).symm

end GlobalTheory.CompleteBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesMemMapCOfCoeffMem
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem mvPowerSeries_map_surjective {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by
  intro g
  refine ⟨fun n => Function.surjInv hφ (MvPowerSeries.coeff n g), ?_⟩
  ext n
  exact Function.surjInv_eq hφ _

theorem mvPowerSeries_mem_map_C_of_coeff_mem {σ R : Type} [CommRing R] (I : Ideal R)
    (hI : I.FG) (g : MvPowerSeries σ R) (hg : ∀ n, MvPowerSeries.coeff n g ∈ I) :
    g ∈ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I := by
  classical
  obtain ⟨s, rfl⟩ := hI
  have h : ∀ n, ∃ c : R → R, ∑ a ∈ s, c a * a = MvPowerSeries.coeff n g := by
    intro n
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hg n)
    exact ⟨c, by simpa [smul_eq_mul] using hc⟩
  choose c hc using h
  let G : R → MvPowerSeries σ R := fun a n => c n a
  have : g = ∑ a ∈ s, G a * MvPowerSeries.C a := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coeff_mul_C]
    rfl
  rw [this]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_left _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

theorem span_X_pow_le_sup_of_residue :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ ι : Type) [Finite σ] (f : ι → MvPowerSeries σ T) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j)) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : T →+* MvPowerSeries σ T) (maximalIdeal T) := by
  intro T _ _ _ σ ι _ f M h
  set φ : MvPowerSeries σ T →+* MvPowerSeries σ (ResidueField T) :=
    MvPowerSeries.map (residue T) with hφ
  have hs : Function.Surjective φ := mvPowerSeries_map_surjective _ residue_surjective
  have h1 : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) =
      Ideal.map φ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext1 i
    simp [hφ]
  have h2 : Ideal.span (Set.range fun j => φ (f j)) = Ideal.map φ (Ideal.span (Set.range f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h1, h2, ← Ideal.map_pow, Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_surjective φ hs] at h
  refine h.trans (sup_le_sup_left ?_ _)
  intro g hg
  refine mvPowerSeries_mem_map_C_of_coeff_mem _ (IsNoetherian.noetherian _) g fun n => ?_
  have h0 : φ g = 0 := by simpa using hg
  rw [← residue_eq_zero_iff]
  have := congrArg (MvPowerSeries.coeff n) h0
  simpa [hφ] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormallyUnramifiedOfIsReduced
open TensorProduct nonZeroDivisors

namespace GlobalTheory.SepIdem

theorem formallyUnramified_of_isReduced (K A : Type) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.FormallyUnramified K A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Finite (MaximalSpectrum A) := inferInstance
  have h : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm

theorem exists_smul_kaehler_eq_zero (O : Type) [CommRing O] [Module.Finite ℤ O] [IsReduced O] :
    ∃ N : ℕ, 0 < N ∧ ∀ ω : Ω[O⁄ℤ], (N : O) • ω = 0 := by
  let A := ℚ ⊗[ℤ] O
  letI : Algebra O A := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid O ℤ⁰) A :=
    IsLocalization.tensorRight ℚ ℤ⁰
  have : IsReduced A := isReduced_localizationPreserves (Algebra.algebraMapSubmonoid O ℤ⁰) A inferInstance
  have : Algebra.FormallyUnramified ℚ A := formallyUnramified_of_isReduced ℚ A
  have : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization ℤ⁰
  have hA : Algebra.FormallyUnramified ℤ A := Algebra.FormallyUnramified.comp ℤ ℚ A
  have : Algebra.FormallyEtale O A :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid O ℤ⁰)
  have hm := KaehlerDifferential.isLocalizedModule_map ℤ O A (Algebra.algebraMapSubmonoid O ℤ⁰)
  have key : ∀ ω : Ω[O⁄ℤ], ∃ n : ℤ, n ≠ 0 ∧ (n : O) • ω = 0 := by
    intro ω
    have h0 : KaehlerDifferential.map ℤ ℤ O A ω = 0 := Subsingleton.elim _ _
    obtain ⟨⟨s, n, hn, rfl⟩, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff (Algebra.algebraMapSubmonoid O ℤ⁰) _).1 h0
    exact ⟨n, nonZeroDivisors.ne_zero hn, by simpa using hs⟩
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := Ω[O⁄ℤ])
  choose n hn0 hn using key
  refine ⟨∏ x ∈ S, (n x).natAbs, Finset.prod_pos fun x _ => Int.natAbs_pos.2 (hn0 x), ?_⟩
  intro ω
  have hω : ω ∈ Submodule.span O (S : Set Ω[O⁄ℤ]) := hS ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (n x).natAbs) hx
    obtain ⟨j, hj⟩ : n x ∣ ((n x).natAbs : ℤ) := Int.dvd_natAbs.2 dvd_rfl
    have : (((n x).natAbs : ℕ) : O) = (j : O) * (n x : O) := by
      rw [← Int.cast_natCast, hj]; push_cast; ring
    rw [hk, Nat.cast_mul, this, mul_comm, ← mul_assoc, mul_smul, hn, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

theorem exists_separability_element (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] :
    ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧
      ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0 := by
  obtain ⟨N, hN, hΩ⟩ := exists_smul_kaehler_eq_zero O
  set I := KaehlerDifferential.ideal ℤ O with hI
  have hfg : I.FG := KaehlerDifferential.ideal_fg ℤ O
  have : Module.Finite (O ⊗[ℤ] O) I := Module.Finite.iff_fg.2 hfg
  have hsq : ∀ x ∈ I, (N : O ⊗[ℤ] O) * x ∈ I ^ 2 := by
    intro x hx
    have h := hΩ (I.toCotangent ⟨x, hx⟩)
    have h2 : I.toCotangent ((N : O ⊗[ℤ] O) • ⟨x, hx⟩) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul]
      exact (Nat.cast_smul_eq_nsmul O N (show Ω[O⁄ℤ] from I.toCotangent ⟨x, hx⟩)).symm.trans h
    exact (Ideal.toCotangent_eq_zero I _).1 h2
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (O ⊗[ℤ] O)
      (algebraMap (O ⊗[ℤ] O) (Module.End (O ⊗[ℤ] O) I) (N : O ⊗[ℤ] O)) I (by
        rintro _ ⟨⟨x, hx⟩, rfl⟩
        rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two]
        exact hsq x hx)
  rw [Polynomial.aeval_algebraMap_apply] at h0
  refine ⟨N ^ p.natDegree, Polynomial.aeval (N : O ⊗[ℤ] O) p, pow_pos hN _, ?_, fun c => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · have hz : ∑ k ∈ Finset.range p.natDegree,
          Algebra.TensorProduct.lmul' ℤ (p.coeff k • (N : O ⊗[ℤ] O) ^ k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have : p.coeff k ∈ I :=
          Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)
        have h : Algebra.TensorProduct.lmul' ℤ (p.coeff k) = 0 := this
        rw [smul_eq_mul, map_mul, h, zero_mul]
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, map_add (f := _),
        hp.coeff_natDegree, one_smul, map_sum, hz, zero_add, map_pow, map_natCast, Nat.cast_pow]
  · have hm := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal ℤ c
    have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨_, hm⟩)
    have h : Polynomial.aeval (N : O ⊗[ℤ] O) p * ((1 : O) ⊗ₜ[ℤ] c - c ⊗ₜ[ℤ] (1 : O)) = 0 := this
    rw [← neg_sub, neg_mul, mul_comm, h, neg_zero]

end GlobalTheory.SepIdem
end
