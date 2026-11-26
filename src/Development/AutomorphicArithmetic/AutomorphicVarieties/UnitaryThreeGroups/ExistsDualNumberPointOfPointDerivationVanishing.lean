module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.WeightedPresExistsAlgHomExtensionOfAdicComplete
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem pf_monomial {O σ S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (f : MvPowerSeries σ O →ₐ[O] S) (m : σ →₀ ℕ) :
    f (monomial m 1) = m.prod fun s k => f (MvPowerSeries.X s) ^ k := by
  have h := GlobalTheory.algHom_coe_mvPolynomial f (MvPolynomial.monomial m (1 : O))
  rw [MvPolynomial.coe_monomial, MvPolynomial.aeval_monomial, RingHom.map_one, one_mul] at h
  exact h

private theorem pf_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp only [mul_pow, Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem pf_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (σ →₀ ℕ), ∀ d, Finsupp.degree d < n → d ∈ T :=
    ⟨(Finsupp.finite_of_degree_lt (σ := σ) n).toFinset, fun d hd => by simpa using hd⟩
  refine ⟨T.image (Finsupp.weight wt), MvPowerSeries.le_order fun d hd => ?_⟩
  have hd' : Finsupp.degree d < n := by exact_mod_cast hd
  have hmem : Finsupp.weight wt d ∈ T.image (Finsupp.weight wt) :=
    Finset.mem_image_of_mem _ (hT d hd')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq, if_pos hmem, sub_self]

private theorem pf_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  obtain ⟨s, hs⟩ := pf_approx wt F n
  have h1 := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  have h2 : φ (∑ j ∈ s, wcomp O wt j F) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => h j
  rw [map_sub, h2, sub_zero] at h1
  rwa [sub_zero]

variable {O X R K : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
  [CommRing K] [Algebra O K] (ξ : W.A →ₐ[O] K)

private theorem pf_zprod (m : W.σ →₀ ℕ) :
    ((m.prod fun s k => W.zA s ^ k : W.A) : R) = W.π (monomial m 1) := by
  rw [pf_monomial]
  exact map_finsuppProd W.A.val _ _

variable [Module.Free ℤ X] [Module.Finite ℤ X] {B : Type} [CommRing B] [Algebra O B] (ι : B →ₐ[O] K)
  (t : Multiplicative X →* Kˣ) (g : MvPowerSeries W.σ O →ₐ[O] B)

private theorem pf_step (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (I J : Ideal B) (S : Set (W.σ →₀ ℕ)) (j : X) (hS : ∀ n ∈ S, Finsupp.weight W.wt n = j)
    (hJ : ∀ n ∈ S, g (monomial n 1) ∈ J)
    (hI : ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ I)
    (F : MvPowerSeries W.σ O) (hF : ∀ n, n ∉ S → coeff n F = 0) (x : W.A) (hx : (x : R) = W.π F) :
    ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ I * J := by
  classical
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W S j hS
  obtain ⟨b, hb, hFb⟩ := hμ F hF
  have hy : ∀ m, W.π (b m) ∈ W.A := fun m =>
    W.part_le_A (j := 0) (show W.π (b m) ∈ W.part 0 from Submodule.mem_map_of_mem (hb m))
  choose c hc hcI using fun m => hI (b m) (hb m) ⟨W.π (b m), hy m⟩ rfl
  refine ⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩
  · have hx' : x = ∑ m ∈ μ, (⟨W.π (b m), hy m⟩ : W.A) * (m.prod fun s k => W.zA s ^ k) := by
      apply Subtype.ext
      rw [hx, hFb]
      show _ = W.A.val _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, map_mul]
      show _ = W.π (b m) * ((m.prod fun s k => W.zA s ^ k : W.A) : R)
      rw [pf_zprod]
    have hgm : ∀ m ∈ μ, ι (g (monomial m 1)) =
        (t (Multiplicative.ofAdd j) : K) * ξ (m.prod fun s k => W.zA s ^ k) := by
      intro m hm
      have h1 := pf_monomial (ι.comp g) m
      simp only [AlgHom.comp_apply, hg] at h1
      rw [h1, pf_prod W.wt t (fun s => ξ (W.zA s)) m, hS m (hμS (Finset.mem_coe.mpr hm)),
        map_finsuppProd]
      simp only [map_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum ι, map_sum ξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul ι, map_mul ξ, hc m, hgm m hm]
    ring
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hFb, map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, ← sub_mul]
    exact Ideal.mul_mem_mul (hcI m) (hJ m (hμS (Finset.mem_coe.mpr hm)))

private theorem mono_lemma {O' σ' B' : Type} [CommRing O'] [CommRing B'] [Algebra O' B'] [Finite σ']
    (g' : MvPowerSeries σ' O' →ₐ[O'] B') (J : Ideal B') (hJ : ∀ s, g' (MvPowerSeries.X s) ∈ J)
    (m : σ' →₀ ℕ) (hm : m ≠ 0) : g' (monomial m 1) ∈ J := by
  classical
  have h := GlobalTheory.algHom_mem_pow_of_le_order g' hJ (n := 1) (g := monomial m 1) ?_
  · simpa using h
  refine MvPowerSeries.le_order fun d hd => ?_
  have hd' : Finsupp.degree d < 1 := by exact_mod_cast hd
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
  subst hd0
  rw [MvPowerSeries.coeff_monomial, if_neg (Ne.symm hm)]

private theorem exists_lift_sub_mem_pow_of_mem_wtPart_zero
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (n : ℕ) :
    ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ n := by
  classical
  induction n with
  | zero =>
    intro b hb x hx
    obtain ⟨c, hc⟩ := h0 x (show (x : R) ∈ W.part 0 from Submodule.mem_map.mpr ⟨b, hb, hx.symm⟩)
    exact ⟨c, hc, by simp⟩
  | succ n ih =>
    intro b hb x hx
    have hb' : ∀ m, Finsupp.weight W.wt m ≠ 0 → coeff m b = 0 := hb
    obtain ⟨b0, hb0⟩ : ∃ b0, b0 = MvPowerSeries.constantCoeff b := ⟨_, rfl⟩
    have hC : (MvPowerSeries.C b0 : MvPowerSeries W.σ O) = algebraMap O _ b0 := rfl
    obtain ⟨x', hxe⟩ : ∃ x' : W.A, x' = x - algebraMap O W.A b0 := ⟨_, rfl⟩
    have hx' : (x' : R) = W.π (b - MvPowerSeries.C b0) := by
      rw [hxe, map_sub, hC, AlgHom.commutes, ← hx]
      rfl
    have hF : ∀ m, m ∉ {m : W.σ →₀ ℕ | Finsupp.weight W.wt m = 0 ∧ m ≠ 0} →
        coeff m (b - MvPowerSeries.C b0) = 0 := by
      intro m hm
      rw [map_sub, MvPowerSeries.coeff_C]
      by_cases hw : Finsupp.weight W.wt m = 0
      · have hm0 : m = 0 := by
          by_contra h
          exact hm ⟨hw, h⟩
        subst hm0
        rw [if_pos rfl, hb0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
      · have hm0 : m ≠ 0 := by
          rintro rfl
          exact hw (map_zero _)
        rw [if_neg hm0, hb' m hw, sub_zero]
    obtain ⟨c', hc', hcm⟩ := pf_step W ξ ι t g hg (J ^ n) J
      {m : W.σ →₀ ℕ | Finsupp.weight W.wt m = 0 ∧ m ≠ 0} 0 (fun m hm => hm.1)
      (fun m hm => mono_lemma g J hJ m hm.2) ih _ hF x' hx'
    refine ⟨algebraMap O B b0 + c', ?_, ?_⟩
    · rw [map_add (f := _), AlgHom.commutes, hc', ofAdd_zero, map_one, Units.val_one, one_mul,
        ← AlgHom.commutes ξ b0, ← map_add, hxe]
      congr 1
      abel
    · have he : g b - (algebraMap O B b0 + c') = g (b - MvPowerSeries.C b0) - c' := by
        rw [map_sub, hC, AlgHom.commutes]
        ring
      rw [he, pow_succ]
      exact hcm

private theorem pf_agree (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (j : X) (F : MvPowerSeries W.σ O) (hF : F ∈ wtPart O W.wt j)
    (x : W.A) (hx : (x : R) = W.π F) : ι (g F) = t (Multiplicative.ofAdd j) * ξ x := by
  have hF' : ∀ m, Finsupp.weight W.wt m ≠ j → coeff m F = 0 := hF
  have key : ∀ n : ℕ, ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ J ^ n := by
    intro n
    by_cases hj : j = 0
    · subst hj
      obtain ⟨c, hc, hm⟩ := exists_lift_sub_mem_pow_of_mem_wtPart_zero W ξ ι t g hg J hJ h0 n F hF x hx
      exact ⟨c, by rw [hc, ofAdd_zero, map_one, Units.val_one, one_mul], hm⟩
    · obtain ⟨c, hc, hm⟩ := pf_step W ξ ι t g hg (J ^ n) J {m | Finsupp.weight W.wt m = j} j
        (fun m hm => hm)
        (fun m hm => mono_lemma g J hJ m (by
          rintro rfl
          exact hj (hm.symm.trans (map_zero _))))
        (exists_lift_sub_mem_pow_of_mem_wtPart_zero W ξ ι t g hg J hJ h0 n) F (fun m hm => hF' m hm) x hx
      exact ⟨c, hc, (Ideal.mul_le_left : J ^ n * J ≤ J ^ n) hm⟩
  obtain ⟨c0, hc0, -⟩ := key 0
  have hgF : g F = c0 := GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
    obtain ⟨c, hc, hm⟩ := key n
    have hcc : c = c0 := hι (hc.trans hc0.symm)
    rwa [hcc] at hm
  rw [hgF, hc0]

private theorem pf_factor [DecidableEq X] (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) :
    ∃ f : R →ₐ[O] B, ∀ j, ∀ x ∈ W.gr j, ι (f x) = t (Multiplicative.ofAdd j) * ξ x := by
  have hker : ∀ F ∈ RingHom.ker W.π, g F = 0 := by
    intro F hF
    refine pf_vanish W.wt J g hJ F fun j => ?_
    have hmem : wcomp O W.wt j F ∈ RingHom.ker W.π := W.homog F hF j
    have h := pf_agree W ξ ι t g hι hg J hJ h0 j (wcomp O W.wt j F) (wcomp_mem O W.wt j F) 0
      (by
        show (0 : R) = _
        exact (RingHom.mem_ker.mp hmem).symm)
    rw [map_zero, mul_zero] at h
    exact hι (h.trans (map_zero ι).symm)
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom, fun j x hx => ?_⟩
  obtain ⟨F, hF, hFx⟩ := Submodule.mem_map.mp (show (x : R) ∈ W.part j from hx)
  have hmk : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) =
      Ideal.Quotient.mk (RingHom.ker W.π) F := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  have hval : (Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom (x : R) = g F := by
    rw [← hFx]
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F)) = g F
    rw [hmk]
    rfl
  rw [hval]
  exact pf_agree W ξ ι t g hι hg J hJ h0 j F hF x hFx.symm

end SlopeTestRemainingChoices

theorem UpperTheory.weightedPres_exists_algHom_extension_of_adicComplete :
    ∀ {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R)
          {B : Type} [CommRing B] [Algebra O B] (J : Ideal B) [IsAdicComplete J B] (τ : W.A →ₐ[O] B), (∀ s, τ (W.zA s) ∈ J) → ∃ f : R →ₐ[O] B, f.comp W.A.val = τ := by
  intro O X R _ _ _ _ _ _ _ W B _ _ J _ τ hτ
  let g := GlobalTheory.mvEvalAdic O J (fun s => τ (W.zA s)) hτ
  have hgX : ∀ s, g (MvPowerSeries.X s) = τ (W.zA s) := fun s => GlobalTheory.mvEvalAdic_X J _ hτ s
  obtain ⟨f, hf⟩ := pf_factor W τ (AlgHom.id O B) (1 : Multiplicative X →* Bˣ) g
    (fun a b h => h) (fun s => by simp [hgX]) J (fun s => by rw [hgX]; exact hτ s)
    (fun x _ => ⟨τ x, rfl⟩)
  refine ⟨f, AlgHom.ext fun a => ?_⟩
  have key : ∀ y ∈ ⨆ j, W.part j, y ∈ W.A ∧ ∀ h : y ∈ W.A, f y = τ ⟨y, h⟩ := by
    intro y hy
    refine Submodule.iSup_induction (fun j => W.part j)
      (motive := fun y => y ∈ W.A ∧ ∀ h : y ∈ W.A, f y = τ ⟨y, h⟩) hy ?_ ?_ ?_
    · intro j z hz
      exact ⟨W.part_le_A hz, fun h => by simpa using hf j ⟨z, h⟩ hz⟩
    · exact ⟨W.A.zero_mem, fun h => by rw [map_zero]; exact (map_zero τ).symm⟩
    · intro z w hz hw
      exact ⟨W.A.add_mem hz.1 hw.1, fun h => by rw [map_add (f := _), hz.2 hz.1, hw.2 hw.1, ← map_add (f := _)]; rfl⟩
  exact (key a a.2).2 a.2
end

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

section SlopeTestRemainingChoices

open Polynomial in
private theorem md_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem md_ext {O X R K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X]
    [CommRing R] [Algebra O R] (W : WPres O X R) [NormedField K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hw : ∀ x : K, ‖x‖ ≤ 1 → IsIntegral O x)
    (ξ : W.A →ₐ[O] DualNumber K) (h1 : ∀ x, ‖(ξ x).fst‖ ≤ 1) (hz : ∀ s, ‖(ξ (W.zA s)).fst‖ < 1)
    (hfg : ((W.gr 0).map ξ.toLinearMap).FG) :
    ∃ Ξ : R →ₐ[O] DualNumber K, (∀ x : W.A, Ξ x = ξ x) ∧ ∀ x, IsIntegral O (Ξ x) := by
  have hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x := fun x hx => by
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    refine IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  let y : W.σ → DualNumber K := fun s => ξ (W.zA s)
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)
    refine ⟨n, hw' _ ?_⟩
    rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ hn.le (norm_nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set (DualNumber K) := (T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      obtain ⟨a, -, rfl⟩ := this
      exact hw' _ (h1 a)
    · exact hw' _ (hz s).le
    · exact he s
  let B : Subalgebra O (DualNumber K) := Algebra.adjoin O G
  haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  haveI : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  have hB : ∀ x, ξ x ∈ B := fun x => by
    have h2 : (⊤ : Subalgebra O W.A) ≤ B.comap ξ := by
      rw [← gr_gen O R X W]
      refine Algebra.adjoin_le ?_
      rintro a (ha | ⟨s, rfl⟩)
      · have h1 : ξ a ∈ Submodule.span O (T : Set (DualNumber K)) := hT ▸ Submodule.mem_map_of_mem ha
        have h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule :=
          Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
        exact h2 h1
      · exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))
    exact h2 trivial
  have hyB : ∀ s, ξ.codRestrict B hB (W.zA s) ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : ξ.codRestrict B hB (W.zA s) ^ e s = algebraMap O B p *
        ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ := by
      apply Subtype.ext
      show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)
      rw [← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := UpperTheory.weightedPres_exists_algHom_extension_of_adicComplete W J (ξ.codRestrict B hB) hyB
  refine ⟨B.val.comp f, fun x => congrArg Subtype.val (DFunLike.congr_fun hf x), fun x => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := O) (f x)).map B.val

private theorem md_uniq {O σ K : Type} [CommRing O] [Fintype σ] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    (φ ψ : MvPowerSeries σ O →ₐ[O] K) (h1 : ∀ F, ‖φ F‖ ≤ 1) (h2 : ∀ F, ‖ψ F‖ ≤ 1)
    (hz : ∀ s, ‖φ (MvPowerSeries.X s)‖ < 1) (h : ∀ s, φ (MvPowerSeries.X s) = ψ (MvPowerSeries.X s)) : φ = ψ := by
  let V : Subalgebra O K :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg _) hb
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      algebraMap_mem' := fun a => by
        have := h1 (algebraMap O _ a)
        rwa [AlgHom.commutes] at this }
  let ρ : NNReal := Finset.univ.sup fun s => ‖φ (MvPowerSeries.X s)‖₊
  have hρ : ρ < 1 := (Finset.sup_lt_iff (by norm_num)).2 fun s _ => hz s
  let J : Ideal V :=
    { carrier := {x | ‖(x : K)‖ ≤ ρ}
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        show ‖(a : K) * b‖ ≤ ρ
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) a.2).trans hb }
  have key : ∀ n : ℕ, ∀ z ∈ J ^ n, ‖(z : K)‖ ≤ (ρ : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z _; rw [pow_zero]; exact z.2
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [Subalgebra.coe_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) hb (norm_nonneg _) (pow_nonneg ρ.2 _)
      · rw [Subalgebra.coe_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  have hJ : ∀ s, φ.codRestrict V h1 (MvPowerSeries.X s) ∈ J := fun s =>
    Finset.le_sup (f := fun s => ‖φ (MvPowerSeries.X s)‖₊) (Finset.mem_univ s)
  have he : ∀ s, φ.codRestrict V h1 (MvPowerSeries.X s) = ψ.codRestrict V h2 (MvPowerSeries.X s) :=
    fun s => Subtype.ext (h s)
  refine AlgHom.ext fun F => ?_
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one ρ.2 hρ) fun n => ?_
  exact key n _ (GlobalTheory.algHom_sub_mem_pow (φ.codRestrict V h1) (ψ.codRestrict V h2) hJ (fun s => he s ▸ hJ s)
    (fun s => by rw [he s, sub_self]; exact zero_mem _) F)

private theorem md_main {O R S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] (hinj : Function.Injective (algebraMap O K))
    (hw : ∀ x : K, IsIntegral O x ↔ ‖x‖ ≤ 1)
    (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S) (hq : Function.Surjective qh) {κ : Type} (g : κ → W.A)
    (hker : RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R))) (hM : M2 W.gr (Ideal.span (Set.range g)))
    (f : S →ₐ[O] K) (hf : IsLocPt f) (D : W.A →ₗ[O] K) (hD : D ∈ PtDer (f.comp (qh.comp W.A.val)) K)
    (hDI : ∀ y ∈ Ideal.span (Set.range g), D y = 0) :
    ∃ F : S →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y := by
  have hO : ∀ a : O, ‖algebraMap O K a‖ ≤ 1 := fun a => (hw _).1 isIntegral_algebraMap
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := fun x => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have := hf _ ha
    rw [map_sub, AlgHom.commutes] at this
    rw [← sub_add_cancel (f x) (algebraMap O _ a)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le this.le (hO a))
  have hz : ∀ s, ‖f (qh (W.z s))‖ < 1 := fun s => hf _ (by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s))
  letI : Module Oᵐᵒᵖ K := Module.compHom K ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O K := ⟨fun _ _ => rfl⟩
  obtain ⟨τ, hτ⟩ := (der_hom O W.A K K (f.comp (qh.comp W.A.val)) D).1 ⟨D, hD, rfl⟩
  have hg0 : ∀ i, τ (g i) = 0 := fun i => by
    have h1 : qh (g i) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    ext
    · rw [(hτ _).1]
      show f (qh (g i)) = 0
      rw [h1, map_zero]
    · rw [(hτ _).2]
      exact hDI _ (Ideal.subset_span ⟨i, rfl⟩)
  have hτI : ∀ y ∈ Ideal.span (Set.range g), τ y = 0 := by
    have : Ideal.span (Set.range g) ≤ RingHom.ker τ := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hg0 i)
    exact this
  have hfg : ((W.gr 0).map τ.toLinearMap).FG := by
    have := Submodule.FG.map (Ideal.Quotient.liftₐ _ τ hτI).toLinearMap hM
    rw [← Submodule.map_comp] at this
    exact this
  obtain ⟨Ξ, hΞ, hint⟩ := md_ext W (K := K) hinj (fun x => (hw x).2) τ (fun x => by rw [(hτ x).1]; exact hf1 _)
    (fun s => by rw [(hτ _).1]; exact hz s) hfg
  have hfst : (dualFst Ξ).comp W.π = (f.comp qh).comp W.π := by
    have e : ∀ s, (Ξ (W.z s)).fst = f (qh (W.z s)) := fun s => by
      have := hΞ (W.zA s)
      rw [show W.z s = (W.zA s : R) from rfl, this, (hτ _).1]
      rfl
    refine md_uniq _ _ (fun F => ?_) (fun F => hf1 _) (fun s => ?_) e
    · exact (hw _).1 ((hint (W.π F)).map (TrivSqZeroExt.fstHom O K K))
    · exact (congrArg norm (e s)).trans_lt (hz s)
  have hK : ∀ x ∈ RingHom.ker qh, Ξ x = 0 := by
    have : RingHom.ker qh ≤ RingHom.ker Ξ := by
      rw [hker]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact (hΞ _).trans (hg0 i)
    exact this
  let F : S →ₐ[O] DualNumber K := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hK).comp
    (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hF : ∀ x, F (qh x) = Ξ x := by
    intro x
    have : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (qh x) = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [F, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨F, AlgHom.ext fun x => ?_, fun y => by rw [hF, hΞ, (hτ y).2]⟩
  obtain ⟨x, rfl⟩ := hq x
  obtain ⟨G, rfl⟩ := W.surj x
  show (F (qh (W.π G))).fst = _
  rw [hF]
  exact DFunLike.congr_fun hfst G

end SlopeTestRemainingChoices

theorem UpperTheory.exists_dualNumber_point_of_pointDerivation_vanishing :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ f : S →ₐ[c.O] PadicAlgCl l, IsLocPt f → ∀ D ∈ PtDer (f.comp (qh.comp W.A.val)) (PadicAlgCl l), (∀ y ∈ Ideal.span (Set.range g), D y = 0) →
            ∃ F : S →ₐ[c.O] DualNumber (PadicAlgCl l), dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y := by
  intro l _ c R S _ _ _ _ _ _ W h qh hq κ g w _ hker hM f hf D hD hDI
  haveI := c.dvr
  haveI := c.fin
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite _ _
  exact md_main Subtype.val_injective (fun x => ⟨fun hx => (md_intIff x).1 (isIntegral_trans (A := c.O) x hx),
    fun hx => ((md_intIff x).2 hx).tower_top⟩) W h qh hq g hker hM f hf D hD hDI
