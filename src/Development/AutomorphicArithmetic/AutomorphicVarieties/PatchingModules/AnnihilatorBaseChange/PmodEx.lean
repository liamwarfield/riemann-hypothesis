module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Patched

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmulPowLeOfStep
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.smul_pow_le_of_step :
    ∀ (R : Type) [CommRing R] (𝔞 I 𝔶 : Ideal R) (f : R),
      (∀ (X : Type) [AddCommGroup X] [Module R X] (X₀ : Type) [AddCommGroup X₀] [Module R X₀] (φ : X₀ →ₗ[R] X) (ψ : X →ₗ[R] X₀) (n : R), (∀ x, φ (ψ x) = n • x) → n ∣ f →
        (𝔞 • ⊤ : Submodule R X₀) ≤ I • ⊤ → ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R X) ≤ I • ⊤) ∧
      (∀ (M : Type) [AddCommGroup M] [Module R M], ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶) • ⊤ →
        ∀ k : ℕ, ((Ideal.span {f ^ k} * 𝔞 ^ k) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶 ^ k) • ⊤) := by
  intro R _ 𝔞 I 𝔶 f
  refine ⟨?_, ?_⟩
  · intro X _ _ X₀ _ _ φ ψ n hn hnf h
    obtain ⟨c, rfl⟩ := hnf
    refine Submodule.smul_le.2 ?_
    intro r hr x _
    obtain ⟨a, ha, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    have h1 : a • ψ x ∈ (I • ⊤ : Submodule R X₀) :=
      h (Submodule.smul_mem_smul ha Submodule.mem_top)
    have h2 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X) := by
      have h3 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X₀).map φ := Submodule.mem_map_of_mem h1
      rw [Submodule.map_smul''] at h3
      exact Submodule.smul_mono le_rfl le_top h3
    have h4 : (n * c * a) • x = c • φ (a • ψ x) := by
      rw [map_smul, hn, smul_smul, smul_smul]
      congr 1
      ring
    rw [h4]
    exact Submodule.smul_mem _ c h2
  · intro M _ _ h k
    rw [← Ideal.span_singleton_pow, ← mul_pow]
    generalize Ideal.span {f} * 𝔞 = b at h
    induction k with
    | zero => simp
    | succ k ih =>
      have hle : (I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶) ≤ I ⊔ 𝔶 ^ (k + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup (𝔶 ^ k), pow_succ]
        refine sup_le (le_sup_of_le_left Ideal.mul_le_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
      calc (b ^ (k + 1) • ⊤ : Submodule R M) = b • (b ^ k • ⊤) := by
            rw [pow_succ', mul_smul]
        _ ≤ b • ((I ⊔ 𝔶 ^ k) • ⊤) := smul_mono_right b ih
        _ = (I ⊔ 𝔶 ^ k) • (b • ⊤) := by
            rw [← mul_smul, ← mul_smul, mul_comm]
        _ ≤ (I ⊔ 𝔶 ^ k) • ((I ⊔ 𝔶) • ⊤) := smul_mono_right _ h
        _ = ((I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶)) • ⊤ := by rw [mul_smul]
        _ ≤ (I ⊔ 𝔶 ^ (k + 1)) • ⊤ := Submodule.smul_mono_left hle
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimConst
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.const_bijective :
    ∀ (R ι : Type) [CommRing R] (U : Ultrafilter ι) (m : Ideal R) (Z : Type) [AddCommGroup Z] [Module R Z], IsAdicComplete m Z →
      (∀ j : ℕ, Finite (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) →
      Function.Bijective fun z : Z => ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) fun _ => z := by
  intro R ι _ U m Z _ _ hc hfin
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) (fun _ => a - b) = 0 := by
      have h1 : (fun _ : ι => a - b) = (fun _ : ι => a) - (fun _ : ι => b) := rfl
      rw [h1, map_sub]
      exact sub_eq_zero.2 hab
    rw [ULim.mk_eq_zero] at h0
    refine sub_eq_zero.1 (IsHausdorff.haus hc.toIsHausdorff _ fun j => ?_)
    obtain ⟨_, h⟩ := (h0 j).exists
    exact SModEq.zero.2 h
  · obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
    have hz : ∀ j : ℕ, ∃ z : Z, ∀ᶠ i in (U : Filter ι), p i ≡ z [SMOD (m ^ j • ⊤ : Submodule R Z)] := by
      intro j
      haveI := hfin j
      obtain ⟨q, hq⟩ := Ultrafilter.eq_pure_of_finite
        (U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)))
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨z, ?_⟩
      have h : ({Submodule.Quotient.mk z} : Set (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) ∈
          U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)) := by
        rw [hq]; simp
      exact h
    choose z hz using hz
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := z) (fun {j k} hjk => by
      obtain ⟨i, h1, h2⟩ := ((hz j).and (hz k)).exists
      exact h1.symm.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk))))
    refine ⟨L, ?_⟩
    show ULim.mk _ _ _ _ = _
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
    intro j
    refine (hz j).mono fun i hi => ?_
    exact SModEq.sub_mem.1 (hi.trans (hL j)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegPS
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem order_of_mem_pow {O σ : Type} [CommRing O] (n : ℕ) :
    ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ n, (n : ℕ∞) ≤ g.order := by
  have h1 : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      ((1 : ℕ) : ℕ∞) ≤ g.order := by
    intro g hg
    have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ≤
        RingHom.ker (constantCoeff : MvPowerSeries σ O →+* O) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    refine nat_le_order fun d hd => ?_
    have hd0 : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst hd0
    simpa using hle hg
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · refine le_trans ?_ le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih x hx) (h1 y hy)
    · exact le_trans (le_min hx hy) min_order_le_add

private theorem coeff_mem_of_mem_map {O σ : Type} [CommRing O] (I : Ideal O) (g : MvPowerSeries σ O)
    (hg : g ∈ I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)) (d : σ →₀ ℕ) : coeff d g ∈ I := by
  have hle : I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) ≤
      RingHom.ker (MvPowerSeries.map (σ := σ) (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have h := congrArg (coeff d) (RingHom.mem_ker.1 (hle hg))
  rw [coeff_map, map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

private theorem monoVal_X_eq {O σ : Type} [CommRing O] (α : σ →₀ ℕ) :
    GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ O) α = monomial α 1 := by
  simp only [GlobalTheory.monoVal, Finsupp.prod, X_pow_eq, prod_monomial, Finset.prod_const_one]
  congr 2
  exact Finsupp.sum_single α

private theorem eq_of_le_of_degree_eq {σ : Type} {α β : σ →₀ ℕ} (h : β ≤ α)
    (hd : β.degree = α.degree) : β = α := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add (f := _)] at hd
  have : γ = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.qRegAt_mvPowerSeries :
    ∀ (Λ σ : Type) [CommRing Λ] [Finite σ] (I : Ideal Λ) (a : ℕ),
      QRegAt (MvPowerSeries σ Λ) (MvPowerSeries.X : σ → MvPowerSeries σ Λ) (I.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) a := by
  intro Λ σ _ _ I a c hc α
  classical
  haveI := Fintype.ofFinite σ
  rw [smul_eq_mul, Ideal.mul_top] at hc ⊢
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  have h0 : MvPowerSeries.coeff α.1 u = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ u hu))
    rw [α.2]
    exact_mod_cast Nat.lt_succ_self a
  have h1 : MvPowerSeries.coeff α.1 (u + v) = MvPowerSeries.constantCoeff (c α) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [huv, map_sum, Finset.sum_eq_single α]
    · rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul]
      simp
    · intro β _ hβ
      rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul, if_neg]
      intro hle
      exact hβ (Subtype.ext (eq_of_le_of_degree_eq hle (β.2.trans α.2.symm)))
    · simp
  have h2 : MvPowerSeries.constantCoeff (c α) ∈ I := by
    rw [← h1, map_add (f := _), h0, zero_add]
    exact coeff_mem_of_mem_map I v hv _
  have h3 : c α = (c α - MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))) +
      MvPowerSeries.C (MvPowerSeries.constantCoeff (c α)) := by ring
  rw [h3]
  exact Submodule.add_mem_sup (mem_span_X _ (by simp)) (Ideal.mem_map_of_mem _ h2)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteModuleMaximalIdealAnnihilation
theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.kjMap :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (k j : ℕ), (kjIdeal Λ σ k j).map s = Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j := by
  intro Λ R σ _ _ _ _ s k j
  rw [kjIdeal, Ideal.map_sup, Ideal.map_pow, Ideal.map_span, ← Set.range_comp, Ideal.map_map, Ideal.map_pow]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.QuotientRegularAtOfQuotientFreeOverPowerSeries
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.quotientRegularAt_of_quotient_free_over_powerSeries :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (M : Type) [AddCommGroup M] [Module R M] (a j r : ℕ) (e : (M ⧸ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ (a + 1) j)), (∀ z m, e (s z • m) = z • e m) → QRegAt M (fun a => s (MvPowerSeries.X a)) (((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) a := by
  intro Λ R σ _ _ _ _ s M _ _ a j r e he c hc α
  classical
  rw [← kjMap Λ R σ s (a + 1) j] at hc
  have hsurj := Ideal.Quotient.mk_surjective (I := kjIdeal Λ σ (a + 1) j)
  choose t ht using fun β i => hsurj (e (Submodule.Quotient.mk (c β)) i)
  have hmono : ∀ β : σ →₀ ℕ, GlobalTheory.monoVal (fun a => s (MvPowerSeries.X a)) β =
      s (GlobalTheory.monoVal MvPowerSeries.X β) := fun β => by
    simp only [GlobalTheory.monoVal, Finsupp.prod, map_prod, map_pow]
  have h0 := congrArg e ((Submodule.Quotient.mk_eq_zero _).2 hc)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← Submodule.mkQ_apply, map_sum, map_sum] at h0
  simp only [map_smul, hmono, he, Submodule.mkQ_apply] at h0
  have hL : ∀ i, t α i ∈ kjIdeal Λ σ 1 j := by
    intro i
    have h1 := congrFun h0 i
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, ← ht, Pi.zero_apply] at h1
    have h2 : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ Λ) β.1 * t β i) ∈ kjIdeal Λ σ (a + 1) j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← h1]
      rfl
    have h3 := qRegAt_mvPowerSeries Λ σ (maximalIdeal Λ ^ j) a (fun β => t β i)
      (by simpa [kjIdeal, Ideal.map_pow] using h2) α
    simpa [kjIdeal, Ideal.map_pow] using h3
  have hs := Submodule.Quotient.mk_surjective ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)
  choose m hm using fun i : Fin r => hs (e.symm (Pi.single i 1))
  have h4 : c α - ∑ i, s (t α i) • m i ∈ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.eq]
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply _ (∑ i, _), map_sum, map_sum]
    simp only [map_smul, he, Submodule.mkQ_apply, hm, AddEquiv.apply_symm_apply]
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [← ht, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hle : kjIdeal Λ σ (a + 1) j ≤ kjIdeal Λ σ 1 j := by
    unfold kjIdeal
    exact sup_le_sup_right (Ideal.pow_le_pow_right (by omega)) _
  have h5 : c α ∈ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R M) := by
    rw [← sub_add_cancel (c α) (∑ i, s (t α i) • m i)]
    refine add_mem (Submodule.smul_mono_left (Ideal.map_mono hle) h4) (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hL i)) Submodule.mem_top
  rw [kjMap, pow_one] at h5
  exact h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsUltraLimitPairOfEventualQuotientMaps
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.UlimQuot
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.ulimQuot :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)] (ν : ℕ → ℕ) (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))), Antitone I → Tendsto ν F atTop → ∃ Φ : ULim F I M →ₗ[R] ULim F I M', ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) = φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p' := by
  intro R _ F I M M' _ _ _ _ ν φ hI hν
  have hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j := fun j =>
    (tendsto_atTop.1 hν j).mono fun N hN => hI hN
  have he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R),
      (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) =
        (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ := by
    intro X _ _ K J
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X,
      (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
        (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X) := by
    intro X _ _ K J hKJ x hx
    rw [he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hd : x - y ∈ (K • ⊤ : Submodule R X) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    have := Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy
    rwa [sub_add_cancel] at this
  have hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X),
      x ∈ (J • ⊤ : Submodule R X) →
        (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
          (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) := by
    intro X _ _ K J x hx
    rw [he]
    exact ⟨x, hx, rfl⟩
  have hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))),
      z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _) := by
    intro N j z hz
    have hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle ⟨z, hz, rfl⟩
  let π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)
  have hπ : Function.Surjective π := fun q =>
    ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,
      funext fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M') := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    rw [ULim.mk_eq_zero]
    intro j
    refine (hev j).mono fun N hN => ?_
    have hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N)) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrFun hp N
    exact Submodule.smul_mono_left hN hpN
  let φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))
  let Φ0 : (∀ N, M N) →ₗ[R] ULim F I M' :=
    ((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp
      ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')
  have hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p' := by
    intro p p' h
    simp only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h]
    have hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [hs, Submodule.liftQ_apply]
  have hnull : uNull F I M ≤ LinearMap.ker Φ0 := by
    intro p hp
    have hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N)) := hp
    rw [LinearMap.mem_ker]
    obtain ⟨p', hp'⟩ := hπ (φ' p)
    rw [hΦ0 p p' hp', ULim.mk_eq_zero]
    intro j
    refine ((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
    apply hlift (I (ν N)) (I j) h2
    have hN : π p' N = φ N (Submodule.Quotient.mk (p N)) := congrFun hp' N
    change π p' N ∈ _
    rw [hN]
    exact hφ N j _ (hmk _ _ _ h1)
  refine ⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩
  change (uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  obtain ⟨q, hq⟩ := hπ (φ' p)
  rw [hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
  intro j
  refine (h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
  apply Submodule.smul_mono_left h2
  rw [← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]
  have hN : π q N = φ N (Submodule.Quotient.mk (p N)) := congrFun hq N
  exact sub_eq_zero.2 hN
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem const_bij {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (U : Ultrafilter ℕ)
    (m : Ideal R) (I : ℕ → Ideal R) (hc : IsAdicComplete m X)
    (hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)))
    (hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤) :
    Function.Bijective
      (ULim.mk (U : Filter ℕ) I (fun _ => X) ∘ₗ LinearMap.pi fun _ : ℕ => (LinearMap.id : X →ₗ[R] X)) := by
  have hb := ULim.const_bijective R ℕ U m X hc hf
  have key : ∀ p q : ℕ → X, ULim.mk (U : Filter ℕ) I (fun _ => X) p = ULim.mk (U : Filter ℕ) I (fun _ => X) q ↔
      ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) p =
        ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) q := by
    intro p q
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero, ← sub_eq_zero (a := ULim.mk _ _ _ p), ← map_sub,
      ULim.mk_eq_zero]
    simp only [hI]
  refine ⟨fun a b hab => hb.1 ((key (fun _ => a) (fun _ => b)).1 hab), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
  obtain ⟨z, hz⟩ := hb.2 (ULim.mk _ _ _ p)
  exact ⟨z, (key (fun _ => z) p).2 hz⟩

private theorem comp_smul {R : Type} [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type)
    [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)]
    (ν : ℕ → ℕ) (hν : Tendsto ν F atTop) (hI : Antitone I) (f : R)
    (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))))
    (ψ : ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))))
    (h : ∀ᶠ N in F, ∀ z, ψ N (φ N z) = f • z)
    (Φ : ULim F I M →ₗ[R] ULim F I M') (Ψ : ULim F I M' →ₗ[R] ULim F I M)
    (hΦ : ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p')
    (hΨ : ∀ (p : ∀ N, M' N) (p' : ∀ N, M N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      ψ N (Submodule.Quotient.mk (p N))) → Ψ (ULim.mk F I M' p) = ULim.mk F I M p') (z : ULim F I M) :
    Ψ (Φ z) = f • z := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ z
  choose q hq using fun N => Submodule.Quotient.mk_surjective _ (φ N (Submodule.Quotient.mk (p N)))
  rw [hΦ p q (Eventually.of_forall hq), ← map_smul]
  refine hΨ q (f • p) (h.mono fun N hN => ?_)
  rw [hq, hN]
  rfl

theorem UpperTheory.V.Pa.Core.exists_ultraLimit_pair_of_eventual_quotient_maps :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∃ (Φ : X →ₗ[R] ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M) (Ψ : ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M →ₗ[R] X), (∀ z, Φ (Ψ z) = f • z) ∧ ∀ z, Ψ (Φ z) = f • z := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hU hs hy h
  classical
  letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
  haveI : IsScalarTower Λ R X := IsScalarTower.of_algebraMap_smul fun a x => (hs a x).symm
  set m : Ideal R := (maximalIdeal Λ).map (s.comp MvPowerSeries.C) with hm
  set I : ℕ → Ideal R := fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ m ^ j with hIdef
  have hkj : ∀ j, (kjIdeal Λ σ 1 j).map s = I j := fun j => by rw [kjMap, pow_one]
  have h' : ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ (I j • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I j • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I j • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I j • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro j
    rw [← hkj j]
    exact h j
  obtain ⟨ν, hν, hP⟩ := exists_diag _ hU _ h'
  have hanti : Antitone I := fun a b hab => sup_le_sup_left (Ideal.pow_le_pow_right hab) _
  have hex : ∀ N, ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro N
    by_cases hN : ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z
    · obtain ⟨φ, ψ, hh⟩ := hN
      exact ⟨φ, ψ, fun _ => hh⟩
    · exact ⟨0, 0, fun hh => absurd hh hN⟩
  choose φ ψ hφψ using hex
  have hgood := hP.mono fun N hN => hφψ N (hN _ le_rfl)
  obtain ⟨Φ, hΦ⟩ := ulimQuot R U I (fun _ => X) M ν φ hanti hν
  obtain ⟨Ψ, hΨ⟩ := ulimQuot R U I M (fun _ => X) ν ψ hanti hν
  have h1 := comp_smul U I (fun _ => X) M ν hν hanti f φ ψ (hgood.mono fun _ hN => hN.2) Φ Ψ hΦ hΨ
  have h2 := comp_smul U I M (fun _ => X) ν hν hanti f ψ φ (hgood.mono fun _ hN => hN.1) Ψ Φ hΨ hΦ
  have hc : IsAdicComplete m X :=
    (IsAdicComplete.map_algebraMap_iff (S := R) (maximalIdeal Λ) X).2 (AnnihilatorQuotientFinite.finCompl Λ X _)
  have hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)) := by
    intro j
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := inferInstanceAs (Finite (ResidueField Λ))
    haveI : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
    haveI : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
      Submodule.finite_quotient_smul _ Module.Finite.fg_top
    have hle : (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X) ≤ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ := by
      refine Submodule.smul_le.2 fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, hs]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (s.comp MvPowerSeries.C) ha
    haveI : Finite (X ⧸ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ) :=
      Finite.of_surjective _ (Submodule.factor_surjective hle)
    exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv Λ _).toEquiv
  have hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤ := by
    intro j
    have h0 : (Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) • ⊤ : Submodule R X) = ⊥ := by
      rw [← Submodule.le_annihilator_iff, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_annihilator.2 fun x _ => hy a x
    show ((_ ⊔ _ : Ideal R) • ⊤ : Submodule R X) = _
    rw [Submodule.sup_smul, h0, bot_sup_eq]
  let e := LinearEquiv.ofBijective _ (const_bij U m I hc hf hI)
  refine ⟨Φ ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ Ψ, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact h2 z
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, map_smul, LinearEquiv.symm_apply_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsPowMaximalIdealSmulFiniteEqZero
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem exists_pow_maximalIdeal_smul_finite_eq_zero (R Q : Type) [CommRing R] [IsLocalRing R] [AddCommGroup Q] [Module R Q] [Finite Q] :
    ∃ c : ℕ, ∀ a ∈ maximalIdeal R ^ c, ∀ z : Q, a • z = 0 :=
  _root_.UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero R Q

private theorem finite_quotient_of_power_maximal_ideal_le (Λ R X : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing Λ]
    [Finite (ResidueField Λ)] [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X] (t : Λ →+* R)
    (ht : ∀ (a : Λ) (x : X), a • x = t a • x) (j : ℕ) (K : Ideal R) (hK : (maximalIdeal Λ).map t ^ j ≤ K) :
    Finite (X ⧸ (K • ⊤ : Submodule R X)) := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X), x ∈ (K • ⊤ : Submodule R X) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      rw [ht]
      refine Submodule.smul_mem_smul (hK ?_) Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  let g : (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) → (X ⧸ (K • ⊤ : Submodule R X)) := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  refine Finite.of_surjective g fun z => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem UpperTheory.V.Pa.Core.finite_quotient_of_ultrafilter_limit_module :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [Finite (ResidueField Λ)] [IsLocalRing R] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∀ k j : ℕ, ∃ c : ℕ, ∀ᶠ N in (U : Filter ℕ), ∀ a ∈ maximalIdeal R ^ c, ∀ x : M N, (f ^ k * a) • x ∈ ((Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) • ⊤ : Submodule R (M N)) := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hC _ h k j
  have hK := kjMap Λ R σ s 1 j
  haveI : Finite (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) :=
    finite_quotient_of_power_maximal_ideal_le Λ R X (s.comp MvPowerSeries.C) hC j _ (hK ▸ le_sup_right)
  obtain ⟨c, hc⟩ := exists_pow_maximalIdeal_smul_finite_eq_zero R (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))
  refine ⟨c * k, (h j).mono ?_⟩
  rintro N ⟨φ, ψ, hφψ, -⟩ a ha x
  have h1 : ((Ideal.span {f} * maximalIdeal R ^ c) • ⊤ : Submodule R (M N)) ≤ (kjIdeal Λ σ 1 j).map s • ⊤ := by
    refine Submodule.smul_le.2 ?_
    intro r hr y _
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, mul_comm, mul_smul, ← hφψ, ← map_smul,
      hc b hb, map_zero]
  rw [hK, pow_one, sup_comm] at h1
  have h2 := (smul_pow_le_of_step R (maximalIdeal R ^ c) _ _ f).2 (M N) h1 k
  rw [sup_comm]
  refine h2 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_) Submodule.mem_top)
  rwa [← pow_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YCplMemOf
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem yCpl_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion (I.map (algebraMap R S)) S) :
    x ∈ (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      AdicCompletion.eval (I.map (algebraMap R S)) S n x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), Ideal.smul_top_eq_map,
    ← Ideal.map_pow, Ideal.map_map, Submodule.restrictScalars_mem, ← IsScalarTower.algebraMap_eq]

private theorem yCpl_mem_of {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (s : S) :
    algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s ∈
      (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      s ∈ (I ^ n).map (algebraMap R S) := by
  rw [yCpl_mem I hI, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, Submodule.mkQ_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

theorem UpperTheory.V.Pa.Core.yCpl :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R), IsYCpl y f (AdicCompletion ((Ideal.span (Set.range y)).map (algebraMap R (Localization.Away f))) (Localization.Away f)) := by
  intro R σ _ _ _ y f
  set S := Localization.Away f
  set I : Ideal R := Ideal.span (Set.range y)
  set A := AdicCompletion (I.map (algebraMap R S)) S
  have hI : I.FG := Submodule.fg_span (Set.finite_range y)
  have hS : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  have hRA : ∀ r : R, algebraMap R A r = algebraMap S A (algebraMap R S r) := fun r =>
    IsScalarTower.algebraMap_apply R S A r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, ?_, ?_, ?_⟩
  · rw [hRA]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · intro n x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (I.map (algebraMap R S)) S n x)
    obtain ⟨⟨r, _, ⟨k, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) s
    simp only at hr
    refine ⟨k, r, ?_⟩
    have hmem : x - algebraMap S A s ∈ (I ^ n).map (algebraMap R A) := by
      rw [yCpl_mem I hI, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, ← hs,
        Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, sub_self]
    have heq : algebraMap R A f ^ k * x - algebraMap R A r
        = algebraMap R A (f ^ k) * (x - algebraMap S A s) := by
      rw [mul_sub, hRA r, ← hr, map_mul, ← hRA (f ^ k), map_pow]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hmem
  · intro n r hr
    rw [hRA, yCpl_mem_of I hI] at hr
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S (I ^ n) r).1 hr
    exact ⟨k, hm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FibEquiv
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem fib_tmul_zero {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (t : S ⊗[R] X) : k • t = 0 := by
  have hI : Ideal.span (Set.range y) ≤ Module.annihilator R X := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact Module.mem_annihilator.mpr (hX a)
  have hmap : (Ideal.span (Set.range y)).map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] X) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hr' := Module.mem_annihilator.mp (hI hr)
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro u
    rw [algebraMap_smul]
    induction u using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | tmul a b => rw [← TensorProduct.tmul_smul, hr' b, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  exact Module.mem_annihilator.mp (hmap hk) t

private theorem fib_tmul_zero' {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (x : X) : k ⊗ₜ[R] x = 0 := by
  have := fib_tmul_zero y S X hX k hk (1 ⊗ₜ[R] x)
  rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this

private theorem fib_bij {R σ : Type} [CommRing R] (y : σ → R) (S BB : Type) [CommRing S] [Algebra R S]
    [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (hD : ∀ b : BB, ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB))
    (hS : ∀ s : S, algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) →
      s ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) :
    Function.Bijective (LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap) := by
  classical
  set IB := (Ideal.span (Set.range y)).map (algebraMap R BB) with hIB
  choose sel hsel using hD
  have hz : ∀ (s1 s2 : S) (x : X), algebraMap S BB s1 - algebraMap S BB s2 ∈ IB →
      s1 ⊗ₜ[R] x = s2 ⊗ₜ[R] x := by
    intro s1 s2 x h12
    have h0 := fib_tmul_zero' y S X hX (s1 - s2) (hS _ (by rwa [map_sub])) x
    rwa [TensorProduct.sub_tmul, sub_eq_zero] at h0
  have hrt : ∀ (s : S) (x : X), LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  let F : BB →ₗ[R] X →ₗ[R] S ⊗[R] X := LinearMap.mk₂ R (fun b x => sel b ⊗ₜ[R] x)
    (fun b1 b2 x => by
      rw [← TensorProduct.add_tmul]
      apply hz
      have e : algebraMap S BB (sel (b1 + b2)) - algebraMap S BB (sel b1 + sel b2) = (b1 - algebraMap S BB (sel b1)) + (b2 - algebraMap S BB (sel b2)) - (b1 + b2 - algebraMap S BB (sel (b1 + b2))) := by
        rw [map_add (f := _)]
        ring
      rw [e]
      exact sub_mem (add_mem (hsel b1) (hsel b2)) (hsel _))
    (fun r b x => by
      rw [TensorProduct.smul_tmul']
      apply hz
      have e : algebraMap S BB (sel (r • b)) - algebraMap S BB (r • sel b) = algebraMap R BB r * (b - algebraMap S BB (sel b)) - (r • b - algebraMap S BB (sel (r • b))) := by
        rw [Algebra.smul_def r (sel b), map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r b]
        ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ (hsel b)) (hsel _))
    (fun b x1 x2 => TensorProduct.tmul_add _ _ _)
    (fun r b x => TensorProduct.tmul_smul _ _ _)
  let g := TensorProduct.lift F
  have hg : ∀ (b : BB) (x : X), g (b ⊗ₜ[R] x) = sel b ⊗ₜ[R] x := fun b x => by
    simp [g, F]
  constructor
  · apply Function.LeftInverse.injective (g := g)
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [hrt, hg]
      apply hz
      have e : algebraMap S BB (sel (algebraMap S BB s)) - algebraMap S BB s = -(algebraMap S BB s - algebraMap S BB (sel (algebraMap S BB s))) := by ring
      rw [e]
      exact neg_mem (hsel _)
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b x =>
      refine ⟨sel b ⊗ₜ[R] x, ?_⟩
      rw [hrt]
      have h0 := fib_tmul_zero' y BB X hX (b - algebraMap S BB (sel b)) (hsel b) x
      rwa [TensorProduct.sub_tmul, sub_eq_zero, eq_comm] at h0
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [map_add (f := _), ha, hc]⟩

private theorem fib_dense {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (b : BB) :
    ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) := by
  obtain ⟨k, r, hkr⟩ := h.dense 1 b
  rw [pow_one] at hkr
  set v := algebraMap S BB (IsLocalization.Away.invSelf (S := S) f) with hv
  have hvf : v * algebraMap R BB f = 1 := by
    rw [hv, IsScalarTower.algebraMap_apply R S BB f, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  refine ⟨algebraMap R S r * (IsLocalization.Away.invSelf (S := S) f) ^ k, ?_⟩
  have : b - algebraMap S BB (algebraMap R S r * IsLocalization.Away.invSelf (S := S) f ^ k) = v ^ k * (algebraMap R BB f ^ k * b - algebraMap R BB r) := by
    rw [map_mul, map_pow, ← hv, ← IsScalarTower.algebraMap_apply]
    calc b - algebraMap R BB r * v ^ k = (v * algebraMap R BB f) ^ k * b - algebraMap R BB r * v ^ k := by rw [hvf, one_pow, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hkr

private theorem fib_strict {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (s : S) (hs : algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB)) :
    s ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
  obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) s
  obtain ⟨k, hk⟩ := m.2
  simp only at hrm
  rw [← hk] at hrm
  have hB : algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ 1).map (algebraMap R BB) := by
    rw [pow_one, IsScalarTower.algebraMap_apply R S BB r, ← hrm, map_mul]
    exact Ideal.mul_mem_right _ _ hs
  obtain ⟨k', hk'⟩ := h.strict 1 r hB
  rw [pow_one] at hk'
  have hmem : s * algebraMap R S (f ^ (k' + k)) ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
    rw [pow_add, map_mul, mul_comm (algebraMap R S (f ^ k')), ← mul_assoc, hrm, ← map_mul, mul_comm]
    exact Ideal.mem_map_of_mem _ hk'
  have hu : IsUnit (algebraMap R S (f ^ (k' + k))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow _
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have : s = s * algebraMap R S (f ^ (k' + k)) * w := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hmem

theorem UpperTheory.V.Pa.Core.fibEquiv :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB] (X : Type) [AddCommGroup X] [Module R X] (MM : Type) [AddCommGroup MM] [Module S MM] [Module BB MM] [IsScalarTower S BB MM] (q : MM →ₗ[S] S ⊗[R] X), IsYCpl y f BB → (∀ a (x : X), y a • x = 0) → Function.Surjective q → LinearMap.ker q = (Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ → Nonempty ((MM ⧸ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)) ≃ₗ[BB] BB ⊗[R] X) := by
  intro R σ _ _ y f S BB _ _ _ _ _ _ _ X _ _ MM _ _ _ _ q hC hX hq hker
  have hbij := fib_bij y S BB X hX (fun b => fib_dense y f S BB hC b)
    (fun s hs => fib_strict y f S BB hC s hs)
  set rT := LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap with hrTdef
  have hrt : ∀ (s : S) (x : X), rT (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  have hrtS : ∀ (s : S) (t : S ⊗[R] X), rT (s • t) = algebraMap S BB s • rT t := by
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hrt, hrt, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add u v hu hv => rw [smul_add, map_add (f := _), map_add (f := _), hu, hv, smul_add]
  have hJ : Ideal.span (Set.range fun a => algebraMap R BB (y a)) = (Ideal.span (Set.range y)).map (algebraMap R BB) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hL : ∀ i ∈ (Ideal.span (Set.range y)).map (algebraMap R BB), ∀ m : MM, q (i • m) = 0 := by
    intro i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨r, hr, rfl⟩ m
      rw [IsScalarTower.algebraMap_apply R S BB, algebraMap_smul, ← LinearMap.mem_ker, hker]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    · intro m
      rw [zero_smul, map_zero]
    · intro a c _ _ ha hc m
      rw [add_smul, map_add (f := _), ha, hc, add_zero]
    · intro a c _ hc m
      rw [smul_eq_mul, mul_comm, mul_smul, hc]
  let φ : MM →ₗ[BB] BB ⊗[R] X :=
    { toFun := fun m => rT (q m)
      map_add' := fun a c => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun b m => by
        obtain ⟨s, hs⟩ := fib_dense y f S BB hC b
        have e : b • m = s • m + (b - algebraMap S BB s) • m := by
          rw [← algebraMap_smul BB s m, ← add_smul, add_sub_cancel]
        show rT (q (b • m)) = b • rT (q m)
        rw [e, map_add (f := _), map_smul, hL _ hs m, add_zero, hrtS]
        conv_rhs => rw [show b = algebraMap S BB s + (b - algebraMap S BB s) by ring, add_smul, fib_tmul_zero y BB X hX _ hs, add_zero] }
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨u, hu⟩ := hbij.2 t
    obtain ⟨m, hm⟩ := hq u
    refine ⟨m, ?_⟩
    show rT (q m) = t
    rw [hm, hu]
  have hK : LinearMap.ker φ = (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM) := by
    apply le_antisymm
    · intro m hm
      have h0 : q m = 0 := hbij.1 ((LinearMap.mem_ker.mp hm).trans (map_zero rT).symm)
      rw [← LinearMap.mem_ker, hker] at h0
      have hle : ((Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ : Submodule S MM) ≤ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM).restrictScalars S := by
        rw [Submodule.smul_le]
        intro s hs n _
        rw [Submodule.restrictScalars_mem, ← algebraMap_smul BB s n]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [hJ, IsScalarTower.algebraMap_eq R S BB, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hs
      exact hle h0
    · rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker]
      show rT (q (i • m)) = 0
      rw [hJ] at hi
      rw [hL i hi m, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hK.symm).trans (φ.quotKerEquivOfSurjective hφ)⟩
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem loc_of_pair {R X Y Z : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] [AddCommGroup Z] [Module R Z] (f : R) (h : X →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) h]
    (Φ : X →ₗ[R] Z) (Ψ : Z →ₗ[R] X) (h1 : ∀ z, Φ (Ψ z) = f • z) (h2 : ∀ z, Ψ (Φ z) = f • z) :
    IsLocalizedModule (Submonoid.powers f) (h ∘ₗ Ψ) := by
  have hf : f ∈ Submonoid.powers f := Submonoid.mem_powers f
  refine ⟨fun c => IsLocalizedModule.map_units h c, fun y => ?_, fun {z₁ z₂} hz => ?_⟩
  · obtain ⟨⟨x, m⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers f) h y
    refine ⟨⟨Φ x, ⟨f, hf⟩ * m⟩, ?_⟩
    simp only [LinearMap.comp_apply, h2, LinearMap.map_smul]
    rw [← hm, mul_smul]
    rfl
  · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := h) hz
    refine ⟨c * ⟨f, hf⟩, ?_⟩
    have hc' := congrArg Φ hc
    simp only [Submonoid.smul_def, LinearMap.map_smul, h1] at hc'
    simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact hc'

theorem UpperTheory.V.Pa.Core.pmodEx :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [IsLocalRing R] [IsNoetherianRing R] (U : Ultrafilter ℕ) (f : R) (ii : Ideal R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ k j, ∀ᶠ N in (U : Filter ℕ), ∃ (r : ℕ) (e : (M N ⧸ ((kjIdeal Λ σ k j).map s • ⊤ : Submodule R (M N))) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ k j)), ∀ a m, e (s a • m) = a • e m) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∃ (e : ℕ) (Gs : Set R), Ideal.span Gs = ii ∧ ∀ r ∈ Gs, ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ a : R, (f * r) ^ e - a ∈ maximalIdeal R ^ j ∧ ∀ m : M N, a • m = 0) → Nonempty (PMod (fun a => s (MvPowerSeries.X a)) f ii X) := by
  intro Λ R σ _ _ _ _ s _ _ _ _ _ U f ii M _ _ X _ _ _ _ hU hΛ hX hk hpair hnil
  classical
  let y : σ → R := fun a => s (MvPowerSeries.X a)
  let m : Ideal R := Ideal.map (s.comp MvPowerSeries.C) (maximalIdeal Λ)
  have hq : ∀ a j, ∀ᶠ N in (U : Filter ℕ), QRegAt (M N) y (m ^ j) a := by
    intro a j
    filter_upwards [hk (a + 1) j] with N hN
    obtain ⟨r, e, he⟩ := hN
    exact quotientRegularAt_of_quotient_free_over_powerSeries Λ R σ s (M N) a j r e he
  have hXR : Module.Finite R X := by
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule Λ X).FG)
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Submodule.span Λ (T : Set X) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul a z _ hz => rw [hΛ]; exact Submodule.smul_mem _ _ hz
  obtain ⟨Φ, Ψ, h1, h2⟩ := exists_ultraLimit_pair_of_eventual_quotient_maps Λ R σ s U f M X hU hΛ hX hpair
  let S := Localization.Away f
  let g := (TensorProduct.mk R S X 1) ∘ₗ Ψ
  haveI : IsLocalizedModule (Submonoid.powers f) g :=
    loc_of_pair f (TensorProduct.mk R S X 1) Φ Ψ h1 h2
  obtain ⟨MM, i1, i2, i3, i4, q, hfin, hsurj, hker, hqr, hann⟩ :=
    exists_patched_module R σ (U : Filter ℕ) hU y m f M S _ rfl hq (S ⊗[R] X) g inferInstance
  let BB := AdicCompletion (Ideal.map (algebraMap R S) (Ideal.span (Set.range y))) S
  have hy : ∀ a (x : X), y a • x = 0 := hX
  obtain ⟨fibE⟩ := fibEquiv R σ y f S BB X MM q (yCpl R σ y f) hy hsurj hker
  have hqr' : GlobalTheory.IsQuasiRegularSeq MM fun a => algebraMap R BB (y a) := by
    rw [isQuasiRegularSeq_iff_qRegAt] at hqr ⊢
    intro a
    have := ((qRegAt_map S BB σ (fun b => algebraMap R S (y b)) ⊥ a).1 MM).1 (hqr a)
    simpa [Ideal.map_bot, ← IsScalarTower.algebraMap_apply] using this
  have hnil' : ii ≤ Ideal.comap (algebraMap R BB) (Module.annihilator BB MM).radical := by
    obtain ⟨e, Gs, hGs, hG⟩ := hnil
    rw [← hGs, Ideal.span_le]
    intro r hr
    have key : ∀ x : MM, algebraMap R S ((f * r) ^ e) • x = 0 := by
      apply hann
      intro k
      refine ⟨k, fun j => ?_⟩
      obtain ⟨c, hc⟩ := finite_quotient_of_ultrafilter_limit_module Λ R σ s U f M X hΛ hX hpair k j
      filter_upwards [hc, hG r hr c] with N hN hN'
      obtain ⟨a, ha, ha0⟩ := hN'
      intro x
      have hmem := hN _ ha x
      have heq : (f ^ k * (f * r) ^ e) • x = (f ^ k * ((f * r) ^ e - a)) • x := by
        rw [mul_sub, sub_smul, mul_smul (f ^ k) a, ha0, smul_zero, sub_zero]
      rw [heq]
      exact hmem
    rw [SetLike.mem_coe, Ideal.mem_comap]
    refine ⟨e, ?_⟩
    rw [Module.mem_annihilator]
    intro x
    have hu : IsUnit ((algebraMap R S f) ^ e) := (IsLocalization.Away.algebraMap_isUnit f).pow e
    have hx : (algebraMap R BB r) ^ e • x = ((algebraMap R S r) ^ e) • x := by
      rw [IsScalarTower.algebraMap_apply R S BB, ← map_pow, algebraMap_smul]
    rw [hx, ← hu.smul_eq_zero, smul_smul, ← mul_pow, ← map_mul, ← map_pow]
    exact key x
  exact ⟨⟨BB, yCpl R σ y f, MM, hfin, hqr', fibE, hnil'⟩⟩
