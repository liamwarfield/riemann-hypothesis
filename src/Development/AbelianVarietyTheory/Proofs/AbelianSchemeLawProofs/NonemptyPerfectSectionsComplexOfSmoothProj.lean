module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyZeroEquivSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNoetherianSubringHomogeneousMatrixFlatChar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteQuotSMulTopXSubOneOfChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingCompOfSaturating
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGradedPresentationSaturating
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowSmulEqAddSubOneSmul
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add (f := _), map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyBaseChangeGrCubeIso
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeAwayOfIntertwine
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

section

variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]

theorem exists_awayFrac_common {f : A₀} (z w : LocalizedModule.Away f N₀) :
    ∃ k m m', awayFrac N₀ f k m = z ∧ awayFrac N₀ f k m' = w := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m', rfl⟩ := exists_awayFrac w
  exact ⟨k + j, f ^ j • m, f ^ k • m', awayFrac_add_pow_smul _ _ _ _,
    by rw [add_comm, awayFrac_add_pow_smul]⟩


omit [Algebra R A] [IsScalarTower R₀ R A] [Module R N] [IsScalarTower R A N]
  [IsScalarTower R₀ R N] in
theorem exists_away_map_of_intertwine (ψ : N₀ →ₗ[R₀] N) (x₀ : A₀) (x : A)
    (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y) :
    ∃ θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N,
      ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y) := by
  choose d n hdn using fun z : LocalizedModule.Away x₀ N₀ => exists_awayFrac z
  have key (k : ℕ) (y : N₀) :
      awayFrac N x (d (awayFrac N₀ x₀ k y)) (ψ (n (awayFrac N₀ x₀ k y))) =
        awayFrac N x k (ψ y) := by
    obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (hdn (awayFrac N₀ x₀ k y))
    exact awayFrac_eq_iff.2 ⟨l, by rw [← h, ← h, hl]⟩
  refine ⟨⟨⟨fun z => awayFrac N x (d z) (ψ (n z)), fun z w => ?_⟩, fun r z => ?_⟩, key⟩
  · obtain ⟨k, m, m', rfl, rfl⟩ := exists_awayFrac_common z w
    rw [← map_add (f := _), key, key, key, map_add (f := _), map_add (f := _)]
  · obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    simp only [RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower, key, key, map_smul, LinearMap.map_smul_of_tower]

theorem isBaseChange_away_of_intertwine (ψ : N₀ →ₗ[R₀] N) (hψ : IsBaseChange R ψ) (x₀ : A₀)
    (x : A) (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y)
    (θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N)
    (hθ : ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y)) : IsBaseChange R θ := by
  let F (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] LocalizedModule.Away x₀ N₀ :=
    ((awayFrac N₀ x₀ k).restrictScalars R₀).baseChange R
  let P (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] N₀ :=
    ((LinearMap.lsmul A₀ N₀ (x₀ ^ k)).restrictScalars R₀).baseChange R
  have hFP (k l : ℕ) (t : R ⊗[R₀] N₀) : F (k + l) (P l t) = F k t := by
    induction t with
    | tmul r y => exact congrArg (r ⊗ₜ[R₀] ·) (awayFrac_add_pow_smul x₀ k l y)
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hP (l : ℕ) (t : R ⊗[R₀] N₀) : hψ.equiv (P l t) = x ^ l • hψ.equiv t := by
    induction t with
    | tmul r y => simp [P, IsBaseChange.equiv_tmul, h, smul_comm r]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, smul_add]
  have hF (k : ℕ) (t : R ⊗[R₀] N₀) :
      θ.liftBaseChange R (F k t) = awayFrac N x k (hψ.equiv t) := by
    induction t with
    | tmul r y => simp [F, IsBaseChange.equiv_tmul, hθ, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hsurj (z : R ⊗[R₀] LocalizedModule.Away x₀ N₀) : ∃ k t, F k t = z := by
    induction z with
    | tmul r z =>
      obtain ⟨k, y, rfl⟩ := exists_awayFrac z
      exact ⟨k, r ⊗ₜ y, by simp [F]⟩
    | add a b ha hb =>
      obtain ⟨k, t, rfl⟩ := ha
      obtain ⟨j, u, rfl⟩ := hb
      exact ⟨k + j, P j t + P k u, by rw [map_add (f := _), hFP, add_comm k j, hFP]⟩
  suffices hb : Function.Bijective (θ.liftBaseChange R) from
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hb) fun z => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, t, rfl⟩ := hsurj z
    rw [hF, awayFrac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    rw [← hP, map_eq_zero_iff _ hψ.equiv.injective] at hl
    rw [← hFP k l, hl, map_zero]
  · intro z
    obtain ⟨k, y, rfl⟩ := exists_awayFrac z
    obtain ⟨t, rfl⟩ := hψ.equiv.surjective y
    exact ⟨F k t, hF k t⟩

end

theorem exists_isBaseChange_away_xProd :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (s : Finset ι), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → ∃ θ : LocalizedModule.Away (xProd R₀ s) N₀ →ₗ[R₀] LocalizedModule.Away (xProd R s) N, IsBaseChange R θ ∧ ∀ (k : ℕ) y, θ (awayFrac N₀ (xProd R₀ s) k y) = awayFrac N (xProd R s) k (ψ y) := by
  intro ι R₀ R _ _ _ N₀ N _ _ _ _ _ _ _ _ _ _ _ ψ s hψ hX
  classical
  have h₁ (y : N₀) : ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [xProd] at ih ⊢; simp only [Finset.prod_insert hi, mul_smul, hX, ih]
  have h (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h₁, ih]
  obtain ⟨θ, hθ⟩ := exists_away_map_of_intertwine ψ _ _ h
  exact ⟨θ, isBaseChange_away_of_intertwine ψ hψ _ _ h θ hθ, hθ⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeGradedPiece
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isBaseChange_gradedPiece : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N] (𝒩₀ : ℤ → Submodule R₀ N₀) [Decomposition 𝒩₀] (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] (ψ : N₀ →ₗ[R₀] N) (n : ℤ) (θ : 𝒩₀ n →ₗ[R₀] 𝒩 n), IsBaseChange R ψ → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → (∀ y, (θ y : N) = ψ y) → IsBaseChange R θ := by
  intro R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ
  let p₀ : N₀ →ₗ[R₀] 𝒩₀ n :=
    DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap
  let p : N →ₗ[R] 𝒩 n :=
    DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap
  have hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n := fun _ => rfl
  have hp : ∀ y, p y = decompose 𝒩 y n := fun _ => rfl
  have hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y := fun y => by
    apply Subtype.ext
    rw [hp₀]
    exact decompose_of_mem_same 𝒩₀ y.2
  have hpi : ∀ y : 𝒩 n, p (y : N) = y := fun y => by
    apply Subtype.ext
    rw [hp]
    exact decompose_of_mem_same 𝒩 y.2
  have hcomm : ∀ y, θ (p₀ y) = p (ψ y) := by
    intro y
    induction y using Decomposition.inductionOn 𝒩₀ with
    | zero => simp
    | @homogeneous j y =>
      by_cases hj : j = n
      · subst hj
        rw [hp₀i, ← hθ, hpi]
      · have h1 : p₀ (y : N₀) = 0 := by
          apply Subtype.ext
          rw [hp₀]
          exact decompose_of_mem_ne 𝒩₀ y.2 hj
        have h2 : p (ψ y) = 0 := by
          apply Subtype.ext
          rw [hp]
          exact decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj
        rw [h1, h2, map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n := LinearMap.liftBaseChange R θ
  have hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hcomm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hθ]
    | add a b ha hb => simp only [map_add (f := _), Submodule.coe_add, ha, hb]
  have hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [hp₀i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a)
          = h.equiv ((𝒩₀ n).subtype.baseChange R b) := by
        rw [← hL2, ← hL2, hab]
      rw [← hret a, h.equiv.injective h1, hret]
    · intro z
      refine ⟨p₀.baseChange R (h.equiv.symm z), ?_⟩
      rw [hL1, LinearEquiv.apply_symm_apply, hpi]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_
  simp [L]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem map_xProd_pow_smul_of_X {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
  classical
  have h1 : ∀ y, ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [xProd, xProd, Finset.prod_insert ha, Finset.prod_insert ha, mul_smul, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h1, ih]

theorem nonempty_baseChange_grCube_iso : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by
  intro ι _ _ R₀ R _ _ _ N₀ _ _ _ _ 𝒩₀ _ _ N _ _ _ _ 𝒩 _ _ _ _ _ ψ n hψ hX hgr
  choose θ hθ hθe using fun s : Finset ι => GlobalTheory.exists_isBaseChange_away_xProd ι R₀ R N₀ N ψ s hψ hX
  have hg : ∀ s j, ∀ y ∈ homLoc 𝒩₀ s j, θ s y ∈ homLoc 𝒩 s j := by
    rintro s j _ ⟨k, m, hm, rfl⟩
    rw [hθe]
    exact awayFrac_mem_homLoc (hgr _ _ hm) rfl
  let η : ∀ s, homLoc 𝒩₀ s n →ₗ[R₀] homLoc 𝒩 s n := fun s =>
    { toFun := fun y => ⟨θ s y, hg s n _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (θ s) a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul (θ s) r a.1) }
  have hη : ∀ s, IsBaseChange R (η s) := fun s =>
    GlobalTheory.isBaseChange_gradedPiece R₀ R _ _ (homLoc 𝒩₀ s) (homLoc 𝒩 s) (θ s) n (η s) (hθ s) (hg s) fun _ => rfl
  have hres : ∀ {s t : Finset ι} (h : s ⊆ t) (z : homLoc 𝒩₀ s n),
      η t (homLocRes 𝒩₀ h n z) = homLocRes 𝒩 h n (η s z) := by
    rintro s t h ⟨_, k, m, hm, rfl⟩
    apply Subtype.ext
    change θ t (locRes X N₀ h (awayFrac N₀ _ k m)) = locRes X N h (θ s (awayFrac N₀ _ k m))
    rw [hθe, locRes_awayFrac X h (Finset.prod_sdiff h).symm,
      locRes_awayFrac X h (Finset.prod_sdiff h).symm, hθe]
    exact congrArg _ (map_xProd_pow_smul_of_X ψ hX (t \ s) k m)
  have key : ∀ {s t : Finset ι} (h : s ⊆ t) (x : R ⊗[R₀] homLoc 𝒩₀ s n),
      (hη t).equiv ((homLocRes 𝒩₀ h n).baseChange R x) = homLocRes 𝒩 h n ((hη s).equiv x) := by
    intro s t h x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r z =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        hres]
  exact ⟨Cube.isoMk (fun s => (hη s).equiv) fun h x => key h x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyHomLocSingletonEquivQuotSMulTop
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_homLoc_singleton_equiv_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatHomLocOfFlatHomLocSingleton
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem flat_loc_over_algebra {A S M N : Type} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    (h : Module.Flat A M) : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this

private theorem flat_iff_forall_piece {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ] :
    Module.Flat R M ↔ ∀ n, Module.Flat R (ℳ n) :=
  (Module.Flat.equiv_iff (decomposeLinearEquiv ℳ)).trans Module.Flat.directSum_iff

theorem flat_homLoc_of_flat_homLoc_singleton :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
      [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
      (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (s : Finset ι)
      (n : ℤ), i ∈ s → Module.Flat R (homLoc ℳ {i} 0) → Module.Flat R (homLoc ℳ s n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i s n hi h0
  have step (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) ↔ Module.Flat R (homLoc ℳ {i} (t + 1)) :=
    Module.Flat.equiv_iff (LinearEquiv.ofBijective _
      (homLocSMul_X_bijective ℳ (Finset.mem_singleton_self i) t))
  have hall (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) := by
    induction t using Int.induction_on with
    | zero => exact h0
    | succ k ih => exact (step _).1 ih
    | pred k ih => exact (step _).2 (by rwa [sub_add_cancel])
  have h1 := (flat_iff_forall_piece (homLoc ℳ {i})).2 hall
  have hsub : ({i} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hi
  have hc : xProd R s = xProd R (s \ {i}) * xProd R {i} := (Finset.prod_sdiff hsub).symm
  have h2 : IsLocalizedModule.Away (xProd R (s \ {i}) * xProd R {i})
      (locRes X M hsub ∘ₗ LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) := by
    rw [locRes_comp_mkLinearMap, ← hc]
    exact localizedModuleIsLocalizedModule _
  have h3 : IsLocalizedModule.Away (xProd R (s \ {i})) (locRes X M hsub) :=
    isLocalizedModule_away_of_comp (b := xProd R {i})
      (LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) _
  have h4 := flat_loc_over_algebra (A := R) (.powers (xProd R (s \ {i}))) (locRes X M hsub) h1
  exact (flat_iff_forall_piece (homLoc ℳ s)).1 h4 n

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeCokerMatrixMvPolynomial
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_isBaseChange_coker {R₀ R A₀ A M₁ M₂ N₁ N₂ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Ring A₀] [Ring A] [Algebra R₀ A₀] [Algebra R A] [SMul R₀ A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₁] [Module R₀ M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower R₀ A₀ M₁] [IsScalarTower R₀ A₀ M₂]
    [Module R₀ N₁] [Module R₀ N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower R₀ R N₁] [IsScalarTower R₀ R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower R₀ A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (h₁ : M₁ →ₗ[R₀] N₁) (h₂ : M₂ →ₗ[R₀] N₂)
    (b₁ : IsBaseChange R h₁) (b₂ : IsBaseChange R h₂) (hcomm : ∀ x, h₂ (f₀ x) = f (h₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (h₂ y) := by
  let q₀ : M₂ →ₗ[R₀] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars R₀
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have hex₀ : Function.Exact (f₀.restrictScalars R₀) q₀ := LinearMap.exact_map_mkQ_range f₀
  have hex : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars R₀).comp h₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hex₀ y).1 hy
    exact (hex _).2 ⟨h₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ : ∀ y, ψ (q₀ y) = q (h₂ y) := by
    intro y
    have : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars R₀) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) h₁ h₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ hex₀ hq₀ hex hq, hψ⟩

theorem isBaseChange_coker_matrix_mvPolynomial :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsHomogeneousRangeMulVecLin
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  intro n v hv
  refine mem_grPi.2 fun l => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, grShift_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := grSMul_mem (polyGrading ι R) (h l j) (mem_grPi.1 hv j)
  rwa [smul_eq_mul, show n + -e j + (e j - d l) = n + -d l by ring] at this

theorem isHomogeneous_range_mulVecLin :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct

noncomputable section

namespace GlobalTheory

theorem dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩

theorem exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ :=
    exists_graded_presentation_saturating ι R G 𝒢 fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, hfp, -, h⟩ := H i
      exact (finite_quotSMulTop_X_sub_one_of_chart ι R G 𝒢 i B iB iA π P iP iM ε h).2
        inferInstance hfp
  let := grQuotDecomposition (grFree ι R d) (isHomogeneous_range_mulVecLin ι R a b d e Φ hΦ)
  obtain ⟨R₀, Φ₀, hN, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_subring_homogeneous_matrix_flat_charts ι R a b d e Φ hΦ fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, -, hp, hπs, hπ, hε, hk⟩ := H i
      obtain ⟨k₁, k₂⟩ := dehomogenising_comp_of_saturating
        (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 hψ i (hsat i).1 (hsat i).2
        (π : MvPolynomial ι R →+* B) ε hπ hε hk
      refine ⟨B, iB, iA, π, P, iP, iM, (ε.comp ψ).comp (LinearMap.range Φ.mulVecLin).mkQ, hs, hp,
        hπs, hπ, k₁.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
      rw [LinearMap.comp_apply, k₂]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective _ w
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, w', by rw [← Matrix.mulVecLin_apply, hv, sub_add_cancel]⟩
      · rintro ⟨v, w', rfl⟩
        refine ⟨Submodule.mkQ _ w', ?_⟩
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨v, by rw [Matrix.mulVecLin_apply, add_sub_cancel_right]⟩
  let := grQuotDecomposition (grFree ι R₀ d)
    (isHomogeneous_range_mulVecLin ι R₀ a b d e Φ₀ hΦ₀)
  obtain ⟨ψ₀, hbc, hψ₀⟩ := isBaseChange_coker_matrix_mvPolynomial ι R₀ R a b Φ₀ Φ hmap
  obtain ⟨iso⟩ := nonempty_baseChange_grCube_iso ι R₀ R _
    (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) _
    (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) ψ₀ 0 hbc
    (fun i y => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, hψ₀, hψ₀, ← Submodule.Quotient.mk_smul]
      congr 1
      ext1 l
      simp)
    (by
      rintro j _ ⟨y, hy, rfl⟩
      refine mem_grQuot.2 ⟨_, mem_grPi.2 fun l => ?_, (hψ₀ y).symm⟩
      have := mem_polyGrading_iff.1 (mem_grPi.1 hy l)
      refine mem_polyGrading_iff.2 fun c hc => this c fun h0 => hc ?_
      rw [MvPolynomial.coeff_map, h0, map_zero])
  refine ⟨R₀, hN, grCube ι (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) 0,
    iso.hom ≫ grCubeMap hψ 0, ?_, ?_, ?_⟩
  · rintro I ⟨i, hi⟩
    obtain ⟨f⟩ := nonempty_homLoc_singleton_equiv_quotSMulTop ι R₀ _
      (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) i
    have := hflat i
    exact flat_homLoc_of_flat_homLoc_singleton ι R₀ _ _ i I 0 hi (Module.Flat.of_linearEquiv f)
  · exact finite_grCech_homology ι R₀ _ _ inferInstance 0
  · rintro I ⟨i, hi⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (homLocMap_bijective_of_X hψ hi (hsat i).1 (hsat i).2 0).comp
      (ConcreteCategory.bijective_of_isIso (iso.hom.app I))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CstSmoothAndFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem cst_smooth_and_flat : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Opens), IsAffineOpen V → (Smooth f → (cst f V).Smooth) ∧ (Flat f → (cst f V).Flat) := by
  intro R _ Y f V hV
  have e : cst f V = (f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl
  have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [e]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact (RingHom.Smooth.of_bijective hb).comp (f.smooth_appLE (isAffineOpen_top _) hV le_top)
  · exact (RingHom.Flat.of_bijective hb).comp (f.flat_appLE (isAffineOpen_top _) hV le_top)

end GlobalTheory.Cohom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexOfNoetherianModel
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem Cube.nonempty_extendScalars_iso_baseChange {ι : Type} {R₀ R : Type} [CommRing R₀]
    [CommRing R] [inst : Algebra R₀ R] (C : Cube.{0} ι R₀) :
    Nonempty (C ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R) ≅ Cube.baseChange R C) := by
  obtain ⟨f, rfl⟩ : ∃ f : R₀ →+* R, inst = f.toAlgebra := ⟨_, toAlgebra_algebraMap.symm⟩
  exact ⟨NatIso.ofComponents (fun s => Iso.refl _) fun h => by
    rw [Iso.refl_hom, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩

theorem finite_projective_extendScalars_obj {R₀ R : Type} [CommRing R₀] [CommRing R]
    (f : R₀ →+* R) (M : ModuleCat.{0} R₀) [Module.Finite R₀ M] [Module.Projective R₀ M] :
    Module.Finite R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) ∧
      Module.Projective R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) := by
  letI := f.toAlgebra
  exact ⟨inferInstanceAs (Module.Finite R (R ⊗[R₀] M)),
    inferInstanceAs (Module.Projective R (R ⊗[R₀] M))⟩

theorem quasiIso_extendScalars_extendScalars {R₀ R R' : Type} [CommRing R₀] [CommRing R]
    [CommRing R'] (f : R₀ →+* R) (g : R →+* R') {K L : CochainComplex (ModuleCat.{0} R₀) ℕ}
    (φ : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (g.comp f)).mapHomologicalComplex _).map φ)) :
    QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map
      (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map φ)) := by
  let e := NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{0} f g)
    (ComplexShape.up ℕ)
  have h' : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} f ⋙
      ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map φ) := by
    rw [← NatIso.naturality_1 e φ]
    infer_instance
  exact h'

theorem exists_finite_projective_complex_of_noetherian_model :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] (C₀ : Cube.{0} ι R₀) (A : Cube.{0} ι R) (θ : Cube.baseChange R C₀ ⟶ A), (∀ s : Finset ι, s.Nonempty → Module.Flat R₀ (C₀.obj s)) → (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) → (∀ s : Finset ι, s.Nonempty → Function.Bijective (θ.app s).hom) → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechComplex A), (∀ p, Fintype.card ι ≤ p + 1 → IsZero (K.X (p + 1))) ∧ (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro ι _ _ R₀ R _ _ _ _ C₀ A θ hflat hfin hθ
  obtain ⟨K₀, φ₀, h0, h1, -, h2, -, -, h3⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} (cechComplex C₀) (Fintype.card ι - 1)
      (fun p hp => isZero_cechComplex_X C₀ (by omega))
      (fun p => Cube.flat_term C₀ (p + 1) fun s hs => hflat s (Finset.card_pos.1 (by omega))) hfin
  obtain ⟨e⟩ := Cube.nonempty_extendScalars_iso_baseChange (R := R) C₀
  let F := (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let ψ : F.obj (cechComplex C₀) ≅ cechComplex A :=
    cechExtendScalarsIso (algebraMap R₀ R) C₀ ≪≫ (cechFunctor ι R).mapIso e ≪≫
      @asIso _ _ _ _ (cechComplexMap θ) (isIso_cechComplexMap θ hθ)
  refine ⟨F.obj K₀, F.map φ₀ ≫ ψ.hom, fun p hp => ?_, fun p => ?_, fun R' _ _ => ?_⟩
  · exact (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).map_isZero (h0 _ (by omega))
  · have := h1 p
    have := h2 p
    exact finite_projective_extendScalars_obj (algebraMap R₀ R) (K₀.X p)
  · letI := ((algebraMap R R').comp (algebraMap R₀ R)).toAlgebra
    have := quasiIso_extendScalars_extendScalars (algebraMap R₀ R) (algebraMap R R') φ₀ (h3 R')
    rw [Functor.map_comp]
    infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundle
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem exists_finite_projective_complex_cechLB : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → Smooth f → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M (fun i => nonzeroLocus (s i))), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro R _ Y f H m s M hH hM hs hf
  have hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V)
      fun i t => SecOnR.mulSec f M t (s i) V := fun V i j t x =>
    SecOn.mulSec_comm (s i) (s j) x
  obtain ⟨R₀, hR₀, C₀, θ, hflat, hfin, hθ⟩ :=
    exists_noetherian_model_grCube (Fin (m + 1)) R (GrSum (hx ⊤)) (GrSum.grading (hx ⊤)) fun i => by
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      obtain ⟨hri, ε, hε, hker, -⟩ := GlobalTheory.AbLaw.exists_dehom_chart R Y f H m s M hH hM hs hx i r hr
      letI := cstAlgebra f (nonzeroLocus (s i))
      obtain ⟨hfp, hproj⟩ := secOn_finitePresentation_projective Y (tw M H 0) (nonzeroLocus (s i))
        (isLB_tw hM hH 0) haff
      exact ⟨Γ(Y, nonzeroLocus (s i)), inferInstance, cstAlgebra f _, MvPolynomial.aeval r,
        SecOn (tw M H 0) (nonzeroLocus (s i)), inferInstance, inferInstance, ε,
        (cst_smooth_and_flat R Y f _ haff).1 hf, hfp, hproj, hsurj,
        (MvPolynomial.aeval_X r i).trans hri, hε, hker⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_grCube_twistedSections_hom_secCube_bijective R Y f H m s M hH hM hs hx 0
  let e := secCubeIso f (fun i => nonzeroLocus (s i)) (SecOn.twZeroEquiv hM hH)
    (SecOn.twZeroEquiv_restrict hM hH)
  obtain ⟨K, φ, -, hK, hφ⟩ := exists_finite_projective_complex_of_noetherian_model (Fin (m + 1)) R₀ R
    C₀ (secCube f M fun i => nonzeroLocus (s i)) (θ ≫ γ ≫ e.inv) hflat hfin fun I hI => by
      rw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp,
        LinearMap.coe_comp, LinearMap.coe_comp]
      exact ((ConcreteCategory.bijective_of_isIso (e.inv.app I)).comp (hγ I)).comp (hθ I hI)
  exact ⟨K, φ, hK, hφ⟩

end GlobalTheory.Cohom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveCechComplexLineBundleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → Smooth f → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M (fun i => nonzeroLocus (s i))), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  first | exact @GlobalTheory.Cohom.exists_finite_projective_complex_cechLB | exact GlobalTheory.Cohom.exists_finite_projective_complex_cechLB | (intros; apply GlobalTheory.Cohom.exists_finite_projective_complex_cechLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem nonempty_perf_of_smooth_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  intro R _ X f hf hp M hM
  obtain ⟨H, hH, m, s, hs⟩ := hp
  obtain ⟨K, φ, hK⟩ := GlobalTheory.T.exists_finite_projective_cechComplex_lineBundle R X f H m s M hH hM hs hf
  exact GlobalTheory.T.threeTermComplex_of_projective_cech_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1
    (GlobalTheory.T.veryAmple_compact_quasiSeparated_affine_charts R X f H m s hH hs).2.2 hK

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy | exact GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy | (intros; apply GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy <;> assumption)
end
