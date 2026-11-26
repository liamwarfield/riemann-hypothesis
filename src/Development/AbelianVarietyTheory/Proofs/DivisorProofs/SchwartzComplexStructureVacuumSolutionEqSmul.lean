module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.VacCore

theorem ray_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : V → ℂ) (hk : Differentiable ℝ k) (w : V) (ℓ : V →ₗ[ℝ] ℂ)
    (h : ∀ z, fderiv ℝ k z w = ℓ z * k z) : k w = k 0 * Complex.exp (ℓ w / 2) := by
  set c := ℓ w
  let E : ℝ → ℂ := fun s => Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c)
  have hE : ∀ s : ℝ, HasDerivAt E (Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c) * (((-(2 * s) / 2 : ℝ) : ℂ) * c)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (-(s ^ 2) / 2 : ℝ)) (-(2 * s) / 2) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const 2
      simpa using this
    exact ((h1.ofReal_comp).mul_const c).cexp
  have hK : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w)) (fderiv ℝ k (s • w) w) s := by
    intro s
    have := (hk (s • w)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const w)
    rw [one_smul] at this
    exact this
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w) * E s) 0 s := by
    intro s
    have := (hK s).mul (hE s)
    refine this.congr_deriv ?_
    rw [h, map_smul]
    simp only [Complex.real_smul, E]
    push_cast
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => k (s • w) * E s)
    (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  simp only [E, one_smul, zero_smul] at hc
  have : Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; simp
  calc k w = k w * (Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2)) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hc]; simp

theorem conj_mul_eq_zero_of_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f g : SchwartzMap V ℂ) (y₀ : V) (hy : y₀ ≠ 0)
    (h : ∀ z, fderiv ℝ f z y₀ * (starRingEnd ℂ) (g z) + f z * (starRingEnd ℂ) (fderiv ℝ g z y₀) = 0) :
    ∀ z, f z * (starRingEnd ℂ) (g z) = 0 := by
  intro z
  let φ : ℝ → ℂ := fun t => f (z + t • y₀) * (starRingEnd ℂ) (g (z + t • y₀))
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • y₀) y₀ t := by
    intro t
    have := ((hasDerivAt_id t).smul_const y₀).const_add z
    simpa using this
  have hφ : ∀ t, HasDerivAt φ 0 t := by
    intro t
    have hf := (f.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg := (g.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg' := hg.star
    have := hf.mul hg'
    refine this.congr_deriv ?_
    have := h (z + t • y₀)
    simpa [Complex.star_def] using this
  have hc : ∀ t, φ t = φ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) t 0
  have hlin : Filter.Tendsto (fun t : ℝ => z + t • y₀) (Filter.cocompact ℝ) (Filter.cocompact V) := by
    apply Filter.tendsto_cocompact_cocompact_of_norm
    intro ε
    have hy' : 0 < ‖y₀‖ := norm_pos_iff.mpr hy
    refine ⟨(ε + ‖z‖) / ‖y₀‖, fun t ht => ?_⟩
    have h1 : ‖t • y₀‖ ≤ ‖z + t • y₀‖ + ‖z‖ := by
      calc ‖t • y₀‖ = ‖(z + t • y₀) - z‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul] at h1
    rw [div_lt_iff₀ hy'] at ht
    linarith
  have hf0 : Filter.Tendsto (fun t : ℝ => f (z + t • y₀)) (Filter.cocompact ℝ) (nhds 0) :=
    (f.tendsto_cocompact).comp hlin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C := ⟨_, fun x => (g.toBoundedContinuousFunction).norm_coe_le_norm x⟩
  have hφ0 : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hf0 ⊢
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have := hf0.mul_const C
    rw [zero_mul] at this
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) this
    simp only [φ, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hconst : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds (φ 0)) := by
    have : φ = fun _ => φ 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hφ0
  simpa [φ] using this

noncomputable def lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b : V) : V →ₗ[ℝ] ℂ where
  toFun z := 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ)
  map_add' x y := by simp only [map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]; ring
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

theorem lin_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b z : V) :
    lin B a b z = 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ) := rfl

theorem schwartz_vacuum_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  intro V _ _ _ B hB J e e' hJ he hJe he1 he2 f g hg0 hg hf

  have hinj : ∀ y, (J y).1 = 0 → y.1 = 0 → y = 0 := by
    intro y hJy hy1
    have key : ∀ x, g x ≠ 0 → B x y.2 = 0 := by
      intro x hx
      have h := hg y x
      simp only [hJy, hy1, map_zero] at h
      have h2 : g x * (2 * Real.pi * (B x y.2 : ℂ) + 2 * Real.pi * Complex.I * (B x (J y).2 : ℂ)) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B x y.2 : ℂ) * g x) * Complex.I_sq
      have h3 := (mul_eq_zero.mp h2).resolve_left hx
      have h4 := congrArg Complex.re h3
      simpa [Real.pi_ne_zero] using h4
    have hy2 : y.2 = 0 := by
      apply hB
      by_contra hne
      push_neg at hne
      obtain ⟨x₀, hx₀⟩ := hne
      apply hg0
      ext x
      simp only [SchwartzMap.zero_apply]
      set t₀ : ℝ := -(B x y.2) / B x₀ y.2
      have hS : IsClosed {t : ℝ | g (x + t • x₀) = 0} :=
        isClosed_eq (g.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
          continuous_const
      have hsub : ({t₀}ᶜ : Set ℝ) ⊆ {t : ℝ | g (x + t • x₀) = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
        simp only [Set.mem_setOf_eq]
        by_contra hgt
        have := key _ hgt
        rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
        apply ht
        simp only [t₀]
        field_simp
        linarith
      have hcl := hS.closure_subset_iff.mpr hsub
      rw [(dense_compl_singleton t₀).closure_eq] at hcl
      have := hcl (Set.mem_univ 0)
      simpa using this
    exact Prod.ext hy1 hy2
  let T : (V × V) →ₗ[ℝ] (V × V) := (LinearMap.fst ℝ V V ∘ₗ J).prod (LinearMap.fst ℝ V V)
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hinj y (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTi

  choose yx hyx using fun x : V => hTs (x, 0)
  have hyx1 : ∀ x, (J (yx x)).1 = x := fun x => by simpa [T] using congrArg Prod.fst (hyx x)
  have hyx2 : ∀ x, (yx x).1 = 0 := fun x => by simpa [T] using congrArg Prod.snd (hyx x)
  have hray : ∀ k : SchwartzMap V ℂ, (∀ (y : V × V) (z : V), fderiv ℝ k z (J y).1 -
      2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * k z =
      Complex.I * (fderiv ℝ k z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * k z)) →
      ∀ x, k x = k 0 * Complex.exp (lin B (J (yx x)).2 (yx x).2 x / 2) := by
    intro k hk x
    apply ray_formula k k.differentiable x (lin B (J (yx x)).2 (yx x).2)
    intro z
    have h := hk (yx x) z
    rw [hyx1, hyx2, map_zero] at h
    rw [lin_apply]
    linear_combination h - (2 * Real.pi * (B z (yx x).2 : ℂ) * k z) * Complex.I_sq
  have hg_ray := hray g hg
  have hg00 : g 0 ≠ 0 := by
    intro h0; apply hg0; ext x; rw [hg_ray x, h0]; simp
  have hgne : ∀ x, g x ≠ 0 := fun x => by
    rw [hg_ray x]; exact mul_ne_zero hg00 (Complex.exp_ne_zero _)
  have he'2 : ∀ v, e' (e' v) = e' v := by
    intro v
    have := congrArg Prod.fst (he (v, 0))
    simp only [he1] at this
    simpa using this
  by_cases hz : ∀ v, e' v = 0
  · have he0 : ∀ y, e y = 0 := by
      intro y; apply Prod.ext
      · rw [he1, hz]; rfl
      · apply hB; intro x; rw [he2, hz, map_zero, LinearMap.zero_apply]
    have hf' : ∀ (y : V × V) (z : V), fderiv ℝ f z (J y).1 -
        2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * f z =
        Complex.I * (fderiv ℝ f z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * f z) := by
      intro y z; have := hf y z; rwa [he0, smul_zero, sub_zero] at this
    have hf_ray := hray f hf'
    refine ⟨f 0 / g 0, ?_⟩
    ext x
    rw [SchwartzMap.smul_apply, smul_eq_mul, hf_ray x, hg_ray x]
    field_simp
  · push_neg at hz
    obtain ⟨v, hv⟩ := hz
    set y₀ := e' v with hy₀def
    have hy₀ : e' y₀ = y₀ := he'2 v
    obtain ⟨u, hu⟩ := hTs (y₀, 0)
    have hu1 : (J u).1 = y₀ := by simpa [T] using congrArg Prod.fst hu
    have hu2 : u.1 = 0 := by simpa [T] using congrArg Prod.snd hu
    have heu : e u = u := by
      have : e u - u = 0 := hinj _
        (by rw [map_sub, Prod.fst_sub, hJe, he1, hu1, hy₀, sub_self])
        (by rw [Prod.fst_sub, he1, hu2, map_zero, sub_self])
      exact sub_eq_zero.mp this
    have hfu : ∀ z, fderiv ℝ f z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        - 2 * Real.pi * (B z u.2 : ℂ)) * f z := by
      intro z
      have h := hf u z
      rw [heu, two_smul, sub_add_cancel_left, map_neg, Prod.fst_neg, Prod.snd_neg, map_neg,
        map_neg, hu1, hu2, map_zero, Complex.ofReal_neg] at h
      linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B z u.2 : ℂ) * f z) * Complex.I_sq
    have hgu : ∀ z, fderiv ℝ g z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        + 2 * Real.pi * (B z u.2 : ℂ)) * g z := by
      intro z
      have h := hg u z
      rw [hu1, hu2, map_zero] at h
      linear_combination h - (2 * Real.pi * (B z u.2 : ℂ) * g z) * Complex.I_sq
    have hk := conj_mul_eq_zero_of_line f g y₀ hv (fun z => by
      rw [hfu z, hgu z]
      simp only [map_add (f := _), map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring)
    refine ⟨0, ?_⟩
    ext z
    rw [zero_smul, SchwartzMap.zero_apply]
    exact (mul_eq_zero.mp (hk z)).resolve_right ((map_ne_zero _).mpr (hgne z))

end GlobalTheory.VacCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmulStatement
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  first | exact @GlobalTheory.VacCore.schwartz_vacuum_eq_smul | exact GlobalTheory.VacCore.schwartz_vacuum_eq_smul | (intros; apply GlobalTheory.VacCore.schwartz_vacuum_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFstSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem spMap_fst_surjective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) := by
  intro q
  haveI : q.asIdeal.IsPrime := q.2
  refine ⟨⟨q.asIdeal.comap (TrivSqZeroExt.inlHom R M), Ideal.IsPrime.comap _⟩, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  show (TrivSqZeroExt.inlHom R M) ((TrivSqZeroExt.fstHom R R M) a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
  have hm : TrivSqZeroExt.inr a.snd ∈ q.asIdeal :=
    q.2.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact q.asIdeal.zero_mem)
  have e : TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inr a.snd = a := TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  constructor
  · intro h
    rw [← e]
    exact q.asIdeal.add_mem h hm
  · intro h
    show TrivSqZeroExt.inl a.fst ∈ q.asIdeal
    rw [eq_sub_of_add_eq e]
    exact q.asIdeal.sub_mem h hm

theorem exists_basicOpen_inl {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] {X : Scheme.{0}} (x : Sp R ⟶ X) (q : Sp (TrivSqZeroExt R M)) :
    ∃ (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (U : X.affineOpens), q ∈ (Sp (TrivSqZeroExt R M)).basicOpen s ∧
      spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 := by
  obtain ⟨q₀, rfl⟩ := spMap_fst_surjective R M q
  obtain ⟨U, hUa, hU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x q₀ ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show q₀ ∈ ((x ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) from hU) (x ⁻¹ᵁ U).2
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv (TrivSqZeroExt.inl r), ⟨U, hUa⟩, ?_, ?_⟩
  · rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact hr
  · intro w hw
    rw [Scheme.Hom.mem_preimage, AlgebraicGeometry.basicOpen_eq_of_affine] at hw
    exact hle hw

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
open ValuativeRel Matrix

namespace GlobalTheory

theorem rank_frame_exists :
    ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K),
        H * X * Q = 1 := by
  intro K _ A D _ _ _ _ X
  classical
  let V := LinearMap.range X.mulVecLin
  let b : Module.Basis (Fin X.rank) K V := Module.finBasis K V
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V) b.equivFun.toLinearMap
  have hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K) := fun i => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (b i).2
    exact ⟨v, hv⟩
  choose q hq using hpre
  refine ⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.one_mulVec]
  have hcol : (Matrix.of fun d i => q i d).col j = q j := by
    ext d; simp [Matrix.col]
  rw [hcol, hq j, LinearMap.toMatrix'_mulVec]
  have := congrArg (fun f => f (b j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe] at this
  rw [this]
  ext k
  rw [Module.Basis.equivFun_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalFormStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K), H * X * Q = 1 := by
  first | exact @GlobalTheory.rank_frame_exists | exact GlobalTheory.rank_frame_exists | (intros; apply GlobalTheory.rank_frame_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polEval_pderiv :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  intro V _ _ ι _ m d hm f₀ hc h0 i p
  have hX : ∀ (j : ι) (q : MvPolynomial ι ℂ),
      polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q) := by
    intro j q
    simp [polEval, Module.End.mul_apply]
  have h1 : polEval m hm f₀ 1 = f₀ := by simp [polEval]
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X q j hq =>
    have hv := LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at hv
    rw [mul_comm q, MvPolynomial.pderiv_mul, map_add (f := _), hX, hX, hq, hv]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
      simp [hij]

end GlobalTheory.CCRFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderivStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  first | exact @GlobalTheory.CCRFock.polEval_pderiv | exact GlobalTheory.CCRFock.polEval_pderiv | (intros; apply GlobalTheory.CCRFock.polEval_pderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFrameNormEqZero
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open MeasureTheory

namespace GlobalTheory.MaxPoint

theorem frameNorm_mulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (y : Fin N → ℂ) :
    frameNorm A (A.mulVec y) = Real.sqrt (∑ k, ‖y k‖ ^ 2) := by
  unfold frameNorm
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]

theorem frameNorm_nonneg' {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : 0 ≤ frameNorm A x :=
  Real.sqrt_nonneg _

theorem frameNorm_smul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (c • x) = ‖c‖ * frameNorm A x := by
  unfold frameNorm
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem eq_zero_of_frameNorm_eq_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {x : Fin N → ℂ}
    (h : frameNorm A x = 0) : x = 0 := by
  unfold frameNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  have hy : A⁻¹.mulVec x = 0 := by
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖A⁻¹.mulVec x i‖)).1 h k (Finset.mem_univ _)
    simpa using this
  calc x = A.mulVec (A⁻¹.mulVec x) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
    _ = 0 := by rw [hy, Matrix.mulVec_zero]

theorem eval_linSubst {B N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ)
    (x : Fin B × Fin N → ℂ) :
    eval x (linSubst A h) = eval (fun q => A.mulVec (fun k => x (q.1, k)) q.2) h := by
  unfold linSubst
  rw [eval_aeval_alt]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mulVec, dotProduct]

end GlobalTheory.MaxPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFinPart

theorem log_gaussAbs_support_finite {E : Type} [Field E] [NumberField E] {σ : Type}
    (g : MvPolynomial σ E) :
    (Function.support fun v : FinitePlace E => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v g)).Finite :=
  ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_support_finite g

theorem finPart_props : ∀ (E : Type) [Field E] [NumberField E] (σ τ : Type),
    (∀ g : MvPolynomial σ E, g ≠ 0 → {v : FinitePlace E | ReciprocityTheory.MultiplicativeHeights.gaussAbs v g ≠ 1}.Finite ∧
      ∀ v : FinitePlace E, 0 < ReciprocityTheory.MultiplicativeHeights.gaussAbs v g) ∧
    (∀ (g : MvPolynomial σ E) (g' : MvPolynomial τ E), g ≠ 0 → g' ≠ 0 →
      (∀ v : FinitePlace E, ReciprocityTheory.MultiplicativeHeights.gaussAbs v g' ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v g) → finPart g' ≤ finPart g) ∧
    ∀ (g : MvPolynomial σ E) (m : σ →₀ ℕ), g.coeff m ≠ 0 →
      -mean E (fun s => Real.log ‖s (g.coeff m)‖) ≤ finPart g := by
  intro E _ _ σ τ
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  refine ⟨fun g hg => ⟨?_, fun v => gauss_abs_pos_of_ne_zero v g hg⟩, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite g hg
  · intro g g' hg hg' hle
    unfold finPart
    refine div_le_div_of_nonneg_right ?_ hd.le
    exact finsum_le_finsum' (log_gaussAbs_support_finite g') (log_gaussAbs_support_finite g)
      (fun v => Real.log_le_log (gauss_abs_pos_of_ne_zero v g' hg') (hle v))
  · intro g m hm
    have hg : g ≠ 0 := by
      rintro rfl; exact hm (by simp)
    set c := g.coeff m with hc
    have h1 : ∑ᶠ v : FinitePlace E, Real.log (v c) ≤ ∑ᶠ v : FinitePlace E, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v g) :=
      finsum_le_finsum'
        ((FinitePlace.hasFiniteMulSupport hm).subset (by
          intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one]))
        (log_gaussAbs_support_finite g)
        (fun v => Real.log_le_log (FinitePlace.pos_iff.mpr hm) (coeff_le_gauss_abs v g m))
    rw [ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm c hm] at h1
    unfold mean finPart
    rw [sum_log_norm_embedding_eq c hm, ← neg_div]
    exact div_le_div_of_nonneg_right h1 hd.le

end GlobalTheory.HSFinPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem coefM_one (z : ℂ) : coefM z 1 = z := by
  simp [coefM, Complex.ext_iff]

theorem coefM_neg_one (z : ℂ) : coefM z (-1) = star z := by
  simp [coefM, Complex.ext_iff]

theorem coefD_one (z : ℂ) : coefD z 1 = -star z := by
  simp [coefD, Complex.ext_iff]

theorem coefD_neg_one (z : ℂ) : coefD z (-1) = -z := by
  simp [coefD, Complex.ext_iff]

theorem heisOp_eq_sum_mul_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  intro P Q R S c
  unfold heisOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ -
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [raiB, lowB, linePos, lineSign, coefM_one, coefM_neg_one, coefD_one, coefD_neg_one, if_true,
      Bool.false_eq_true, if_false] <;>
    module

end GlobalTheory.CCRFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderivStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHeisenbergOperatorOfCoords_eq_sum_mulLeft_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  first | exact @GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv | exact GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv | (intros; apply GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

theorem withBot_lt_of_add_one_le_nat {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) :=
  withBot_lt_of_add_one_lt (lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n))

theorem topSelf_pull_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  intro k _ X Y _ _ p q D hq hX hY π hπ B hB
  letI := GlobalTheory.algebraΓOfHom q
  have hs : strHom k Y = q := GlobalTheory.strHom_eq (f := q) fun _ => rfl
  have hη : genericPoint X ∈ (closure ({π (genericPoint Y)} : Set X))ᶜ := fun h =>
    hπ (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := dim_closure_add_one_le (genericPoint_specializes (π (genericPoint Y)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint X} : Set X)) = topologicalKrullDim X := by
    rw [(genericPoint_spec X).def]
    exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  have h3 := withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hX))
  have h := interNum_pull_eq_zero k 0 D Y X (hs ▸ hq) (by rwa [Nat.zero_add]) π h3
    (fun i => i.elim0) (fun i => i.elim0) (fun _ => B) (fun _ => hB)
  rw [topSelf_def, ← interNum_comp_equiv k _ (fun _ => pull_isLB hB π)
    (Equiv.emptySum (Fin 0) (Fin D)), ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.PullVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  first | exact @GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | exact GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant | (intros; apply GlobalTheory.PullVanish.topSelf_pull_eq_zero_of_not_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuum
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.FockVac

theorem jm_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (i : Ix P Q) (j : Ix R S) :
    (Jm P Q * c * Jm R S : Matrix (Ix P Q) (Ix R S) ℂ) i j = lineSign (p := P) (q := Q) (r := R) (s := S) i j * c i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Jm, Formalism.UG.Jpq, lineSign, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem heisOp_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) (1 : Formalism.BasicNotions.TH.Pol P Q R S) = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply]
  rw [smul_comm Complex.I]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ -
  rw [Matrix.smul_apply, jm_mul_jm_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [raiB, lowB, linePos, lineSign, smul_smul]

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sumPl_heisOp_vacuum {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [atPl_tprod, atPl_tprod, heisOp_one, MultilinearMap.map_update_smul]
  rfl

end GlobalTheory.FockVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuumStatement
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVac.sumPl_heisOp_vacuum | exact GlobalTheory.FockVac.sumPl_heisOp_vacuum | (intros; apply GlobalTheory.FockVac.sumPl_heisOp_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.RallisEuler


open GlobalTheory.LFun in
theorem trivPar_euler : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  intro D χ Sf n hU
  refine ⟨(n : ℝ) / 2 + 1, fun s hs => ?_⟩
  have hs' : (n : ℝ) / 2 + 1 < s.re := hs
  set T := above D.host.E (Sf : Set (FinPl D)) with hT

  have hc : ∀ i ∈ Finset.range n, HasProd (fun w : {w // w ∉ T} => locL (charFam χ⁻¹) w.1 (s + (n : ℂ) / 2 - i))
      (charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
    refine (converges_charFam T χ⁻¹ ?_).hasProd
    simp
    linarith
  have hp := hasProd_prod hc
  show (∏ i ∈ Finset.range n, charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) =
    LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)
  rw [← hp.tprod_eq]
  unfold LSD LSTw LS eulerProd
  refine tprod_congr fun w => ?_
  have hw : UnrAt χ⁻¹ w.1 := (hU w.1 w.2).inv
  rw [GlobalTheory.BottomRallis.trivPar, twist_segFam, locL_segFam']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [locL, locL, charFam_of_unrAt hw, val_inv]
  congr 2
  · simp
  · congr 1
    push_cast
    ring

end GlobalTheory.RallisEuler
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeLStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  first | exact @GlobalTheory.RallisEuler.trivPar_euler | exact GlobalTheory.RallisEuler.trivPar_euler | (intros; apply GlobalTheory.RallisEuler.trivPar_euler <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Adelic.LinSys

theorem exists_ratio_mem_of_point {F K : Type} [Field F] [Field K] (S : LinSys F) (hS : S.IsVariety) (r e : ℕ)
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (hcov : ∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i)))
    (x : Sp K ⟶ S.Y) (V : ValuationSubring K) (hV : ∀ c, S.baseHom x c ∈ V) :
    ∃ i, S.val x (S.comb (u i)) ≠ 0 ∧ S.powVal x th / S.val x (S.comb (u i)) ^ e ∈ V := by
  have hpr : IsProper S.str := GlobalTheory.CommonModel.isProper_of_isProjOver hS.proj
  let φ : F →+* V := (S.baseHom x).codRestrict V hV
  have hsq : x ≫ S.str = specAlgebraMap V K ≫ spMap φ := by
    rw [S.comp_str x, ← Spec.map_comp]
    rfl
  obtain ⟨l, hl, -⟩ := exists_valuativeExtension S.str (spMap φ) x hsq
  have hx : spMap (algebraMap V K) ≫ l = x := hl
  obtain ⟨i, hi⟩ := hcov (l (IsLocalRing.closedPoint V))
  have hyc := S.mem_chartAt (l (IsLocalRing.closedPoint V))
  set c := S.chartAt (l (IsLocalRing.closedPoint V))
  have hU : ⊤ ≤ l ⁻¹ᵁ S.L.U c := (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 hyc
  have hB : ⊤ ≤ l ⁻¹ᵁ S.Y.basicOpen ((S.comb (u i)).f c) :=
    (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 ((mem_nonzeroLocus_iff_basicOpen _ hyc).1 hi)
  obtain ⟨w, hw⟩ := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff l _ hU _).2 hB
  obtain ⟨hU', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap V K) l _ hU
  rw [hx] at hU' hval
  obtain ⟨c₀, hc₀, h₁, h₂⟩ := S.exists_frame_change x c ((le_iff_ptOf_mem x _).1 hU')
  have ha := (h₁ (S.comb (u i))).symm.trans (hval _)
  have ht := (h₂ e th).symm.trans (hval _)
  rw [← hw] at ha
  have hw₀ : algebraMap V K (w : V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 w.ne_zero
  have hv : S.val x (S.comb (u i)) ≠ 0 := fun h => hw₀ (by rw [← ha, h, mul_zero])
  refine ⟨i, hv, ?_⟩
  have key : S.powVal x th / S.val x (S.comb (u i)) ^ e =
      algebraMap V K (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e) := by
    have hinv : algebraMap V K ((w⁻¹ : Vˣ) : V) = (algebraMap V K (w : V))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [map_mul, map_pow, ← ht, hinv, ← ha, zpow_natCast]
    rw [inv_pow, mul_pow]
    field_simp
  rw [key]
  exact (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e).2

theorem exists_ratio_mem_valuationSubring : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V :=
  fun _ _ S hS r e u th hcov η _ V hV => exists_ratio_mem_of_point S hS r e u th hcov (resPt η) V hV

end GlobalTheory.Adelic.LinSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPointStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V := by
  first | exact @GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | exact GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | (intros; apply GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring <;> assumption)
end
end
