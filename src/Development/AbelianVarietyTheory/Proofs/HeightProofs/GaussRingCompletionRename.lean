module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMvPolynomialSubMapMem
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing

theorem gaussRing_isDVR {σ : Type} [Finite σ] (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime]
    (hP : P = Ideal.map MvPolynomial.C (maximalIdeal O₁))
    (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial σ O₁) O₂]
    [IsLocalization.AtPrime O₂ P] : ∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂ := by
  have hd : IsDomain O₂ :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors
  refine ⟨hd, ?_⟩
  have : IsNoetherianRing O₂ :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (maximalIdeal O₁)
  have hg' : maximalIdeal O₁ = Ideal.span {g} := hg
  have hmax : maximalIdeal O₂ =
      Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
    conv_lhs => rw [hP]
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField O₂ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    intro h
    have h1 := hinj (h.trans (map_zero _).symm)
    have h2 : g = 0 := by simpa using h1
    apply IsDiscreteValuationRing.not_a_field O₁
    rw [hg', h2]; simp
  refine ((IsDiscreteValuationRing.TFAE O₂ hnf).out 1 5).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩

theorem exists_mvPolynomial_sub_map_mem {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal S) (h : ∀ x : S, ∃ a : R, x - φ a ∈ I) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R,
      p - MvPolynomial.map φ q ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) I := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha⟩ := h x
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := Ideal.add_mem _ ha hb
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨a * MvPolynomial.X n, ?_⟩
    have := Ideal.mul_mem_right (MvPolynomial.X n) _ ha
    convert this using 1
    rw [map_mul, MvPolynomial.map_X]; ring

theorem gaussRing_completion :
    ∀ (K : Type) [Field K] [NumberField K] (D N : ℕ) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra (𝓞 K) O₁], Function.Injective (algebraMap (𝓞 K) O₁) → Ideal.map (algebraMap (𝓞 K) O₁) la.asIdeal = IsLocalRing.maximalIdeal O₁ → (∀ x : O₁, ∃ a : 𝓞 K, x - algebraMap (𝓞 K) O₁ a ∈ IsLocalRing.maximalIdeal O₁) → ∀ (P : Ideal (MvPolynomial (TVar D N) O₁)) [P.IsPrime], P = Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O₁) → ∀ (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial (TVar D N) O₁) O₂] [IsLocalization.AtPrime O₂ P], (∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂) ∧ ∃ f : Op D N la →+* O₂, (∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)) ∧ f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (Op D N la)) = IsLocalRing.maximalIdeal O₂ ∧ ∀ x : O₂, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal O₂ := by
  intro K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _
  obtain ⟨hd, hdvr⟩ := gaussRing_isDVR O₁ P hP O₂
  refine ⟨⟨hd, hdvr⟩, ?_⟩
  have hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal := by
    symm
    apply la.isMaximal.eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← hmap]; exact Ideal.le_comap_map
  have hmem : ∀ p : OT K D N,
      MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la := by
    intro p
    rw [hP, MvPolynomial.mem_map_C_iff]
    refine Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm
    refine forall_congr' fun m => ?_
    rw [MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]
  let g : OT K D N →+* O₂ :=
    (algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))
  have hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := P.primeCompl) O₂
      ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩
  let f : Op D N la →+* O₂ := IsLocalization.lift (M := (laT D N la).primeCompl) hu
  have hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g := IsLocalization.lift_comp hu
  have hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) =
      algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p) :=
    fun p => IsLocalization.lift_eq hu p
  have hinj₂ := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective g := hinj₂.comp (MvPolynomial.map_injective _ hinj)
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (laT D N la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf'] at h1
    have h2 : p = 0 := hginj (h1.symm.trans (map_zero g).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h
  have hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]
    congr 1
    rw [hP, ← hmap, Ideal.map_map]
    change Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  refine ⟨f, hf', ?_, ?_, hmax, ?_⟩
  · haveI := Op_isDVR D N la
    algebraize [f]
    have : Module.IsTorsionFree (Op D N la) O₂ := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact hfinj
    unfold RingHom.Flat
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : f a ∈ maximalIdeal O₂ := hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  · intro x
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    obtain ⟨p₀, hp⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p
    obtain ⟨s₀, hs⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres
      (s : MvPolynomial (TVar D N) O₁)
    rw [← hP] at hp hs
    have hs₀ : s₀ ∈ (laT D N la).primeCompl := by
      intro h0
      apply s.2
      have := P.add_mem hs ((hmem _).2 h0)
      simpa using this
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩
    refine ⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩
    have hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂ := by
      intro q hq
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
      exact Ideal.mem_map_of_mem _ hq
    have h1 := hm _ hp
    have h2 := hm _ hs
    rw [map_sub, ← hf'] at h1 h2
    simp only at h hu'
    rw [← hu'] at h2
    have h3 : f u * f ↑u⁻¹ = 1 := by rw [← map_mul]; simp
    have h4 := Ideal.mul_mem_right (f ↑u⁻¹) _
      (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))
    convert h4 using 1
    rw [map_mul, ← h]
    linear_combination (-x) * h3

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open IsLocalRing

section
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem mem_maximalIdeal_iff (x : la.adicCompletionIntegers K) :
    x ∈ maximalIdeal (la.adicCompletionIntegers K) ↔
      Valued.v (x : la.adicCompletion K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h1 : Valued.v (x : la.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K la).1 x.2
  constructor
  · intro h
    have h2 := lt_of_le_of_ne h1 h
    rcases eq_or_ne (Valued.v (x : la.adicCompletion K)) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
  · intro h h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega

theorem algebraMap_injective :
    Function.Injective (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) := by
  intro a b h
  have h1 := congrArg (fun x : la.adicCompletionIntegers K => (x : la.adicCompletion K)) h
  simp only [Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO] at h1
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K (la.adicCompletion K)).injective h1)

theorem map_asIdeal :
    Ideal.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) la.asIdeal =
      maximalIdeal (la.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff, Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO, Formalism.MainNotions.Gaps.LocalGlobalPassage.val_alg,
      HeightOneSpectrum.valuation_of_algebraMap, la.intValuation_le_pow_iff_mem, pow_one]
    exact ha
  · intro x hx
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    obtain ⟨d, hd⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_factor (K := K) la hπ 1 x
      ((mem_maximalIdeal_iff la x).1 hx)
    rw [hd, pow_one]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem exists_sub_mem (x : la.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, x - algebraMap (𝓞 K) (la.adicCompletionIntegers K) a ∈
      maximalIdeal (la.adicCompletionIntegers K) := by
  obtain ⟨r, hr⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.approx (K := K) la x 1
  exact ⟨r, (mem_maximalIdeal_iff la _).2 hr⟩

end

theorem isLocalization_rename {σ τ O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] (I : Ideal O₁)
    (e : σ ≃ τ) (Q : Ideal (MvPolynomial τ O₁)) [Q.IsPrime] (hQ : Q = Ideal.map MvPolynomial.C I)
    (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime] (hP : P = Ideal.map MvPolynomial.C I)
    [Algebra (MvPolynomial τ O₁) O₂] [IsLocalization.AtPrime O₂ Q] :
    letI : Algebra (MvPolynomial σ O₁) O₂ :=
      ((algebraMap (MvPolynomial τ O₁) O₂).comp
        (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom).toAlgebra
    IsLocalization.AtPrime O₂ P := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv Q.primeCompl O₂
    (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm
  have hmap : Ideal.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom P = Q := by
    rw [hP, hQ, Ideal.map_map]
    congr 1
    ext a
    simp
  have hmem : ∀ x, (MvPolynomial.renameEquiv O₁ e).toRingEquiv x ∈ Q ↔ x ∈ P := by
    intro x
    have hb := Ideal.comap_map_of_bijective (MvPolynomial.renameEquiv O₁ e).toRingEquiv.toRingHom
      (MvPolynomial.renameEquiv O₁ e).toRingEquiv.bijective (I := P)
    rw [hmap] at hb
    rw [← hb]
    exact Iff.rfl
  have hM : Q.primeCompl.map (MvPolynomial.renameEquiv O₁ e).toRingEquiv.symm = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      apply hy
      have := (hmem _).2 hx
      rwa [RingEquiv.apply_symm_apply] at this
    · intro hx
      exact ⟨_, fun hy => hx ((hmem x).1 hy), RingEquiv.symm_apply_apply _ _⟩
  rw [hM] at h
  exact h

theorem gaussRing_completion_rename :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ) (e : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N' ≃ Idx D j N), ∃ (f : ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la →+* Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N), f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la)) = IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) ∧ (∀ x : Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) ∧ (∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r)) ∧ (∀ a : B.KO, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.C a)) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧ ∀ p, φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X p)) = @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (Tv X la N (e p)) := by
  intro D B P j X la N D' N' e
  letI alg : Algebra (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) :=
    ((algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) e).toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la))
      (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) p =
      algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (MvPolynomial.rename e p) := fun _ => rfl
  haveI hprime := Formalism.DV.GaussP.gaussIdeal_isPrime (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)
  haveI hloc : IsLocalization.AtPrime (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) :=
    isLocalization_rename (maximalIdeal (X.Ol la)) e (gI X la N) rfl
      (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl
  obtain ⟨-, f, hf, hflat, hloc', hmax, hres⟩ := GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
    (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la)
    (Formalism.DV.gaussIdeal (ReciprocityTheory.ChartRestriction.G.T0.TVar D' N') (X.Ol la)) rfl (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
  have hinj₂ : Function.Injective (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (ReciprocityTheory.ChartRestriction.G.T0.laT D' N' la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at h1
    have h2 : p = 0 := by
      have h3 := hinj₂ (h1.symm.trans (map_zero _).symm)
      have h4 := MvPolynomial.rename_injective e e.injective (h3.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (h4.trans (map_zero _).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) s).mul_left_eq_zero.mp h
  letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) D' N' la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) D' N' la
  have hg : Function.Injective
      ((@algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _).comp f) :=
    (IsFractionRing.injective (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N)).comp hfinj
  let φ : ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg
  have hφ : ∀ r, φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D' N' la r) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _ (f r) := fun r =>
    IsFractionRing.lift_algebraMap (A := ReciprocityTheory.ChartRestriction.G.T0.Op D' N' la) hg r
  have hφp : ∀ p : ReciprocityTheory.ChartRestriction.G.T0.OT B.KO D' N',
      φ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      @algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N) _ _ _
        (algebraMap (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N)
          (MvPolynomial.rename e (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    intro p
    rw [← halg, ← hf, ← hφ, ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hloc', hmax, hres, hφ, ?_, ?_⟩
  · have key : (φ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N')
        (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N')).comp MvPolynomial.C)) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h1 := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h1
      simp only [RingHom.comp_apply]
      rw [h1, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change _ = algebraMap (X.Kl la) (Kp X la N)
        (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun key a
  · intro p
    have h1 := hφp (MvPolynomial.X p)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h1
    exact h1

end GlobalTheory.GaussCompletion
