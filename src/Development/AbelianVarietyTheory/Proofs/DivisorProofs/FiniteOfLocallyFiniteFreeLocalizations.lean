module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
open IsLocalRing

namespace GlobalTheory

open Polynomial

theorem absIntClosed_localization_and_quotient : ∀ (T : Type) [CommRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∀ (M : Submonoid T), 0 ∉ M → (IsDomain (Localization M) ∧ ∀ f : Polynomial (Localization M), f.Monic → 0 < f.natDegree → ∃ x : (Localization M), f.eval x = 0)) ∧ (∀ (p : Ideal T), p.IsPrime → (IsDomain (T ⧸ p) ∧ ∀ f : Polynomial (T ⧸ p), f.Monic → 0 < f.natDegree → ∃ x : (T ⧸ p), f.eval x = 0)) := by
  intro T _ ⟨hdom, hroot⟩
  refine ⟨fun M hM => ?_, fun p hp => ?_⟩
  · have hle : M ≤ nonZeroDivisors T := le_nonZeroDivisors_of_noZeroDivisors hM
    haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M f
      (by rw [hf.leadingCoeff]; exact one_mem _)
    obtain ⟨g, hg, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hf)
    rw [natDegree_scaleRoots] at hgdeg
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    set s : Localization M :=
      algebraMap T (Localization M) (IsLocalization.commonDenom M f.support f.coeff) with hs
    have hu : IsUnit s := IsLocalization.map_units _ _
    refine ⟨algebraMap T (Localization M) y * ↑hu.unit⁻¹, ?_⟩
    have key := scaleRoots_eval_mul f (algebraMap T (Localization M) y * ↑hu.unit⁻¹) s
    have hsr : s * (algebraMap T (Localization M) y * ↑hu.unit⁻¹) =
        algebraMap T (Localization M) y := by
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    rw [hsr, ← hg, eval_map, eval₂_hom, hy, map_zero] at key
    exact ((hu.pow _).mul_right_eq_zero).1 key.symm
  · haveI := hp
    haveI : IsDomain (T ⧸ p) := Ideal.Quotient.isDomain p
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl : f ∈ lifts (Ideal.Quotient.mk p) :=
      (mem_lifts _).2 (map_surjective _ Ideal.Quotient.mk_surjective f)
    obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic hl hf
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    refine ⟨Ideal.Quotient.mk p y, ?_⟩
    rw [← hg, eval_map, eval₂_hom, hy, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubset
open TopologicalSpace

namespace GlobalTheory

theorem topologicalKrullDim_add_one_le_of_ssubset (T : Type) [TopologicalSpace T] (A B : Set T)
    (hA : IsClosed A) (hAi : IsIrreducible A) (hBi : IsIrreducible B) (hAB : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  have hsub : A ⊆ B := hAB.subset
  have hemb : Topology.IsClosedEmbedding (Set.inclusion hsub) :=
    Topology.IsClosedEmbedding.inclusion hsub (hA.preimage continuous_subtype_val)
  haveI : IrreducibleSpace A := Subtype.irreducibleSpace hAi
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi
  let f : IrreducibleCloseds A → IrreducibleCloseds B := fun Z =>
    ⟨Set.inclusion hsub '' (Z : Set A),
      Z.isIrreducible.image _ hemb.continuous.continuousOn,
      hemb.isClosedMap _ Z.isClosed⟩
  let top : IrreducibleCloseds B := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩
  have hf : StrictMono f := by
    intro Z W h
    have h' : (Z : Set A) ⊂ (W : Set A) := h
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.inclusion hsub '' (W : Set A)
    exact hemb.injective.injOn.image_ssubset_image_iff (Set.subset_univ _) (Set.subset_univ _) |>.mpr h'
  have htop : ∀ Z, f Z < top := by
    intro Z
    show Set.inclusion hsub '' (Z : Set A) ⊂ Set.univ
    obtain ⟨x, hxB, hxA⟩ := Set.exists_of_ssubset hAB
    refine Set.ssubset_univ_iff.mpr ?_
    intro h
    have : (⟨x, hxB⟩ : B) ∈ Set.inclusion hsub '' (Z : Set A) := h ▸ Set.mem_univ _
    obtain ⟨y, -, hy⟩ := this
    have : (y : T) = x := congrArg Subtype.val hy
    exact hxA (this ▸ y.2)
  haveI : Nonempty (IrreducibleCloseds A) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ A, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds A) → IrreducibleCloseds B := WithTop.recTopCoe top f
  have hg : StrictMono g := by
    rw [WithTop.strictMono_iff]
    exact ⟨hf, htop⟩
  have := Order.krullDim_le_of_strictMono g hg
  rwa [Order.krullDim_WithTop] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
noncomputable section

namespace GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def inrL (κ κ' : Type) [Fintype κ] [Fintype κ'] : (κ' → V) →L[ℝ] (κ ⊕ κ' → V) :=
  ContinuousLinearMap.pi fun i =>
    Sum.elim (fun _ : κ => (0 : (κ' → V) →L[ℝ] V)) (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => V) j) i

theorem elim_eq_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) = fun y => Sum.elim x 0 + inrL κ κ' y := by
  funext y i
  cases i with
  | inl i => simp [inrL]
  | inr j => simp [inrL]

theorem hasTemperateGrowth_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    Function.HasTemperateGrowth (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) := by
  rw [elim_eq_add]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.hasTemperateGrowth (inrL (V := V) κ κ'))

theorem norm_le_norm_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inr j)

theorem elim_upper {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    ∃ (k : ℕ) (C : ℝ), ∀ y : κ' → V, ‖y‖ ≤ C * (1 + ‖(Sum.elim x y : κ ⊕ κ' → V)‖) ^ k :=
  ⟨1, 1, fun y => by rw [pow_one, one_mul]; linarith [norm_le_norm_elim x y]⟩

def sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) :
    SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x) f

@[simp] theorem sliceR_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := rfl

def sliceRL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x)

theorem sliceRL_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    sliceRL x f = sliceR f x := rfl

end GlobalTheory.SliceSchwartz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi

theorem twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet
  refine ⟨?_, ?_, ?_⟩
  · intro F g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]
    congr 2
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · intro f hf
    have h := mulVec_eq_zero_of_det_nonZeroDivisor _ hdet
      (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by
        funext h
        rw [Pi.zero_apply, ← hf h]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, ← hmul, mul_smul_comm, mul_comm])
    simpa [h1] using congrFun h 1
  · intro F hF h0
    refine mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ
      (by rwa [Matrix.det_transpose]) F ?_
    funext g
    have h2 := congrArg (st g) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    have h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0 := by
      rw [← h2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]
    have h4 := congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4
    simpa [Matrix.mulVec, dotProduct] using h4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSuperposition
open MeasureTheory

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul_one_add_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ a ^ n := pow_nonneg ha n
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) n]
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow 2 a n
      _ ≤ 2 ^ n * (1 + a ^ n) := by
        have : 0 ≤ (2:ℝ) ^ n := by positivity
        nlinarith


open Real in
theorem fourier_inversion_real_linear_forms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : SchwartzMap V ℂ),
    ∃ (m : ℕ) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] (V →L[ℝ] ℝ)) (φ : EuclideanSpace ℝ (Fin m) → ℂ),
      Continuous φ ∧ (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖)) ∧
      ∀ x, ψ x = ∫ w, φ w * Complex.exp ((A w x : ℂ) * Complex.I) := by
  intro V _ _ _ ψ
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let ψ' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm ψ
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ w x, A w x = 2 * π * inner ℝ w (e x) := by
    intro w x
    simp [A]
  let Φ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ := FourierTransform.fourier ψ'
  refine ⟨Module.finrank ℝ V, A, (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ),
    Φ.continuous, fun n => ?_, fun x => ?_⟩
  · have hi : Integrable (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) =>
        2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖)) :=
      ((Φ.integrable_pow_mul volume 0).norm.add (Φ.integrable_pow_mul volume n) |>.congr
        (Filter.Eventually.of_forall fun w => by simp)).const_mul _
    refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + ‖w‖) ^ n * ‖Φ w‖ ≤ 2 ^ n * (1 + ‖w‖ ^ n) * ‖Φ w‖ :=
          mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul_one_add_pow _ (norm_nonneg _) n) (norm_nonneg _)
      _ = 2 ^ n * (‖Φ w‖ + ‖w‖ ^ n * ‖Φ w‖) := by ring
  · have h1 : ψ x = ψ' (e x) := by
      simp [ψ']
    have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x))
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) ψ')
    rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    congr 1
    ext w
    rw [hA, smul_eq_mul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace GlobalTheory.LocalCompletion

theorem exists_localHom_adicCompletion_extend :
    ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  intro A R _ _ _ _ _ hR φ hφ
  let I : Ideal A := maximalIdeal A
  let J : Ideal R := maximalIdeal R
  have hmap : I.map φ ≤ J := ((IsLocalRing.local_hom_tfae φ).out 1 3).1 hφ
  have hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let g : ∀ n : ℕ, AdicCompletion I A →+* R ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [g, RingHom.comp_apply, RingHom.coe_coe]
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
  let e : R ≃ₐ[R] AdicCompletion J R := AdicCompletion.ofAlgEquiv J
  let ψ : AdicCompletion I A →+* R := (e.symm : AdicCompletion J R →+* R).comp (AdicCompletion.liftRingHom J g hg)
  have hψ : ψ.comp (algebraMap A (AdicCompletion I A)) = φ := by
    refine RingHom.ext fun b => e.injective ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rw [show e (φ b) = algebraMap R (AdicCompletion J R) (φ b) from e.commutes (φ b),
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rfl
  refine ⟨ψ, ?_, hψ⟩
  refine ((IsLocalRing.local_hom_tfae ψ).out 1 3).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  exact hmap

end GlobalTheory.LocalCompletion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtendStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupStableInfTypeSpace
namespace GlobalTheory


open Classical in
theorem iSup_stable_inf_typeSpace {G E C : Type} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) (U : C → Submodule ℂ E) (S : C → Prop)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ (c : C) (_ : S c), U c) ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) =
      ⨆ (c : C) (_ : S c), U c ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) := by
  set K : Submodule ℂ E :=
    ⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id) with hK
  have memK : ∀ x, x ∈ K ↔ ∀ h : P, ρ (h : G) x = ((ψ h : ℂˣ) : ℂ) • x := by
    intro x
    simp [hK, Submodule.mem_iInf, sub_eq_zero]
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let T : E →ₗ[ℂ] E :=
    (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G)
  have hT : ∀ x, T x = (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x := by
    intro x
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply]
  have h1 : ∀ x ∈ K, T x = x := by
    intro x hx
    rw [hT]
    have : ∀ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x = x := by
      intro h
      rw [(memK x).1 hx h, smul_smul, Units.inv_mul, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : ∀ x, T x ∈ K := by
    intro x
    rw [memK]
    intro k
    rw [hT, map_smul, smul_comm]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
    intro h
    simp only [Equiv.coe_mulLeft, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply,
      smul_smul]
    congr 1
    rw [← Units.val_mul, mul_inv_rev, mul_comm (ψ h)⁻¹, mul_inv_cancel_left]
  have h3 : ∀ c, ∀ x ∈ U c, T x ∈ U c := by
    intro c x hx
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun h _ =>
      Submodule.smul_mem _ _ (hU c h (Submodule.mem_map_of_mem hx)))
  apply le_antisymm
  · rintro x ⟨hx, hxK⟩
    have hle : (⨆ (c : C) (_ : S c), U c) ≤ (⨆ (c : C) (_ : S c), U c ⊓ K).comap T := by
      refine iSup₂_le fun c hc y hy => ?_
      exact (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c ⊓ K) c hc le_rfl)
        (show T y ∈ U c ⊓ K from ⟨h3 c y hy, h2 y⟩)
    have := hle hx
    rwa [Submodule.mem_comap, h1 x hxK] at this
  · exact iSup₂_le fun c hc => inf_le_inf_right _
      (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c) c hc le_rfl)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.FinrankComp

theorem finrank_eq_mul_of_rankAtStalk (K S T : Type*) [Field K] [CommRing S] [AddCommGroup T]
    [Algebra K S] [Module S T] [Module K T] [IsScalarTower K S T] [Module.Finite K S]
    [Module.Finite S T] [Module.Flat S T] (d : ℕ)
    (h : ∀ p : PrimeSpectrum S, Module.rankAtStalk T p = d) :
    Module.finrank K T = d * Module.finrank K S := by
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq S T d
    (fun P => by
      have := P.isMaximal
      letI := Ideal.Quotient.field P.asIdeal
      have h1 := Module.rankAtStalk_baseChange (R := S) (M := T) (S := S ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, h] at h1
      exact h1)
  rw [(b.equivFun.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_comp_field {X Y : Scheme.{0}} (K : CommRingCat.{0}) (hK : IsField K)
    (φ : X ⟶ Y) (ψ : Y ⟶ Spec K) [IsFinite φ] [Flat φ] [IsFinite ψ] [Flat ψ] (d : ℕ)
    (h : ∀ y, φ.finrank y = d) (z : Spec K) : (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · have _ : IsAffine Y := isAffine_of_isAffineHom ψ
    have := this (φ ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ ψ) (fun y => by
      rw [← h (Y.isoSpec.inv y)]
      exact Scheme.Hom.finrank_of_isPullback (𝟙 X) _ φ Y.isoSpec.inv
        (IsPullback.of_horiz_isIso ⟨by simp⟩) y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom φ
    have := this (X.isoSpec.inv ≫ φ) (fun y => by simpa using h y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective ψ
  obtain ⟨g, rfl⟩ := Spec.map_surjective φ
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rename_i hf1 hf2 hg1 hg2
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank (f := f ≫ g) (hg1.comp hf1) (hf2.comp hg2),
    Scheme.Hom.finrank_SpecMap_eq_finrank hf1 hf2]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hg1 hg2] at h
  letI := hK.toField
  algebraize [f.hom, g.hom, (f ≫ g).hom]
  rw [← RingHom.algebraMap_toAlgebra g.hom, RingHom.finrank_algebraMap] at h
  rw [← RingHom.algebraMap_toAlgebra f.hom, ← RingHom.algebraMap_toAlgebra (f ≫ g).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  have : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq' rfl
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk K S T d h

theorem finrank_comp_of_const {X Y Z : Scheme.{0}} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsFinite φ] [Flat φ]
    [IsFinite ψ] [Flat ψ] (d : ℕ) (h : ∀ y, φ.finrank y = d) (z : Z) :
    (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  let i := Z.fromSpecResidueField z
  let pt : Spec (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  have hz : i pt = z := Scheme.fromSpecResidueField_apply z pt
  have hp := (IsPullback.of_hasPullback φ (pullback.fst ψ i)).paste_vert
    (IsPullback.of_hasPullback ψ i)
  rw [← hz, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp pt,
    ← Scheme.Hom.finrank_pullback_snd ψ i pt]
  exact finrank_comp_field _ (Field.toIsField _) _ _ d
    (fun y => by rw [Scheme.Hom.finrank_pullback_snd, h]) pt

end GlobalTheory.FinrankComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvolEqOfFixed
namespace GlobalTheory

theorem exists_mul_invol_eq_of_fixed (k : Type) [Field k] [Finite k] (τ : k →+* k)
    (hτ : Function.Involutive τ) (hne : ∃ b : k, τ b ≠ b) (c : k) (hc : τ c = c) :
    ∃ a : k, a * τ a = c := by
  classical
  obtain ⟨b, hb⟩ := hne
  let F : Subfield k := τ.eqLocusField (RingHom.id k)
  have hd : b - τ b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)

  let f : F × F → k := fun p => (p.1 : k) + (p.2 : k) * b
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨α, β⟩ ⟨α', β'⟩ h
      have ea : τ (α : k) = α := α.2
      have eb : τ (β : k) = β := β.2
      have ea' : τ (α' : k) = α' := α'.2
      have eb' : τ (β' : k) = β' := β'.2
      have h0 : (α : k) + β * b = α' + β' * b := h
      have h1 : τ ((α : k) + β * b) = τ ((α' : k) + β' * b) := by rw [h0]
      rw [map_add (f := _), map_mul, map_add (f := _), map_mul, ea, eb, ea', eb'] at h1
      have hβ : (β : k) = β' := by
        have h2 : ((β : k) - β') * (b - τ b) = 0 := by linear_combination h0 - h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hd
      have hα : (α : k) = α' := by
        rw [hβ] at h0
        linear_combination h0
      exact Prod.ext (Subtype.ext hα) (Subtype.ext hβ)
    · intro x
      have hβ : τ ((x - τ x) / (b - τ b)) = (x - τ x) / (b - τ b) := by
        rw [map_div₀, map_sub, map_sub, hτ x, hτ b, ← neg_sub x (τ x), ← neg_sub b (τ b),
          neg_div_neg_eq]
      have hm : (x - τ x) / (b - τ b) * (b - τ b) = x - τ x := div_mul_cancel₀ _ hd
      have hα : τ (x - (x - τ x) / (b - τ b) * b) = x - (x - τ x) / (b - τ b) * b := by
        rw [map_sub, map_mul, hβ]
        linear_combination hm
      refine ⟨(⟨x - (x - τ x) / (b - τ b) * b, hα⟩, ⟨(x - τ x) / (b - τ b), hβ⟩), ?_⟩
      show x - (x - τ x) / (b - τ b) * b + (x - τ x) / (b - τ b) * b = x
      ring
  have hcard : Nat.card k = Nat.card F ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hrank : Module.finrank F k = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := k)
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm

  let τ' : k ≃ₐ[F] k := AlgEquiv.ofBijective { τ with commutes' := fun r => r.2 } hτ.bijective
  have hτ' : ∀ x, τ' x = τ x := fun _ => rfl
  have hne1 : (1 : k ≃ₐ[F] k) ≠ τ' := by
    intro h
    apply hb
    rw [← hτ' b, ← h]
    rfl
  have hcardG : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hrank]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, τ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcardG, Finset.card_pair hne1]

  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F k ⟨c, hc⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [ha, huniv, Finset.prod_pair hne1] at h
  refine ⟨a, ?_⟩
  calc a * τ a = (1 : k ≃ₐ[F] k) a * τ' a := rfl
    _ = c := h.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
open scoped TensorProduct

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem formallyEtale_mvPolynomial_eval₂_tensor {k R B : Type} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B)
    (hf : (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  set f := MvPolynomial.eval₂Hom (algebraMap k B) τ with hfdef
  set g := MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i) with hgdef
  letI : Algebra (MvPolynomial (Fin r) k) B := f.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) (R ⊗[k] B) := g.toAlgebra
  letI : Algebra B (R ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (MvPolynomial (Fin r) k) (R ⊗[k] B) :=
    (g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R))).toAlgebra
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) k) B := hf
  have key : g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R)) =
      (algebraMap B (R ⊗[k] B)).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C, f, g,
        MvPolynomial.eval₂Hom_C]
      show (algebraMap k R a) ⊗ₜ[k] (1 : B) = (1 : R) ⊗ₜ[k] algebraMap k B a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X, f, g,
        MvPolynomial.eval₂Hom_X']
      rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) B := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def]
  haveI : IsScalarTower k B (R ⊗[k] B) := IsScalarTower.of_algebraMap_eq fun x =>
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).commutes x).symm
  haveI : IsScalarTower (MvPolynomial (Fin r) k) B (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, key]; rfl
  haveI : IsScalarTower (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI h1 : Algebra.IsPushout k B R (R ⊗[k] B) := inferInstance
  haveI h2 : Algebra.IsPushout (MvPolynomial (Fin r) k) B (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin r) k) R (MvPolynomial (Fin r) R)
      (T := B) (T' := R ⊗[k] B)).1 h1
  haveI : Algebra.IsPushout (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B) :=
    h2.symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    Algebra.FormallyEtale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B))
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHomStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_baseChange_eval_hom : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  first | exact @GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | exact GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | (intros; apply GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegral
open NumberField Polynomial

namespace GlobalTheory

theorem isIntegral_pow_mul_esymm (s : Multiset ℂ) (c : ℂ) (m : ℕ)
    (h : ∀ w ∈ s, IsIntegral ℤ (c * w)) : IsIntegral ℤ (c ^ m * s.esymm m) := by
  rw [Multiset.esymm, ← Multiset.sum_map_mul_left]
  refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  have : c ^ m * t.prod = (t.map (fun w => c * w)).prod := by
    rw [Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_id', ht.2]
  rw [this]
  refine (integralClosure ℤ ℂ).multiset_prod_mem ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
  exact h w (Multiset.mem_of_le ht.1 hw)

theorem finite_monic_roots_bdd_mul_isIntegral :
    ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  intro F _ _ n N B hN
  let φ₀ : F →+* ℂ := (Classical.arbitrary (InfinitePlace F)).embedding
  let B₁ : ℝ := max |B| 1
  let C : ℝ := (N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)
  have hT := Embeddings.finite_of_norm_le F ℂ C
  let f : F[X] → Fin (n + 1) → F := fun P k => (N : F) ^ n * P.coeff k
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_
  · rintro _ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
    refine ⟨?_, fun φ => ?_⟩
    · have hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hdeg : (P.map φ₀).natDegree = n := by rw [hm.natDegree_map, hd]
      have hc := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
      rw [(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map] at hc
      rw [← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]
      show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))
      rw [map_mul, map_pow, map_natCast, hc]
      have hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) =
          ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) *
            ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) := by
        have : (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [this]; ring
      rw [hsplit]
      refine IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _)
        ((isIntegral_one.neg).pow _)) ?_
      exact GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)
    · show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
      have hb := coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _)
        (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))
      rw [coeff_map, hd] at hb
      have hB₁ : (1 : ℝ) ≤ B₁ := le_max_right _ _
      have h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n :=
        mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _))
          (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
  · rintro P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ
    ext i
    by_cases hi : i ≤ n
    · have h := congrFun hPQ ⟨i, by omega⟩
      exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegralStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
noncomputable section

open MvPolynomial

namespace GlobalTheory.NormSheaf

def normForm (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} (x : Fin m → L) :
    MvPolynomial (Fin m) K :=
  (∑ i, (X i : MvPolynomial (Fin m) K) •
    (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K)).det

def normIdeal (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [FiniteDimensional K L]
    [CommRing B] [Algebra B L] (J : Ideal B) : Ideal A :=
  Ideal.span {a | ∃ (m : ℕ) (g : Fin m → B), (∀ i, g i ∈ J) ∧
    ∃ s, algebraMap A K a = (normForm K L (fun i => algebraMap B L (g i))).coeff s}

end GlobalTheory.NormSheaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntMatrixTransposeMulEqSmulOne
namespace GlobalTheory

theorem exists_int_matrix_transpose_mul_eq_smul_one (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares s
  have h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ) := by
    exact_mod_cast h
  refine ⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring

end GlobalTheory
end
