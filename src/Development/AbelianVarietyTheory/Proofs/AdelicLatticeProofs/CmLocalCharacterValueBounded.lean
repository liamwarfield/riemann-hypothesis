module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCmAdeleTensorEquivMixedFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.InfAdeleMixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toMixed [_root_.NumberField.IsTotallyComplex E] {R : Type} [CommRing R]
    (θ : {w : InfinitePlace E // w.IsComplex} → (R →+* ℂ)) : R →+* mixedSpace E :=
  RingHom.prod
    (Pi.ringHom fun w : {w : InfinitePlace E // w.IsReal} =>
      (False.elim (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2) : R →+* ℝ))
    (Pi.ringHom θ)

theorem mixed_ext [_root_.NumberField.IsTotallyComplex E] {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext fun w =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2).elim) (funext h)

theorem exists_place_over [_root_.NumberField.IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨⟨w, IsTotallyComplex.isComplex w⟩, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw

theorem exists_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hθ := fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)
  obtain ⟨δ, hδ0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hc' τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact hδ0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ v : InfinitePlace F, v.Completion ≃ᵢ ℝ := fun v =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v x, r v x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x :=
    fun _ _ => rfl
  let p : {w : InfinitePlace E // w.IsComplex} → InfinitePlace F := fun w =>
    InfinitePlace.mk (w.1.embedding.comp (algebraMap F E))
  let Θ : InfiniteAdeleRing F ⊗[F] E →+* mixedSpace E := toMixed fun w => θ0 w.1.embedding
  have hΘ : ∀ z w, (Θ z).2 w = θ0 w.1.embedding z := fun _ _ => rfl
  have hval : ∀ (w) (a b : InfiniteAdeleRing F), (Θ (a ⊗ₜ 1 + b ⊗ₜ δ)).2 w =
      ⟨r _ (a (p w)), r _ (b (p w)) * (w.1.embedding δ).im⟩ := by
    intro w a b
    rw [hΘ, map_add (f := _), hθ, hθ, GlobalTheory.InfAdeleCM.ext_eq_ofReal, GlobalTheory.InfAdeleCM.ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, hr, p]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, hr, p]
  choose t ht using exists_place_over (F := F) (E := E)
  have ht' : ∀ v, p (t v) = v := ht
  have htp : ∀ w, t (p w) = w := by
    intro w
    apply Subtype.ext
    rw [← InfinitePlace.mk_embedding (t (p w)).1, ← InfinitePlace.mk_embedding w.1]
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' hδ0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff (ht (p w))) with e | e
    · rw [e]
    · rw [e, InfinitePlace.mk_conjugate_eq]
  let A : (({w : InfinitePlace E // w.IsComplex}) → ℝ) → InfiniteAdeleRing F := fun y v => (r v).symm (y (t v))
  have hA : Continuous A := continuous_pi fun v => (r v).symm.continuous.comp (continuous_apply (t v))
  have hA' : ∀ y w, r _ (A y (p w)) = y w := by
    intro y w
    simp only [A, IsometryEquiv.apply_symm_apply, htp]
  let G : mixedSpace E → InfiniteAdeleRing F ⊗[F] E := fun z =>
    A (fun w => (z.2 w).re) ⊗ₜ[F] (1 : E) + A (fun w => (z.2 w).im / (w.1.embedding δ).im) ⊗ₜ[F] δ
  have hG : ∀ z, Θ (G z) = z := by
    intro z
    refine mixed_ext fun w => ?_
    rw [hval]
    refine Complex.ext (hA' (fun w => (z.2 w).re) w) ?_
    have h := hA' (fun w => (z.2 w).im / (w.1.embedding δ).im) w
    exact (congrArg (· * (w.1.embedding δ).im) h).trans (div_mul_cancel₀ _ (him _))
  have hinj : Function.Injective Θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, b, rfl⟩ := GlobalTheory.InfAdeleCM.exists_decomp hs z
    have key : ∀ v, a v = 0 ∧ b v = 0 := by
      intro v
      have h := hval (t v) a b
      rw [hz, ht' v] at h
      have h1 := congrArg Complex.re h
      have h3 := congrArg Complex.im h
      simp only [Prod.snd_zero, Pi.zero_apply, Complex.zero_re, Complex.zero_im] at h1 h3
      have z0 : r v 0 = 0 := by rw [hr, map_zero]
      exact ⟨(r v).injective (by rw [z0, ← h1]),
        (r v).injective (by rw [z0]; exact (mul_eq_zero.1 h3.symm).resolve_right (him _))⟩
    have ha : a = 0 := funext fun v => (key v).1
    have hb : b = 0 := funext fun v => (key v).2
    rw [ha, hb, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  let e : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E := RingEquiv.ofBijective Θ ⟨hinj, fun z => ⟨G z, hG z⟩⟩
  have he : ∀ z, e z = Θ z := fun _ => rfl
  have htm : ∀ x : E, Continuous fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x := by
    intro x
    have : (fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x) = fun a => a • ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.fun_smul continuous_id' continuous_const
  refine ⟨e, fun x => mixed_ext fun w => ?_, ?_, fun u hu => ?_⟩
  · rw [he, hΘ, h0, mixedEmbedding_apply_isComplex]
  · have : (e.symm : mixedSpace E → _) = G := by
      funext z
      rw [RingEquiv.symm_apply_eq, he, hG]
    rw [this]
    have c1 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).re) := by fun_prop
    have c2 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).im / (w.1.embedding δ).im) := by fun_prop
    exact Continuous.fun_add ((htm 1).comp' (hA.comp' c1)) ((htm δ).comp' (hA.comp' c2))
  · have hne : ∀ w, ((u : mixedSpace E).2 w).re ≠ 0 := by
      intro w h
      have h1 : (u : mixedSpace E).2 w = 0 := Complex.ext h (hu w)
      have h3 := congrArg (fun z : mixedSpace E => z.2 w) u.mul_inv
      simp only [Prod.snd_mul, Pi.mul_apply, h1, zero_mul, Prod.snd_one, Pi.one_apply] at h3
      exact zero_ne_one h3
    have hunit : IsUnit (A fun w => ((u : mixedSpace E).2 w).re) := by
      refine Pi.isUnit_iff.2 fun v => IsUnit.mk0 _ fun h => hne (t v) ?_
      have h1 : (r v).symm ((u : mixedSpace E).2 (t v)).re = 0 := h
      have h3 := congrArg (r v) h1
      rwa [IsometryEquiv.apply_symm_apply, hr, map_zero] at h3
    refine ⟨hunit.unit, mixed_ext fun w => ?_⟩
    have h := hval w (A fun w => ((u : mixedSpace E).2 w).re) 0
    rw [TensorProduct.zero_tmul, add_zero] at h
    rw [IsUnit.unit_spec, he, h]
    refine Complex.ext (hA' (fun w => ((u : mixedSpace E).2 w).re) w) ?_
    have z0 : r (p w) ((0 : InfiniteAdeleRing F) (p w)) = 0 := by
      rw [hr]
      exact map_zero _
    rw [hu w]
    simp only [z0, zero_mul]

end GlobalTheory.InfAdeleMixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpaceStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  exact GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCmAdeleTensorEquivMixedFinite
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleCM

theorem exists_adele_tensor_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI t1 : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  obtain ⟨θ, hθ1, hθc, hθ3⟩ := GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace F E σ hF hE h2 hσ
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr θ ι)
  have hΦ : ∀ z, Φ z = (θ (e z).1, ι (e z).2) := fun z => rfl
  refine ⟨Φ, fun x => ?_, fun y => ?_, fun v ε h0 h1 hv => ⟨?_, fun P => ?_⟩, ?_, fun x hx2 hx1 => ?_⟩
  · rw [hΦ, he1, he2]
    exact Prod.ext (hθ1 x) (hι1 x)
  · rw [← (he y).2]
    exact hι2 (e y).2
  · rw [hΦ, he1, h0]
    simp
  · rw [hΦ, he2]
    exact hι3 v ε.2 h1 hv P
  · have : (Φ.symm : _ → _) = fun w => e.symm (θ.symm w.1, ι.symm w.2) := rfl
    rw [this]
    exact hec.comp ((hθc.comp continuous_fst).prodMk (hιc.comp continuous_snd))
  · obtain ⟨a, ha⟩ := hθ3 (Units.map (RingHom.fst (mixedSpace E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x) hx1
    refine ⟨⟨((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
      ((a⁻¹ : (InfiniteAdeleRing F)ˣ), (1 : FiniteAdeleRing (𝓞 F) F)), ?_, ?_⟩, ?_⟩
    · exact Prod.ext a.mul_inv (mul_one _)
    · exact Prod.ext a.inv_mul (mul_one _)
    · rw [hΦ, he1, he2]
      refine Prod.ext ha ?_
      rw [hx2]
      exact map_one ι

end GlobalTheory.AdeleCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCmAdeleTensorEquivMixedFiniteStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_adele_tensor_equiv_mixed_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  first | exact @GlobalTheory.AdeleCM.exists_adele_tensor_equiv | exact GlobalTheory.AdeleCM.exists_adele_tensor_equiv | (intros; apply GlobalTheory.AdeleCM.exists_adele_tensor_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionary
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem cmAdele_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AF F)ˣ, Φ (idF F E a : (AE F E)ˣ) = x := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hex := GlobalTheory.T.exists_cm_adele_tensor_equiv_mixed_finite F E σ h1 h2 h3 h4
  obtain ⟨Φ, a1, a2, a3, a4, a5⟩ := hex
  refine ⟨Φ, a1, a2, ?_, a4, a5⟩
  rintro v ε ⟨α, rfl, hv, hv'⟩
  exact a3 v (pairA F 0 α) rfl hv hv'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionaryStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_adeles_standardModel_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AF F)ˣ, Φ (idF F E a : (AE F E)ˣ) = x := by
  first | exact @GlobalTheory.cmAdele_dictionary | exact GlobalTheory.cmAdele_dictionary | (intros; apply GlobalTheory.cmAdele_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdeleIdemPrimeCriterion
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory

private lemma one_lt_valued_inv_iff_mem {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) (hx : x ≠ 0) :
    1 < Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) ↔ x ∈ Q.asIdeal := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))

theorem _root_.GlobalTheory.adele_idem_prime_criterion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E)), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ (e : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (ε : _root_.HeckeCharacterZeroLocus.ThmBIn.AF F), _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → e * e = e → e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e → ((∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E)) ↔ ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0)) := by
  intro F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε
  obtain ⟨h0, -⟩ := hplace v ε hε
  have ha : (Φ e).1 = 0 := by
    have h := congrArg (fun z => (Φ z).1) heε
    simp only [map_mul, Prod.fst_mul, h0, mul_zero] at h
    exact h.symm
  have hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1 := by
    intro Q
    have h := congrArg (fun z => (Φ z).2 Q) he
    rw [map_mul] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  have key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔
      ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hint, map_mul, hΦ]
    push_neg
    constructor
    · rintro ⟨Q, hQ⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ
      rcases hidem Q with h | h
      · rw [h, zero_mul, map_zero] at hQ
        exact absurd hQ (not_lt.mpr zero_le')
      · rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx] at hQ
        exact ⟨Q, h, hQ⟩
    · rintro ⟨Q, h, hQ⟩
      refine ⟨Q, ?_⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)
      rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx]
      exact hQ
  constructor
  · intro hcrit
    have hS : ∀ Q, (Φ e).2 Q = 1 → Q = P := by
      intro Q hQ
      by_contra hne
      have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
        hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx : x ≠ 0 := fun h => hxP (h ▸ P.asIdeal.zero_mem)
      exact hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))
    obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (key x hx).mp ((hcrit x hx).mp hxP)
    have hQP := hS Q hQ
    subst hQP
    refine ⟨ha, hQ, fun R hR => ?_⟩
    rcases hidem R with h | h
    · exact h
    · exact absurd (hS R h) hR
  · rintro ⟨-, hP, hQ⟩ x hx
    rw [key x hx]
    constructor
    · exact fun hxP => ⟨P, hP, hxP⟩
    · rintro ⟨Q, h, hxQ⟩
      by_cases hQP : Q = P
      · exact hQP ▸ hxQ
      · rw [hQ Q hQP] at h
        exact absurd h zero_ne_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMField
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMField
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.PrimeIdemExists

theorem exists_indicator (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : FiniteAdeleRing (𝓞 K) K, a v = 1 ∧ ∀ w, w ≠ v → a w = 0 := by
  refine ⟨(⟨fun w => if w = v then 1 else 0, ?_⟩ :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite), ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun w => ?_
    beta_reduce
    by_cases h : w = v
    · rw [if_pos h]; exact one_mem (w.adicCompletionIntegers K)
    · rw [if_neg h]; exact zero_mem (w.adicCompletionIntegers K)
  · exact if_pos rfl
  · intro w hw; exact if_neg hw

theorem cA_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ε : AF F) :
    cA σ (algebraMap (AF F) (AE F E) ε) = algebraMap (AF F) (AE F E) ε := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (ε ⊗ₜ[F] (1 : E)) = ε ⊗ₜ[F] (1 : E)
  simp

theorem cA_incA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : E) :
    cA σ (incA F E x) = incA F E (σ x) := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] (σ x)
  simp

theorem prod_ext {K : Type} [Field K] [NumberField K] {M : Type} {a b : M × FiniteAdeleRing (𝓞 K) K}
    (h1 : a.1 = b.1) (h2 : ∀ P, a.2 P = b.2 P) : a = b :=
  Prod.ext h1 (DFunLike.ext _ _ h2)

theorem exists_isPrimeIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  intro F E _ _ _ _ _ σ hσ P
  obtain ⟨c, hcc, -, hcmem, hcund, -, hcint, -⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have crit := GlobalTheory.adele_idem_prime_criterion F E Φ hΦ1 hΦ2 hΦ3
  obtain ⟨α, hα1, hα0⟩ := exists_indicator F (P.under (𝓞 F))
  have hε : IsPlaceIdem F (P.under (𝓞 F)) (pairA F 0 α) := ⟨α, rfl, hα1, hα0⟩
  set ε := pairA F 0 α with hεdef
  set η := algebraMap (AF F) (AE F E) ε with hη
  obtain ⟨hη1, hη2⟩ := hΦ3 _ _ hε
  rw [← hη] at hη1 hη2
  have hη3 : ∀ Q, (Φ η).2 Q = if Q = P ∨ Q = c P then 1 else 0 := by
    intro Q
    rw [hη2 Q]
    exact if_congr (eq_comm.trans (hcund P Q)) rfl rfl
  have mulap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a * b).2 Q = a.2 Q * b.2 Q :=
    fun _ _ _ => rfl
  have addap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a + b).2 Q = a.2 Q + b.2 Q :=
    fun _ _ _ => rfl
  by_cases hP : c P = P
  · have hηη : η * η = η := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, hη1, mul_zero]
      · rw [mulap, hη3]; split_ifs <;> simp
    refine ⟨η, η, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ?_⟩⟩
    refine (crit η P _ ε hε hηη hηη).2 ⟨hη1, ?_, fun Q hQ => ?_⟩
    · rw [hη3, if_pos (Or.inl rfl)]
    · rw [hη3, if_neg]
      rw [hP]; simpa using hQ
  · obtain ⟨β, hβ1, hβ0⟩ := exists_indicator E P
    set e : AE F E := Φ.symm (0, β) with he
    have hΦe : Φ e = (0, β) := Φ.apply_symm_apply _
    have he1 : (Φ e).1 = 0 := by rw [hΦe]
    have heP : (Φ e).2 P = 1 := by rw [hΦe]; exact hβ1
    have he0 : ∀ Q, Q ≠ P → (Φ e).2 Q = 0 := by rw [hΦe]; exact hβ0
    have hee : e * e = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, mul_zero]
      · rw [mulap]
        by_cases hQ : Q = P
        · subst hQ; rw [heP, mul_one]
        · rw [he0 Q hQ, mul_zero]
    have heη : e * η = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hη3, if_pos (Or.inl hQ), mul_one]
        · rw [he0 Q hQ, zero_mul]
    have hcr := (crit e P _ ε hε hee heη).2 ⟨he1, heP, he0⟩
    have hσσ : ∀ x : E, σ (σ x) = x := by
      intro x
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [hσ.2.2.2, hσ.2.2.2, star_star]
    have hcr' : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ (c P).asIdeal ↔
        finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
      intro x hx
      have hint : IsIntegral ℤ (σ (x : E)) :=
        (RingOfIntegers.isIntegral_coe x).map (σ.toRingHom.toIntAlgHom)
      let y : 𝓞 E := ⟨σ (x : E), hint⟩
      have hy : (y : E) = σ (x : E) := rfl
      have hxy : (x : E) = σ (y : E) := by rw [hy, hσσ]
      have hy0 : y ≠ 0 := by
        intro h0
        apply hx
        apply RingOfIntegers.ext
        rw [hxy, h0]; simp
      rw [(hcmem P y x hxy).1, hcr y hy0, ← hcint, map_mul (cA σ), cA_incA, map_inv₀, ← hxy]
    have hee' : cA σ e * cA σ e = cA σ e := by rw [← map_mul, hee]
    have heη' : cA σ e * η = cA σ e := by
      have := congrArg (cA σ) heη
      rwa [map_mul, hη, cA_algebraMap] at this
    obtain ⟨hc1, hcP, hc0⟩ := (crit (cA σ e) (c P) _ ε hε hee' heη').1 hcr'
    refine ⟨e, e + cA σ e, Or.inl ⟨⟨⟨hee, ?_, _, ε, hε, ?_⟩, hcr⟩, rfl⟩⟩
    · apply Φ.injective
      rw [map_mul, map_zero]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]; rfl
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hc0 Q (by rw [hQ]; exact fun h => hP h.symm), mul_zero]; rfl
        · rw [he0 Q hQ, zero_mul]; rfl
    · apply Φ.injective
      rw [map_add (f := _), ← hη]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_add, he1, hc1, hη1, add_zero]
      · rw [addap, hη3]
        by_cases hQ : Q = P
        · subst hQ
          rw [heP, hc0 _ (fun h => hP h.symm), add_zero, if_pos (Or.inl rfl)]
        · by_cases hQ' : Q = c P
          · subst hQ'
            rw [he0 _ hQ, hcP, zero_add, if_pos (Or.inr rfl)]
          · rw [he0 _ hQ, hc0 _ hQ', add_zero, if_neg (by tauto)]

end GlobalTheory.PrimeIdemExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMFieldStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeIdempotent_CMField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  first | exact @GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | exact GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | (intros; apply GlobalTheory.PrimeIdemExists.exists_isPrimeIdem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrime
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrimeStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotent_eq_indicator_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  first | exact @GlobalTheory.isPrimeIdem_eq_indicator | exact GlobalTheory.isPrimeIdem_eq_indicator | (intros; apply GlobalTheory.isPrimeIdem_eq_indicator <;> assumption)
end
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.HeckeUnif

theorem idem_glue_mul {R : Type*} [CommRing R] {e : R} (he : e * e = e) (a b : R) :
    (e * a + (1 - e)) * (e * b + (1 - e)) = e * (a * b) + (1 - e) := by
  linear_combination (a * b - a - b + 1) * he

theorem intValuation_of_mem_notMem_sq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) {a : R} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.intValuation a = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem unifIdele_exists_chiAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)), (∃ x, IsUnifIdele σ P x) ∧ (IsUnramAt σ χ P → ∀ x, IsUnifIdele σ P x → chiAt σ χ P = (χ x : ℂ)) ∧ ‖chiAt σ χ P‖ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ χ P
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have hu := GlobalTheory.T.primeIdempotent_eq_indicator_prime F E σ Φ h1 h2 h3 P
  obtain ⟨e, f, hef⟩ := GlobalTheory.T.exists_primeIdempotent_CMField F E σ hσ P
  obtain ⟨ea, eb, ec⟩ := hu e f hef
  have huniq : ∀ e' f', IsPrimeIdem σ P e' f' → e' = e := by
    intro e' f' h'
    obtain ⟨ea', eb', ec'⟩ := hu e' f' h'
    apply Φ.injective
    refine Prod.ext (by rw [ea, ea']) ?_
    ext Q
    by_cases hQ : Q = P
    · subst hQ; rw [eb, eb']
    · rw [ec Q hQ, ec' Q hQ]
  let ψ : ∀ Q : HeightOneSpectrum (𝓞 E), AE F E →+* Q.adicCompletion E := fun Q =>
    ((evalV E Q).toRingHom.comp (RingHom.snd _ _)).comp Φ.toRingHom
  have hψ : ∀ Q y, (Φ y).2 Q = ψ Q y := fun _ _ => rfl
  have he : e * e = e := by
    apply Φ.injective
    refine Prod.ext (by rw [map_mul, Prod.fst_mul, ea, mul_zero]) ?_
    ext Q
    rw [hψ, hψ, map_mul, ← hψ]
    by_cases hQ : Q = P
    · subst hQ; rw [eb, mul_one]
    · rw [ec Q hQ, mul_zero]
  have hint : ∀ c : E, P.valuation E c ≤ 1 →
      finPart F E (e * incA F E c + (1 - e)) ∈ intAE F E := by
    intro c hc
    rw [h2]
    intro Q
    rw [hψ, map_add (f := _), map_sub, map_mul, map_one, ← hψ, ← hψ]
    by_cases hQ : Q = P
    · subst hQ
      rw [eb, h1, one_mul, sub_self, add_zero]
      have : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) c) Q) = Q.valuation E c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q c
      exact this.le.trans hc
    · rw [ec Q hQ]; simp
  have hex : ∃ x, IsUnifIdele σ P x := by
    obtain ⟨ϖ, m1, m2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    have hϖ : (ϖ : E) ≠ 0 := by
      intro h
      have : ϖ = 0 := by exact_mod_cast h
      exact m2 (this ▸ zero_mem _)
    have hm : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1 := by
      rw [idem_glue_mul he, ← map_mul, mul_inv_cancel₀ hϖ, map_one]; ring
    exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, e, f, ϖ, hef, by simpa using m1, m2, rfl⟩
  have hq : ∀ x y : (AE F E)ˣ, IsUnifIdele σ P x → IsUnifIdele σ P y →
      ∃ c : E, P.valuation E c ≤ 1 ∧
        ((x * y⁻¹ : (AE F E)ˣ) : AE F E) = e * incA F E c + (1 - e) := by
    rintro x y ⟨e1, f1, a, p1, a1, a2, hx⟩ ⟨e2, f2, b, p2, b1, b2, hy⟩
    rw [huniq _ _ p1] at hx
    rw [huniq _ _ p2] at hy
    have hb : (b : E) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact b2 (this ▸ zero_mem _)
    refine ⟨(a : E) / (b : E), ?_, ?_⟩
    · have va : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P a1 a2]
        exact HeightOneSpectrum.valuation_of_algebraMap P a
      have vb : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P b1 b2]
        exact HeightOneSpectrum.valuation_of_algebraMap P b
      rw [map_div₀, va, vb, div_self WithZero.exp_ne_zero]
    · rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hx, hy, idem_glue_mul he, ← map_mul,
        div_mul_cancel₀ _ hb]
  refine ⟨hex, ?_, ?_⟩
  · intro hun x hx
    have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨hun, hex⟩
    rw [chiAt, dite_eq_left hc]
    have hy := hc.2.choose_spec
    set y := hc.2.choose
    obtain ⟨e', f', p', hχ⟩ := hun
    rw [huniq _ _ p'] at hχ
    obtain ⟨c, c1, c2⟩ := hq y x hy hx
    obtain ⟨d, d1, d2⟩ := hq x y hx hy
    have := hχ (y * x⁻¹) (by rw [c2]; linear_combination (1 - incA F E c) * he)
      (by rw [c2]; exact hint c c1)
      (by rw [mul_inv_rev, inv_inv, d2]; exact hint d d1)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]
  · rw [chiAt]
    split_ifs
    · exact (Circle.norm_coe _).le
    · simp

end GlobalTheory.HeckeUnif
