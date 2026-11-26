module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGeneratorCharTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.TensPres

variable {k : Type} [CommRing k]

def ordIdeal (ρ : Type) (N : ℕ) : Ideal (MvPowerSeries ρ k) where
  carrier := {f | (N : ℕ∞) ≤ f.order}
  add_mem' {f g} hf hg := MvPowerSeries.le_order fun d hd => by
    rw [map_add (f := _), MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
      MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    change (N : ℕ∞) ≤ (c * f).order
    exact hf.trans (le_add_self.trans (MvPowerSeries.le_order_mul (f := c) (g := f)))

theorem mem_ordIdeal_order {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ (N : ℕ∞) ≤ f.order := Iff.rfl

theorem mem_ordIdeal {ρ : Type} {N : ℕ} {f : MvPowerSeries ρ k} :
    f ∈ ordIdeal (k := k) ρ N ↔ ∀ α : ρ →₀ ℕ, α.degree < N → coeff α f = 0 := by
  constructor
  · intro h α hα
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.2 hα) ((mem_ordIdeal_order).1 h))
  · intro h
    exact (mem_ordIdeal_order).2 (MvPowerSeries.nat_le_order h)

theorem one_le_order_X {ρ : Type} (t : ρ) : (1 : ℕ∞) ≤ (X t : MvPowerSeries ρ k).order := by
  have := MvPowerSeries.nat_le_order (f := (X t : MvPowerSeries ρ k)) (n := 1) fun d hd => by
    have : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]; omega
    subst this; simp
  exact_mod_cast this

theorem subst_mem_ordIdeal {ρ ρ' : Type} [Finite ρ] (e : ρ → ρ') {N : ℕ}
    {f : MvPowerSeries ρ k} (hf : f ∈ ordIdeal (k := k) ρ N) :
    subst (fun i => (X (e i) : MvPowerSeries ρ' k)) f ∈ ordIdeal (k := k) ρ' N := by
  have ha : HasSubst (fun i => (X (e i) : MvPowerSeries ρ' k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_X _
  have h1 : (1 : ℕ∞) ≤ ⨅ i, ((fun i => (X (e i) : MvPowerSeries ρ' k)) i).order :=
    le_iInf fun i => one_le_order_X (e i)
  have h2 := MvPowerSeries.le_order_subst ha f
  refine (mem_ordIdeal_order).2 ?_
  calc (N : ℕ∞) ≤ f.order := (mem_ordIdeal_order).1 hf
    _ = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr
    _ ≤ _ := h2

end GlobalTheory.TensPres


open GlobalTheory.TensPres in
theorem GlobalTheory.evA_tensor_presents : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  intro k _ σ τ _ _ A B _ _ _ _ x hx y hy hz hsx hsy
  have hX : ∀ t, evA k _ hz (X t) =
      Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) t :=
    fun t => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (σ ⊕ τ) (A ⊗[k] B) _ hz t
  have hzX : ∀ t, IsNilpotent (evA k _ hz (X t)) := fun t => by rw [hX]; exact hz t
  have hxl : ∀ i, IsNilpotent (x i ⊗ₜ[k] (1 : B)) := fun i => hz (Sum.inl i)
  have hyr : ∀ j, IsNilpotent ((1 : A) ⊗ₜ[k] y j) := fun j => hz (Sum.inr j)
  have hL : ∀ f : MvPowerSeries σ k,
      evA k _ hz (subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f) =
        evA k x hx f ⊗ₜ[k] (1 : B) := by
    intro f
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun i => constantCoeff_X _) _ hxl (fun i => by rw [hX]; rfl) f]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ A).2 (A ⊗[k] B) (Algebra.TensorProduct.includeLeft (S := k))
      x hx _ hxl (fun i => rfl) f).symm
  have hR : ∀ g : MvPowerSeries τ k,
      evA k _ hz (subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g) =
        (1 : A) ⊗ₜ[k] evA k y hy g := by
    intro g
    rw [(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ (A ⊗[k] B)).1 (σ ⊕ τ) (evA k _ hz) hzX _
      (fun j => constantCoeff_X _) _ hyr (fun j => by rw [hX]; rfl) g]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k τ B).2 (A ⊗[k] B) Algebra.TensorProduct.includeRight
      y hy _ hyr (fun j => rfl) g).symm
  refine ⟨?_, ?_⟩
  · intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨f, rfl⟩ := hsx a
      obtain ⟨g, rfl⟩ := hsy b
      refine ⟨subst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) f *
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) g, ?_⟩
      rw [map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add u v hu hv =>
      obtain ⟨f, rfl⟩ := hu
      obtain ⟨g, rfl⟩ := hv
      exact ⟨f + g, map_add _ _ _⟩
  · intro N hNx hNy f hf α hα
    let J := ordIdeal (k := k) (σ ⊕ τ) N
    let mk := Ideal.Quotient.mkₐ k J
    have haL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have haR : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (σ ⊕ τ) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    let φA : MvPowerSeries σ k →ₐ[k] _ := mk.comp (substAlgHom haL)
    let φB : MvPowerSeries τ k →ₐ[k] _ := mk.comp (substAlgHom haR)
    have hkA : ∀ g ∈ RingHom.ker (evA k x hx), φA g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φA, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inl (mem_ordIdeal.2 (hNx g hg))
    have hkB : ∀ g ∈ RingHom.ker (evA k y hy), φB g = 0 := by
      intro g hg
      rw [RingHom.mem_ker] at hg
      simp only [φB, mk, AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact subst_mem_ordIdeal Sum.inr (mem_ordIdeal.2 (hNy g hg))
    let ΨA : A →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φA hkA).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsx).symm.toAlgHom
    let ΨB : B →ₐ[k] _ := (Ideal.Quotient.liftₐ _ φB hkB).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsy).symm.toAlgHom
    have hΨA : ∀ g, ΨA (evA k x hx g) = φA g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φA hkA ((Ideal.quotientKerAlgEquivOfSurjective hsx).symm (evA k x hx g)) = _
      rw [this]
      rfl
    have hΨB : ∀ g, ΨB (evA k y hy g) = φB g := by
      intro g
      have : (Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g) =
          Ideal.Quotient.mk _ g := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      change Ideal.Quotient.liftₐ _ φB hkB ((Ideal.quotientKerAlgEquivOfSurjective hsy).symm (evA k y hy g)) = _
      rw [this]
      rfl
    let Ψ := Algebra.TensorProduct.lift ΨA ΨB (fun _ _ => Commute.all _ _)
    have hnil : ∀ t, IsNilpotent (mk (X t)) := by
      intro t
      refine ⟨N, ?_⟩
      rw [← map_pow]
      simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      refine (mem_ordIdeal_order).2 ?_
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • (X t : MvPowerSeries (σ ⊕ τ) k).order := by gcongr; exact one_le_order_X t
        _ ≤ _ := MvPowerSeries.le_order_pow _
    have huniq := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (σ ⊕ τ) _ mk (Ψ.comp (evA k _ hz)) hnil (by
      intro t
      rw [AlgHom.comp_apply, hX]
      cases t with
      | inl i =>
        simp only [Sum.elim_inl, Ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hΨA]
        simp only [φA, AlgHom.comp_apply, coe_substAlgHom, subst_X haL]
      | inr j =>
        simp only [Sum.elim_inr, Ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rw [← GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k τ B y hy j, hΨB]
        simp only [φB, AlgHom.comp_apply, coe_substAlgHom, subst_X haR])
    have hmk : mk f = 0 := by
      rw [huniq, AlgHom.comp_apply, hf, map_zero]
    simp only [mk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact mem_ordIdeal.1 hmk α hα
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProductStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  first | exact @GlobalTheory.evA_tensor_presents | exact GlobalTheory.evA_tensor_presents | (intros; apply GlobalTheory.evA_tensor_presents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernDescend

theorem chernIntegrableOn_descend : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  intro k _ Y _ q e hY Y' _ ρ hY' hη hδ N σ U f hf hint
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hY hY' ρ rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  have hFm : Measurable (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ)) :=
    (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : Y.Opens, PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' ptsIn q σ W =
      ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn q σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn q σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : ∀ ε : ℤˣ, (N.φ σ).chernPart e ε (ptsIn q σ V)ᶜ = 0 := by
    intro ε
    have h := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((V : Y.Opens) : Set Y)ᶜ V.isOpen.isClosed_compl (by simp [hVη]) σ
      (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : ∀ ε : ℤˣ, (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) =
      Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
        ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
          (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
    intro ε
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hY hY' ρ rfl (N.φ σ) (N.cInf σ) ε (ptsIn q σ V) (isOpen_ptsIn V) _ hcard hchart
        hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart ρ rfl (N.φ σ) (N.cInf σ) c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull (h0 ε)]
  have hδ1 : (1 : ℝ≥0∞) ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero hδ)
  have key : ∀ ε : ℤˣ, IntegrableOn (fun y => f (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (((N.φ σ).pull ρ rfl).chernPart e ε) →
      IntegrableOn f (ptsIn q σ U) ((N.φ σ).chernPart e ε) := by
    intro ε h
    refine ⟨hf.aestronglyMeasurable hUm, ?_⟩
    have h1 := h.2
    unfold HasFiniteIntegral at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    calc ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U)
        ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) *
          ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) :=
          le_mul_of_one_le_left' hδ1
      _ = ∫⁻ y, ‖f y‖ₑ ∂Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
          ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
          rw [← hmeas ε, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, ‖f (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) z)‖ₑ
          ∂((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) :=
          lintegral_map_le _ hFm.aemeasurable
      _ ≤ _ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rw [← hpre U]
          exact Set.preimage_mono Set.inter_subset_left
  exact ⟨key 1 hint.1, key (-1) hint.2⟩

end GlobalTheory.ChernDescend

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  first | exact @GlobalTheory.ChernDescend.chernIntegrableOn_descend | exact GlobalTheory.ChernDescend.chernIntegrableOn_descend | (intros; apply GlobalTheory.ChernDescend.chernIntegrableOn_descend <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntAlter

open Set

variable {k : Type} [CommRing k] {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] {q : Y ⟶ Sp k}
  {σ : k →+* ℂ}

theorem continuousOn_logNorm {L : LB Y} (φ : Weight q σ L) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hφ : φ.IsCInf) :
    ContinuousOn (logNorm φ r) (offSupp q σ (divOfRatSec φ.isLB hr)) := by
  intro y hy
  have ho := isOpen_offSupp (q := q) (σ := σ) (divOfRatSec φ.isLB hr)
  have hi : y ∈ ptsIn q σ (L.U (pick φ.isLB y)) := mem_pick _ y
  have hu := hr.unitAt φ.isLB hy hi
  have hn : ptsIn q σ (L.U (pick φ.isLB y)) ∩ offSupp q σ (divOfRatSec φ.isLB hr) ∈ 𝓝 y :=
    inter_mem ((isOpen_ptsIn _).mem_nhds hi) (ho.mem_nhds hy)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun z => Real.log ‖ratVal (r (pick φ.isLB y) : Y.functionField) z‖ -
      φ.φ (pick φ.isLB y) z / 2) y :=
    ((LogNormInt.continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ _ y hi).continuousAt.div_const 2)
  refine hc.congr ?_
  filter_upwards [hn] with z hz
  exact (logNorm_eq φ hr hz.2 hz.1).symm

variable (M : HermLB q) (ρ : Y' ⟶ Y) (hη : ρ (genericPoint Y') ⤳ genericPoint Y)
  {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)

theorem mem_offSupp_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    y ∈ offSupp (ρ ≫ q) σ ((M.restr ρ).div (MultPull.isRatSec_pull_map ρ hη hr)) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  obtain ⟨c, hc⟩ := exists_chart (M.restr ρ).isLB (under y)
  have hc' : PtsOver.map ρ rfl _ y ∈ ptsIn q σ (M.B.U (c PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hu := hr.unitAt M.isLB hx hc'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  exact mem_offSupp.2 fun h => ((presents_divOfRatSec (M.restr ρ).isLB
    (MultPull.isRatSec_pull_map ρ hη hr)).isEqn c _ hc).mem_supp_iff.1 h hu'

theorem logNorm_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    logNorm ((M.restr ρ).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (c PUnit.unit))) y = logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  have hj : y ∈ ptsIn _ σ ((M.restr ρ).B.U (pick ((M.restr ρ).φ σ).isLB y)) := mem_pick _ y
  have hj' : PtsOver.map ρ rfl _ y ∈
      ptsIn q σ (M.B.U (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hj) PUnit.unit)
  have hu := hr.unitAt M.isLB hx hj'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  have e₁ : ((M.restr ρ).φ σ).φ (pick ((M.restr ρ).φ σ).isLB y) y =
      (M.φ σ).φ (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) (PtsOver.map ρ rfl _ y) :=
    (M.φ σ).pull_φ ρ rfl _ y
  have e₂ : ratVal ((Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) : Y'.functionFieldˣ) : Y'.functionField) y =
      ratVal (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) : Y.functionField)
      (PtsOver.map ρ rfl _ y) := by
    show ratVal (TrueGeo.SmallSec.fnMap ρ hη (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) :
      Y.functionField)) y = _
    rw [TrueGeo.SmallSec.ratVal_eq_valAt y hu'.regAt, TrueGeo.SmallSec.valAt_fnMap ρ hη _ hu.regAt,
      TrueGeo.SmallSec.ratVal_eq_valAt _ hu.regAt]
    rfl
  rw [logNorm_eq (M.φ σ) hr hx hj', logNorm, e₁, e₂]

end GlobalTheory.ArchIntAlter

namespace GlobalTheory.ArchIntAlter

open Set

end GlobalTheory.ArchIntAlter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem isLocalHom_of_map_maximalIdeal {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] (c : W →+* κ)
    (hc : ∀ x ∈ maximalIdeal W, c x = 0) : IsLocalHom c :=
  ⟨fun a ha => by
    by_contra h
    have hm : a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal a).2 h
    rw [hc a hm] at ha
    exact not_isUnit_zero ha⟩

theorem exists_common_residue {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V]
    [IsLocalRing V] (ψ : R →+* W) [IsLocalHom ψ] (g : R →+* V) [IsLocalHom g] :
    ∃ (κ : Type) (_ : Field κ) (c : W →+* κ) (b : V →+* κ), (∀ x ∈ maximalIdeal W, c x = 0) ∧
      (∀ x ∈ maximalIdeal V, b x = 0) ∧ c.comp ψ = b.comp g := by
  letI : Algebra (ResidueField R) (ResidueField W) := (ResidueField.map ψ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField V) := (ResidueField.map g).toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (ResidueField W ⊗[ResidueField R] ResidueField V)
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  refine ⟨_ ⧸ M, inferInstance, q.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (residue W)),
    q.comp ((Algebra.TensorProduct.includeRight.toRingHom).comp (residue V)), fun x hx => ?_, fun x hx => ?_,
    RingHom.ext fun r => ?_⟩
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp only [RingHom.comp_apply]
    congr 1
    rw [← ResidueField.map_residue ψ r, ← ResidueField.map_residue g r]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap (ResidueField R) (ResidueField W) (residue R r)) =
      Algebra.TensorProduct.includeRight (algebraMap (ResidueField R) (ResidueField V) (residue R r))
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem spread₂_of_trait {B : Scheme.{0}} (H : Over B) [GrpObj H]
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
    {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
    {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]
    (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    {R : Type} [CommRing R] [IsLocalRing R] (ιB : Sp R ⟶ B) (HR : Over (Sp R)) [GrpObj HR] [IsCommMonObj HR]
    (φR : HR.left ⟶ H.left) (hR : IsGrpPullback HR H ιB φR)
    (g₁ : R →+* V₁) (β₁' : G₁.left ⟶ HR.left) (eβ₁ : β₁' ≫ φR = β₁) (hξ₁ : spMap g₁ ≫ ιB = ξ₁)
    (g₂ : R →+* V₂) (hg₂ : IsLocalHom g₂) (β₂' : G₂.left ⟶ HR.left) (hβ₂ : IsGrpPullback G₂ HR (spMap g₂) β₂')
    (eβ₂ : β₂' ≫ φR = β₂) (hξ₂ : spMap g₂ ≫ ιB = ξ₂)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ψ₀ : R →+* W) (hψ : IsLocalHom ψ₀)
    (Ω : Type) [Field Ω] (α : W →+* Ω) (hα : Function.Injective α) (b₁ : V₁ →+* Ω)
    (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0) (eα : α.comp ψ₀ = b₁.comp g₁)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ₀)).obj HR).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ₀)).obj HR) (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (hnn : n ≫ pullback.fst HR.hom (spMap ψ₀) = n₁ ≫ β₁')
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ (Over.pullback (spMap ψ₀)).obj HR) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁) :
    ∃ ρ, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  haveI := hψ
  haveI := hg₂
  haveI := hj
  obtain ⟨κ, _, c, b₂, hc0, hb0, ec⟩ := exists_common_residue ψ₀ g₂
  have hcl : IsLocalHom c := isLocalHom_of_map_maximalIdeal c hc0
  have hb₂ := GlobalTheory.TorusPart.map_pow_one_eq_zero hb0
  have hW := isGrpPullback_pullback HR (spMap ψ₀)
  have hm := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap c)
  obtain ⟨m₂, hm₂, em₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₂ (spMap b₂)
    ((hm.comp hW).congr ((GlobalTheory.SpreadTrait.spMap_comp' ψ₀ c).trans
      ((congrArg spMap ec).trans (GlobalTheory.SpreadTrait.spMap_comp' g₂ b₂).symm)) rfl)
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).2 _
    (GlobalTheory.TorusPart.pullTorus hm j) inferInstance
  refine ⟨ρ, W, inferInstance, inferInstance, inferInstance, spMap ψ₀ ≫ ιB, (Over.pullback (spMap ψ₀)).obj HR,
    inferInstance, inferInstance, pullback.fst HR.hom (spMap ψ₀) ≫ φR, j, Ω, inferInstance, α, b₁, hb₁, GΩ,
    inferInstance, n, hn, n₁, hn₁, κ, inferInstance, c, b₂, hb₂, _, inferInstance, _, hm, m₂, hm₂, hW.comp hR, hj, hα,
    hcl, ?_, ?_, ?_, ?_, ej, hρ⟩
  · rw [← hξ₁, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', eα]
  · rw [← hξ₂, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', ec]
  · rw [← Category.assoc, hnn, Category.assoc, eβ₁]
  · rw [← eβ₂, ← Category.assoc m₂, em₂, Category.assoc]

theorem exists_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ hBi hBn hsp
  haveI := hBi
  haveI := hBn
  let R : Type := B.presheaf.stalk (ξ₂ (closedPoint V₂))
  let ιB : Sp R ⟶ B := B.fromSpecStalk (ξ₂ (closedPoint V₂))
  let HR := (Over.pullback ιB).obj H
  have hHR : IsSemiAbelian HR := IsSemiAbelian.pullback ιB H hH
  haveI : IsCommMonObj HR := hHR.comm
  have hR := isGrpPullback_pullback H ιB
  let g₁ : R →+* V₁ := (B.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ₁).hom
  let g₂ : R →+* V₂ := (Scheme.stalkClosedPointTo ξ₂).hom
  have hg₂ : IsLocalHom g₂ := Scheme.isLocalHom_stalkClosedPointTo' ξ₂
  have hξ₁ : spMap g₁ ≫ ιB = ξ₁ := by
    have e : spMap g₁ = Spec.map (Scheme.stalkClosedPointTo ξ₁) ≫ Spec.map (B.presheaf.stalkSpecializes hsp) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hξ₂ : spMap g₂ ≫ ιB = ξ₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₂
  obtain ⟨β₁', hβ₁', eβ₁⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₁) (hβ₁.congr hξ₁.symm rfl)
  obtain ⟨β₂', hβ₂', eβ₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₂) (hβ₂.congr hξ₂.symm rfl)
  by_cases hl : IsLocalHom g₁
  · haveI := hl
    let κ₁ := ResidueField V₁
    have hC : IsLocalHom (PowerSeries.C (R := κ₁)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ₁))⟩
    let c₁ : V₁ →+* PowerSeries κ₁ := (PowerSeries.C (R := κ₁)).comp (residue V₁)
    have hcl : IsLocalHom c₁ := RingHom.isLocalHom_comp _ _
    let ψ₀ : R →+* PowerSeries κ₁ := c₁.comp g₁
    have hψ : IsLocalHom ψ₀ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ₁) (FractionRing (PowerSeries κ₁))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b₁ : V₁ →+* FractionRing (PowerSeries κ₁) := α.comp c₁
    have hc0 : ∀ x ∈ maximalIdeal V₁, c₁ x = 0 := fun x hx => by
      simp [c₁, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), c₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := fun x hx => by
      simp [b₁, hc x hx]
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    obtain ⟨mc, hmc, hmcβ⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₁' (spMap c₁)
      (hm₁.congr (GlobalTheory.SpreadTrait.spMap_comp' g₁ c₁).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap α)
    have hn' : IsGrpPullback _ G₁ (spMap b₁) _ := (hn.comp hmc).congr (GlobalTheory.SpreadTrait.spMap_comp' c₁ α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ pullback.fst HR.hom (spMap ψ₀) =
        (pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ mc) ≫ β₁' := by
      rw [Category.assoc, hmcβ]
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      (PowerSeries κ₁) ψ₀ hψ _ α hα b₁ hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U₁.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨W, _, _, _, ψ₀, Ω, _, αK, b₁, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R HR hHR V₁ g₁ hl
    haveI := hψ
    let alg := algebraMap W (FractionRing W)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective W (FractionRing W))
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    have hG₁' : IsSemiAbelian ((Over.pullback (spMap ψ₀)).obj HR) := IsSemiAbelian.pullback _ HR hHR
    obtain ⟨φ₁, hφ₁, -⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback HR (spMap (alg.comp ψ₀))).congr (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ alg).symm rfl)
    have hn' := isGrpPullback_pullback G₁ (spMap b₁)
    obtain ⟨n, hn, hnm⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ₁').congr ((GlobalTheory.SpreadTrait.spMap_comp' g₁ b₁).trans ((congrArg spMap eα.symm).trans
        (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr W ((Over.pullback (spMap ψ₀)).obj HR) hG₁' _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb' hn') inferInstance
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      W ψ₀ hψ Ω (αK.comp alg) hα b₁ hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_spread_over_trait_specialisation : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | exact GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_spread₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem link_of_normal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  intro o Ω _ _ _ _ S ρ M U₀ EE FinalForm hU O _ _ _ _ _ _ x u hx hu

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x₀ : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x₀ ≫ FinalForm.u₀ = spMap S.R.val.toRingHom := FinalForm.u₀_gen x₀ hx₀
  let j : Sp Ω ⟶ Sp O := spMap (algebraMap O Ω)
  have hju : j ≫ spMap u = spMap S.R.val.toRingHom := (spMap_comp u (algebraMap O Ω)).symm.trans (congrArg spMap hu)

  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let A₀ := (Over.pullback M.pt).obj FinalForm.G
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x₀)
             (by rw [pullback.condition, Category.assoc, hx₀])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x₀ := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback A₀ FinalForm.G (x₀ ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx₀.symm hν₁.symm
  have gν : IsGrpPullback A₀ Q x₀ ν := FinalForm.cart.cancel gη hν₂
  have gψ : IsGrpPullback A₀ ρ.P.A (j ≫ spMap u) (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) :=
    (gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr (by rw [hju, hxu]) rfl

  let A := (Over.pullback (spMap u)).obj ρ.P.A
  have hA := isGrpPullback_pullback ρ.P.A (spMap u)
  have wA : (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ ρ.P.A.hom = (A₀.hom ≫ j) ≫ spMap u := by
    rw [gψ.1.w, Category.assoc]
  let φ₂ : A₀.left ⟶ A.left := hA.1.lift _ _ wA
  have eφ₂ : φ₂ ≫ pullback.fst ρ.P.A.hom (spMap u) = ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ := hA.1.lift_fst _ _ _
  have sφ₂ : φ₂ ≫ A.hom = A₀.hom ≫ j := hA.1.lift_snd _ _ _
  have hφ₂ : IsGrpPullback A₀ A j φ₂ := hA.cancel (gψ.congr rfl eφ₂.symm) sφ₂

  let GO := (Over.pullback x).obj FinalForm.G
  have hGO := isGrpPullback_pullback FinalForm.G x
  have gη' : IsGrpPullback A₀ FinalForm.G (j ≫ x) (pullback.fst FinalForm.G.hom M.pt) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm rfl
  have wG : pullback.fst FinalForm.G.hom M.pt ≫ FinalForm.G.hom = (A₀.hom ≫ j) ≫ x := by rw [gη'.1.w, Category.assoc]
  let φ₁ : A₀.left ⟶ GO.left := hGO.1.lift _ _ wG
  have eφ₁ : φ₁ ≫ pullback.fst FinalForm.G.hom x = pullback.fst FinalForm.G.hom M.pt := hGO.1.lift_fst _ _ _
  have hφ₁ : IsGrpPullback A₀ GO j φ₁ := hGO.cancel (gη'.congr rfl eφ₁.symm) (hGO.1.lift_snd _ _ _)
  have sA : IsSemiAbelian A := IsSemiAbelian.pullback _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ ρ.P.isAb)
  have sG : IsSemiAbelian GO := IsSemiAbelian.pullback _ _ FinalForm.semi
  obtain ⟨E, ⟨hE, hEφ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O) (GlobalTheory.IsGenericPointHom.fractionField O Ω) sA sG hφ₂ hφ₁
  haveI := hE
  let gm : A.left ⟶ FinalForm.G.left := E.hom.left ≫ pullback.fst FinalForm.G.hom x
  have hgm : IsGrpPullback A FinalForm.G x gm := ((isGrpPullback_of_iso E).comp hGO).congr (Category.id_comp _) rfl
  have key : φ₂ ≫ gm = ν ≫ FinalForm.φ := by
    show φ₂ ≫ E.hom.left ≫ pullback.fst FinalForm.G.hom x = _
    rw [← Category.assoc, hEφ, eφ₁, hν₁]
  have hgmw : gm ≫ FinalForm.G.hom = A.hom ≫ x := hgm.1.w
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ sA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ FinalForm.semi
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing O Ω
  haveI : IsSchemeTheoreticallyDominant φ₂ := .of_isPullback hφ₂.1.flip
  refine ⟨gm, hgm, ?_, ?_⟩
  · intro f Fm hf T' p p' h₁ h₂
    let fO := (Over.pullback (spMap u)).map f
    let fQ := (Over.pullback FinalForm.u₀).map f
    have hfO₁ : fO.left ≫ pullback.fst ρ.P.A.hom (spMap u) = pullback.fst ρ.P.A.hom (spMap u) ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfQ₁ : fQ.left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfO₂ : fO.left ≫ A.hom = A.hom := Over.w fO
    have hp' : p' = p ≫ fO.left := by
      apply pullback.hom_ext
      · rw [h₂, Category.assoc, hfO₁]
      · show p' ≫ A.hom = (p ≫ fO.left) ≫ A.hom
        rw [Category.assoc, hfO₂, h₁]
    have wk : (ν ≫ fQ.left) ≫ Q.hom = A₀.hom ≫ x₀ := by
      rw [Category.assoc, Over.w fQ, gν.1.w]
    let k : A₀.left ⟶ A₀.left := gν.1.lift _ _ wk
    have hk₁ : k ≫ ν = ν ≫ fQ.left := gν.1.lift_fst _ _ _
    have hk₂ : k ≫ A₀.hom = A₀.hom := gν.1.lift_snd _ _ _
    have hφk : φ₂ ≫ fO.left = k ≫ φ₂ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hfO₁, eφ₂, reassoc_of% eφ₂, reassoc_of% hk₁, hfQ₁]
      · show (φ₂ ≫ fO.left) ≫ A.hom = (k ≫ φ₂) ≫ A.hom
        rw [Category.assoc, hfO₂, Category.assoc, sφ₂, ← Category.assoc, hk₂]
    have main : fO.left ≫ gm = gm ≫ Fm.left := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant FinalForm.G.hom ?_ φ₂ ?_
      · rw [Category.assoc, hgmw, ← Category.assoc, hfO₂, Category.assoc, Over.w Fm, hgmw]
      · calc φ₂ ≫ fO.left ≫ gm = k ≫ φ₂ ≫ gm := by rw [← Category.assoc, hφk, Category.assoc]
          _ = (k ≫ ν) ≫ FinalForm.φ := by rw [key, Category.assoc]
          _ = ν ≫ FinalForm.φ ≫ Fm.left := by rw [hk₁, Category.assoc, hf]
          _ = φ₂ ≫ gm ≫ Fm.left := by rw [← Category.assoc, ← key, Category.assoc]
    rw [hp', Category.assoc, main]
  · intro a Wo h hs T' p x' h₁ h₂
    have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := by simpa [baseOver] using Over.w (ρ.pt a)
    let σ : Sp O ⟶ A.left := pullback.lift (spMap u ≫ (ρ.pt a).left) (𝟙 (Sp O))
      (by rw [Category.assoc, hpa]; simp)
    have hσ₁ : σ ≫ pullback.fst ρ.P.A.hom (spMap u) = spMap u ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
    have hσ₂ : σ ≫ A.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hp : p = (p ≫ A.hom) ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hσ₁, h₂, Category.assoc]
      · show p ≫ A.hom = ((p ≫ A.hom) ≫ σ) ≫ A.hom
        rw [Category.assoc, hσ₂, Category.comp_id]
    let O' := x ⁻¹ᵁ Wo
    have hpb := isPullback_morphismRestrict x Wo
    let q : T' ⟶ O'.toScheme := hpb.lift x' (p ≫ A.hom) (by rw [h₁, Category.assoc])
    have hq₁ : q ≫ (x ∣_ Wo) = x' := hpb.lift_fst _ _ _
    have hq₂ : q ≫ O'.ι = p ≫ A.hom := hpb.lift_snd _ _ _
    have hmain : O'.ι ≫ σ ≫ gm = (x ∣_ Wo) ≫ h := by
      by_cases hO : (O' : Set (Sp O)).Nonempty
      · have hr' : Set.range j ⊆ Set.range O'.ι := by
          rw [Scheme.Opens.range_ι, (GlobalTheory.IsGenericPointHom.fractionField O Ω).range_eq, Set.singleton_subset_iff]
          exact ((genericPoint_spec (Sp O)).mem_open_set_iff O'.isOpen).2 (by simpa using hO)
        let jO : Sp Ω ⟶ O'.toScheme := IsOpenImmersion.lift O'.ι j hr'
        have hjO : jO ≫ O'.ι = j := IsOpenImmersion.lift_fac _ _ _
        haveI : IsDominant (jO ≫ O'.ι) := by rw [hjO]; infer_instance
        haveI : IsDominant jO := IsDominant.of_comp_of_isOpenImmersion jO O'.ι
        refine ext_of_isDominant_of_isSeparated FinalForm.G.hom ?_ jO ?_
        · simp only [Category.assoc]
          rw [hgmw, ← Category.assoc σ, hσ₂, Category.id_comp, hs.1, morphismRestrict_ι]
        · let x'' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀ := pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt a).left) x₀
            (by rw [Category.assoc, hpa, hxu]; simp)
          have hx''₁ : x'' ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left :=
            pullback.lift_fst _ _ _
          have hx''₂ : x'' ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = x₀ := pullback.lift_snd _ _ _
          have hsec := hs.2 (jO ≫ (x ∣_ Wo)) x''
            (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hjO, hx])
            (by rw [FinalForm.cart.1.w, ← Category.assoc]; erw [hx''₂]; exact hx₀) hx''₁
          let e : Sp Ω ⟶ A₀.left := hφ₂.1.lift (j ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ₂, Category.comp_id, Category.id_comp])
          have he₁ : e ≫ φ₂ = j ≫ σ := hφ₂.1.lift_fst _ _ _
          have he₂ : e ≫ A₀.hom = 𝟙 _ := hφ₂.1.lift_snd _ _ _
          have heν : e ≫ ν = x'' := by
            apply pullback.hom_ext
            · rw [hx''₁, Category.assoc, ← eφ₂, ← Category.assoc, he₁, Category.assoc, hσ₁, ← Category.assoc, hju]
            · rw [hx''₂, Category.assoc]
              erw [hν₂]
              rw [← Category.assoc]
              erw [he₂]
              rw [Category.id_comp]
          calc jO ≫ O'.ι ≫ σ ≫ gm = (e ≫ φ₂) ≫ gm := by rw [← Category.assoc, hjO, he₁, Category.assoc]
            _ = (e ≫ ν) ≫ FinalForm.φ := by rw [Category.assoc, key, Category.assoc]
            _ = jO ≫ (x ∣_ Wo) ≫ h := by rw [heν, ← Category.assoc, hsec]
      · haveI : IsEmpty O'.toScheme := ⟨fun y => hO ⟨y.1, y.2⟩⟩
        exact isInitialOfIsEmpty.hom_ext _ _
    rw [hp, ← hq₂, ← hq₁, Category.assoc, Category.assoc, hmain, Category.assoc]

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_pullback_semiAbelian_over_normalDomain : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.link_of_normal | exact GlobalTheory.Poinc.Sep.Spz.link_of_normal | (intros; apply GlobalTheory.Poinc.Sep.Spz.link_of_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullField
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernNullField

theorem chernPart_compl_null : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ X _ p σ D _ U hU B φ ε
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have hA : MeasurableSet (ptsIn p σ U)ᶜ := (isOpen_ptsIn U).measurableSet.compl
  have glue_null {n : ℕ} {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
      (e : ι → OpenPartialHomeomorph Y (ReciprocityTheory.L2DbarEstimates.V n))
      (ρ : ι → Y → ENNReal) {F : Set Y} (hF : MeasurableSet F)
      (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
      GlobalTheory.ChartGlue.glueMeas e ρ F = 0 := by
    have hc : ∀ i, GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F = 0 := fun i => by
      rw [GlobalTheory.ChartGlue.chartMeas_apply (e i) (ρ i) hF]
      exact setLIntegral_measure_zero _ _ (h0 i)
    have hle : GlobalTheory.ChartGlue.glueMeas e ρ ≤ (GlobalTheory.ChartGlue.glueMeas e ρ).restrict Fᶜ := by
      refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
      rw [Measure.restrict_apply hB]
      calc GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) B ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
            measure_mono fun y hy => by
              by_cases h : y ∈ F
              · exact Or.inr h
              · exact Or.inl ⟨hy, h⟩
        _ ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) + GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F := measure_union_le _ _
        _ = GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
        _ ≤ GlobalTheory.ChartGlue.glueMeas e ρ (B ∩ Fᶜ) :=
            Measure.le_iff'.1 (le_iSup (fun i => GlobalTheory.ChartGlue.chartMeas (e i) (ρ i)) i) _
    have h := Measure.le_iff'.1 hle F
    rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
    exact nonpos_iff_eq_zero.1 h
  refine glue_null _ _ hA fun c => ?_
  rw [hcX]
  exact GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D _ U.isOpen.isClosed_compl (by simpa using hU) c

end GlobalTheory.ChernNullField

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_complement_dense_open_null_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  first | exact @GlobalTheory.ChernNullField.chernPart_compl_null | exact GlobalTheory.ChernNullField.chernPart_compl_null | (intros; apply GlobalTheory.ChernNullField.chernPart_compl_null <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BiKill

open GlobalTheory.CechPic

theorem lam_lam_diag {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (a b : T ⟶ A) :
    lam (lam (cls M hM) (𝟙 A) (𝟙 A)) a b = 2 • lam (cls M hM) a b := by
  have e : ∀ h : T ⟶ A, pull h.left (lam (cls M hM) (𝟙 A) (𝟙 A)) = lam (cls M hM) h h := fun h =>
    by rw [pull_lam, Category.comp_id]
  have hr : ∀ x y z : T ⟶ A, lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [lam_comm, lam_mul_left hM hΘ, lam_comm _ y, lam_comm _ z]
  change pull (a * b).left _ - pull a.left _ - pull b.left _ + pull (1 : T ⟶ A).left _ = _
  rw [e, e, e, e, lam_mul_left hM hΘ, hr, hr, lam_one_left, lam_comm _ b a, two_smul]
  abel

theorem kernel_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  intro A _ _ g hA hg P hP h1 h2 hsw hamp n hn T x hx
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsw
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ A hA M hM
  have hcube : (cubeLB A ![fst A A, snd A A] M).IsLB := LB.isLB_linComb hM _ _
  have hcP : cls P hP = lam (cls M hM) (fst A A) (snd A A) :=
    ((cls_eq_iff hP hcube).2 hPM).trans (cls_cube_two hM _ _ hcube)
  have hpullP : ∀ {Y : Over (Sp ℂ)} (a b : Y ⟶ A) (h : (P.pull (lift a b).left).IsLB),
      cls _ h = lam (cls M hM) a b := by
    intro Y a b h
    rw [cls_pull hP, hcP, pull_lam, lift_fst, lift_snd]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hcL : cls _ hL = lam (cls M hM) (𝟙 A) (𝟙 A) := hpullP _ _ hL
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨u, Hm, χ, -, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  obtain ⟨Q, ψ, ρ, N, hN, hψ, hρ, e₁, e₂, e₃⟩ :=
    GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL hAH
  have hlamM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hlamL : (abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).IsLB := LB.isLB_linComb hL _ _
  have hker : ∀ {Y : Over (Sp ℂ)} (y : Y ⟶ A),
      (∃ t : (P.pull (lift (snd A Y ≫ y) (fst A Y)).left).Gen, t.IsGen) →
      GlobalTheory.RealMult.HasGen ((abelian₂ A M).pull (lift (fst A Y) (snd A Y ≫ y)).left) ∧
      GlobalTheory.RealMult.HasGen ((abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).pull (lift (fst A Y) (snd A Y ≫ y)).left) := by
    intro Y y ht
    have h0 : lam (cls M hM) (fst A Y) (snd A Y ≫ y) = 0 := by
      rw [lam_comm, ← hpullP _ _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).2 ht
    refine ⟨(cls_eq_zero_iff (pull_isLB hlamM _)).1 ?_, (cls_eq_zero_iff (pull_isLB hlamL _)).1 ?_⟩
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hM]
      exact h0
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hL, hcL, lam_lam_diag hM hΘ, h0, smul_zero]
  have hk : x ^ (N * N) = 1 :=
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL Q ψ ρ N hψ hρ e₁ e₂ e₃ T x (hker x hx).2
  have key := GlobalTheory.torsion_point_comp_eq_one A hA M ((𝟙 A) ^ n) (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_)
    T x hk (hker x hx).1
  · rwa [MonObj.comp_pow, Category.comp_id] at key
  · rw [MonObj.comp_pow, Category.comp_id]
    refine hn y ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    rw [hpullP, lam_comm, ← GlobalTheory.RealMult.Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamM _)]
    exact (cls_eq_zero_iff _).2 hy

end GlobalTheory.BiKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  first | exact @GlobalTheory.BiKill.kernel_pow_eq_one | exact GlobalTheory.BiKill.kernel_pow_eq_one | (intros; apply GlobalTheory.BiKill.kernel_pow_eq_one <;> assumption)
end
end
