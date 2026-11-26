module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIntegrallyClosed
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRadialPrimitive

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRingUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

theorem CMRingUnmixed.proof : CMRingUnmixed.Statement := by
  intro A _ _ p hp
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  have heq : ringKrullDim (A ⧸ p) = ringKrullDim A :=
    le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
  refine ⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩
  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)
  have hq' : q.IsPrime := hq.1
  have h1 := Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt
  have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [ringKrullDim_quotient_eq_coheight, hdim] at h2
  rw [ringKrullDim_quotient_eq_coheight, hdim] at heq
  have e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞) := by exact_mod_cast heq
  have e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞) := by exact_mod_cast h2
  rw [e1] at h1
  have h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ) := by exact_mod_cast h1.trans e2
  have h4 : rs.length + 1 ≤ rs.length := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem withBot_enat_le_zero_of_add_one_le_one {x : WithBot ℕ∞} (h : x + 1 ≤ 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    have : e ≤ 0 := by
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h'
        exact_mod_cast (show k ≤ 0 by omega)
    exact_mod_cast this

theorem CurveNormalisationQuotientLength.proof (hF : CurveNormalisationFinite.Statement) :
    CurveNormalisationQuotientLength.Statement := by
  intro n I q hrad hdim
  set O := curveLocalRing I q
  set N := curveNormalisation I q
  set M := N ⧸ LinearMap.range (Algebra.linearMap O N)
  have hfin : Module.Finite O N := hF n I q hrad

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := N)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
    (fun x : N ↦ ((show ↥(integralClosure O (FractionRing O)) from x) : FractionRing O))
  have hmul : ∀ y : N, (b : O) • y ∈ LinearMap.range (Algebra.linearMap O N) := by
    intro y
    have hle : Submodule.span O (s : Set N) ≤
        (LinearMap.range (Algebra.linearMap O N)).comap ((b : O) • LinearMap.id) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨a, ha⟩ := hb x hx
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
    exact hle (hs ▸ Submodule.mem_top : y ∈ Submodule.span O (s : Set N))
  have hann : (b : O) ∈ Module.annihilator O M := by
    rw [Module.mem_annihilator]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H y => rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hmul y

  have hd := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (Module.annihilator O M))
    Ideal.Quotient.mk_surjective b.2 (Ideal.Quotient.eq_zero_iff_mem.2 hann)
  rw [hdim] at hd
  have : Ring.KrullDimLE 0 (O ⧸ Module.annihilator O M) :=
    Ring.krullDimLE_iff.2 (by exact_mod_cast withBot_enat_le_zero_of_add_one_le_one hd)
  have : IsArtinianRing (O ⧸ Module.annihilator O M) := isArtinianRing_iff_krullDimLE_zero.2 inferInstance
  let := Module.quotientAnnihilator (R := O) (M := M)
  have := (Module.isTorsionBySet_annihilator O M).isScalarTower (S := O)
  have : Module.Finite (O ⧸ Module.annihilator O M) M := Module.Finite.of_restrictScalars_finite O _ _
  have : IsArtinian O M := isArtinian_of_surjective_algebraMap (S := O) (R := O ⧸ Module.annihilator O M)
    (show Function.Surjective (algebraMap O (O ⧸ Module.annihilator O M)) from Ideal.Quotient.mk_surjective)
  exact Module.length_ne_top

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntSumOffHyperplane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ChartIntSumOffHyperplane.proof (hFB : FibreBound.Statement)
    (hCN : ChartChangeSheetNull.Statement) : ChartIntSumOffHyperplane.Statement := by
  intro n d J A u m f F φ hJ hdim hA hu hf hint

  have hnull := hCN n d J J A A u u Set.univ Set.univ id id hJ hdim hJ hdim hu hu hA hA isOpen_univ
    isOpen_univ (Set.subset_univ _) (Set.subset_univ _) differentiableOn_id differentiableOn_id
    (fun x hx => hx) (fun x hx => hx) (fun x _ => rfl) (fun x _ => rfl)
  have hae : ∀ᵐ y ∂(volume : Measure (Fin d → ℂ)),
      chartDens J A f φ y = ∑ b, chartDens J A (F b) φ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    have hfin : (ComplexSets.fibre J A y).Finite := (hFB n d J A hJ hdim hA y).2.1
    simp only [chartDens, sheetSum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · have hux : linEval u x ≠ 0 := by
        by_contra h0
        exact hy ⟨x, ⟨hx.1, hs, fun h => h.1 h0⟩, hx.2⟩
      rw [hf x hx.1 hux, Finset.sum_mul]
    · simp
  calc chartInt J A f φ = ∫ y, ∑ b, chartDens J A (F b) φ y := integral_congr_ae hae
    _ = ∑ b, chartInt J A (F b) φ := integral_finsetSum _ fun b _ => hint b

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHypersurfacePresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace HypersurfacePresentation

section Core

variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]


omit [CharZero E] [IsDomain A] in
theorem exists_clear_denominators (p : Polynomial E) :
    ∃ b : R, b ≠ 0 ∧ ∃ p' : Polynomial R,
      p'.map (algebraMap R E) = Polynomial.C (algebraMap R E b) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  exact ⟨b, nonZeroDivisors.ne_zero hb, _, by rw [h, Algebra.smul_def, Polynomial.algebraMap_apply]⟩


omit [IsDomain A] in
include E L in
theorem minpoly_separable_up_to [IsIntegrallyClosed R] {θ : A} (hθ : IsIntegral R θ) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ u v : Polynomial R,
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C δ := by
  have hθL : IsIntegral R (algebraMap A L θ) := hθ.map (IsScalarTower.toAlgHom R A L)
  have hm : minpoly R (algebraMap A L θ) = minpoly R θ :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom R A L) (IsFractionRing.injective A L) θ
  have hE : minpoly E (algebraMap A L θ) = (minpoly R θ).map (algebraMap R E) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' E hθL, hm]
  obtain ⟨a, b, hab⟩ := (minpoly.irreducible (hθL.tower_top (A := E))).separable
  rw [hE, Polynomial.derivative_map] at hab
  obtain ⟨ba, hba, a', ha'⟩ := exists_clear_denominators (R := R) a
  obtain ⟨bb, hbb, b', hb'⟩ := exists_clear_denominators (R := R) b
  refine ⟨ba * bb, mul_ne_zero hba hbb, Polynomial.C bb * a', Polynomial.C ba * b', ?_⟩
  apply Polynomial.map_injective (algebraMap R E) (IsFractionRing.injective R E)
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, ha', hb', map_mul]
  linear_combination (Polynomial.C (algebraMap R E ba) * Polynomial.C (algebraMap R E bb)) * hab


omit [CharZero E] [IsDomain A] in
theorem exists_mul_eq_aeval {θ : A} (hθ : IsIntegral R θ)
    (hgen : IntermediateField.adjoin E {algebraMap A L θ} = ⊤) (x : A) :
    ∃ b : R, b ≠ 0 ∧ ∃ q : Polynomial R, Polynomial.aeval θ q = algebraMap R A b * x := by
  have hθE : IsIntegral E (algebraMap A L θ) := (hθ.map (IsScalarTower.toAlgHom R A L)).tower_top
  have hx : algebraMap A L x ∈ (IntermediateField.adjoin E {algebraMap A L θ}).toSubalgebra := by
    rw [hgen]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθE.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨b, hb, q, hq⟩ := exists_clear_denominators (R := R) p
  refine ⟨b, hb, q, IsFractionRing.injective A L ?_⟩
  have h1 := congrArg (Polynomial.aeval (algebraMap A L θ)) hq
  rw [Polynomial.aeval_map_algebraMap, map_mul, Polynomial.aeval_C] at h1
  rw [← Polynomial.aeval_algebraMap_apply, h1, map_mul, ← IsScalarTower.algebraMap_apply R A L,
    IsScalarTower.algebraMap_apply R E L]
  exact congrArg _ hp


omit [IsDomain R] [IsDomain A] in
theorem exists_integral_primitive [FaithfulSMul R A] [Algebra.IsAlgebraic R A] {n : ℕ} (x : Fin n → A)
    (hgen : IntermediateField.adjoin E (Set.range fun j => algebraMap A L (x j)) = ⊤) :
    ∃ θ : A, IsIntegral R θ ∧ IntermediateField.adjoin E {algebraMap A L θ} = ⊤ := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  have hint : ∀ j, IsIntegral E (algebraMap A L (x j)) := fun j =>
    (((Algebra.IsAlgebraic.isAlgebraic (R := R) (x j)).algHom (IsScalarTower.toAlgHom R A L)).extendScalars
      (IsFractionRing.injective R E)).isIntegral
  have : FiniteDimensional E L := by
    have := IntermediateField.finiteDimensional_adjoin (K := E)
      (S := Set.range fun j => algebraMap A L (x j)) (by rintro _ ⟨j, rfl⟩; exact hint j)
    rw [hgen] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable E L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ E) q, map_ratCast, eq_ratCast]
  obtain ⟨D, hD, hDc⟩ := ComplexSets.GenericPrimitive.proof ℚ E L n (fun j => algebraMap A L (x j)) hgen
  obtain ⟨c, hc, hcD⟩ : ∃ c ∈ Set.pi Set.univ (fun _ : Fin n => Set.range (Int.cast : ℤ → ℚ)),
      MvPolynomial.eval c D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (MvPolynomial.funext_set _ (fun _ => Set.infinite_range_of_injective Int.cast_injective)
      fun c hc => by simpa using h c hc)
  choose z hz using fun j => hc j (Set.mem_univ j)
  set θ₁ : A := ∑ j, z j • x j with hθ₁def
  have hθ₁ : IntermediateField.adjoin E {algebraMap A L θ₁} = ⊤ := by
    have h := hDc c hcD
    have he : ∑ j, c j • algebraMap A L (x j) = algebraMap A L θ₁ := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hθ₁def, map_sum, map_zsmul, ← hz, Int.cast_smul_eq_zsmul]
    rwa [he] at h
  obtain ⟨a, ha, hai⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) θ₁).exists_integral_multiple
  refine ⟨a • θ₁, hai, eq_top_iff.2 (hθ₁ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)⟩
  have ha' : algebraMap E L (algebraMap R E a) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L]
    intro h0
    exact ha ((FaithfulSMul.algebraMap_injective R A).eq_iff' (map_zero _) |>.1
      ((IsFractionRing.injective A L).eq_iff' (map_zero _) |>.1 h0))
  have heq : algebraMap A L θ₁ = (algebraMap E L (algebraMap R E a))⁻¹ * algebraMap A L (a • θ₁) := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L,
      IsScalarTower.algebraMap_apply R E L, inv_mul_cancel_left₀ ha']
  rw [heq]
  exact mul_mem (IntermediateField.inv_mem _ (IntermediateField.algebraMap_mem _ _))
    (IntermediateField.mem_adjoin_simple_self E _)

end Core

section Generic

theorem exists_separable_presentation {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Algebra.IsAlgebraic R A]
    {n : ℕ} (x : Fin n → A) (hx : Algebra.adjoin R (Set.range x) = ⊤) {ι : Type} [Fintype ι] (z : ι → A) :
    ∃ θ : A, (minpoly R θ).Monic ∧ (∀ H : Polynomial R, Polynomial.aeval θ H = 0 ↔ minpoly R θ ∣ H) ∧
      ∃ D : R, D ≠ 0 ∧ ∃ (q : ι → Polynomial R) (u v : Polynomial R),
      u * minpoly R θ + v * Polynomial.derivative (minpoly R θ) = Polynomial.C D ∧
      ∀ i, Polynomial.aeval θ (q i) = algebraMap R A D * z i := by
  classical
  have : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp (FaithfulSMul.algebraMap_injective R A))
  let : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra _ _
  have : CharZero (FractionRing R) :=
    charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hgen : IntermediateField.adjoin (FractionRing R)
      (Set.range fun j => algebraMap A (FractionRing A) (x j)) = ⊤ := by
    set F := IntermediateField.adjoin (FractionRing R) (Set.range fun j => algebraMap A (FractionRing A) (x j))
    have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈ F := by
      intro a
      have ha : a ∈ Algebra.adjoin R (Set.range x) := hx ▸ Algebra.mem_top
      induction ha using Algebra.adjoin_induction with
      | mem a h =>
        obtain ⟨j, rfl⟩ := h
        exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
      | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A)]
        exact F.algebraMap_mem _
      | add a b _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | mul a b _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective A w
    exact div_mem (hA a) (hA b)
  obtain ⟨θ, hθ, hθgen⟩ :=
    exists_integral_primitive (R := R) (E := FractionRing R) (L := FractionRing A) x hgen
  obtain ⟨δ, hδ, u, v, huv⟩ := minpoly_separable_up_to (E := FractionRing R) (L := FractionRing A) hθ
  choose b hb q hq using fun i =>
    exists_mul_eq_aeval (E := FractionRing R) (L := FractionRing A) hθ hθgen (z i)
  have : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective R A)
  refine ⟨θ, minpoly.monic hθ, minpoly.isIntegrallyClosed_dvd_iff hθ, δ * ∏ i, b i, mul_ne_zero hδ (Finset.prod_ne_zero_iff.2 fun i _ => hb i),
    fun i => Polynomial.C (δ * ∏ j ∈ Finset.univ.erase i, b j) * q i,
    Polynomial.C (∏ i, b i) * u, Polynomial.C (∏ i, b i) * v, ?_, fun i => ?_⟩
  · rw [Polynomial.C_mul]
    linear_combination Polynomial.C (∏ i, b i) * huv
  · rw [map_mul, Polynomial.aeval_C, hq i, ← mul_assoc, ← map_mul, mul_assoc δ,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

theorem exists_transcendenceBasis_fin {S A : Type} [CommRing S] [CommRing A] [IsDomain A] [Algebra S A]
    [FaithfulSMul S A] {ι : Type} [Finite ι] (x : ι → A) (hx : Algebra.adjoin S (Set.range x) = ⊤) :
    ∃ (d : ℕ) (y : Fin d → A), IsTranscendenceBasis S y := by
  have : Algebra.IsAlgebraic (Algebra.adjoin S (Set.range x)) A := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin S (Set.range x) := hx ▸ Algebra.mem_top
    exact isAlgebraic_algebraMap (R := Algebra.adjoin S (Set.range x)) (A := A) ⟨a, ha⟩⟩
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := S) (Set.range x)
  have : Finite t := ((Set.finite_range x).subset ht).to_subtype
  exact ⟨_, _, hb.comp_equiv (Finite.equivFin t).symm⟩

theorem isAlgebraic_aeval_of_isTranscendenceBasis {S A : Type} [CommRing S] [Nontrivial S] [CommRing A]
    [Algebra S A] {d : ℕ} {y : Fin d → A} (hb : IsTranscendenceBasis S y) :
    letI := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
    Algebra.IsAlgebraic (MvPolynomial (Fin d) S) A := by
  let _ : Algebra (MvPolynomial (Fin d) S) A := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
  have := hb.isAlgebraic
  have h : (algebraMap (MvPolynomial (Fin d) S) A).comp (hb.1.aevalEquiv.symm : _ →+* _) =
      (RingHom.id A).comp (algebraMap (Algebra.adjoin S (Set.range y)) A) := RingHom.ext fun z => by
    show MvPolynomial.aeval y (hb.1.aevalEquiv.symm z) = (z : A)
    rw [← hb.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
    rfl
  exact ⟨fun a => (isAlgebraic_ringHom_iff_of_comp_eq hb.1.aevalEquiv.symm (RingHom.id A)
    Function.injective_id h).2 (Algebra.IsAlgebraic.isAlgebraic a)⟩

end Generic

section Main

variable {σ ι : Type} [Finite σ] [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) [K.IsPrime]


omit [Finite σ] in
set_option synthInstance.maxHeartbeats 400000 in
theorem hypersurfacePresentation_of (hKS : ∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) :
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K := by
  classical
  have := Fintype.ofFinite ι
  let 𝔸 := (MvPolynomial ι (MvPolynomial σ ℂ)) ⧸ K
  have hmkC : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial σ ℂ) 𝔸 s := fun s => rfl
  have hSinj : Function.Injective (algebraMap (MvPolynomial σ ℂ) 𝔸) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    rw [← hmkC, Ideal.Quotient.eq_zero_iff_mem] at hs
    exact hKS s hs
  have : FaithfulSMul (MvPolynomial σ ℂ) 𝔸 := (faithfulSMul_iff_algebraMap_injective _ _).2 hSinj
  let x : ι → 𝔸 := fun i => Ideal.Quotient.mk K (X i)
  have hadj : Algebra.adjoin (MvPolynomial σ ℂ) (Set.range x) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkC]; exact Subalgebra.algebraMap_mem _ s
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  obtain ⟨d, yA, hbd⟩ := exists_transcendenceBasis_fin x hadj

  let : Algebra (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 := (MvPolynomial.aeval yA).toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r = MvPolynomial.aeval yA r :=
    fun _ => rfl
  have hRinj : Function.Injective (algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸) := fun a b h =>
    algebraicIndependent_iff_injective_aeval.1 hbd.1 (by rwa [hmap, hmap] at h)
  have : FaithfulSMul (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hRinj
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 :=
    isAlgebraic_aeval_of_isTranscendenceBasis hbd
  have hmkCR : ∀ s, Ideal.Quotient.mk K (C s) = algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 (C s) :=
    fun s => by
      rw [hmkC]
      show _ = MvPolynomial.aeval yA (C s)
      rw [MvPolynomial.aeval_C]
  let eι := Finite.equivFin ι
  have hadjR : Algebra.adjoin (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (Set.range fun j => x (eι.symm j)) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    clear ‹a ∈ ⊤›
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C s => rw [hmkCR]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨eι i, by simp [x]⟩)
  obtain ⟨θA, hmon, hker, D, hD, q, u, v, huv, hq⟩ :=
    exists_separable_presentation (R := MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (fun j => x (eι.symm j)) hadjR x

  choose y hy using fun j => Ideal.Quotient.mk_surjective (yA j)
  obtain ⟨θ, hθmk⟩ := Ideal.Quotient.mk_surjective θA
  have hcompA : (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) K).comp (aeval y) = MvPolynomial.aeval yA :=
    MvPolynomial.algHom_ext fun j => by
      rw [AlgHom.comp_apply, aeval_X, aeval_X, Ideal.Quotient.mkₐ_eq_mk, hy]
  have hcomp : ∀ r, Ideal.Quotient.mk K (aeval y r) =
      algebraMap (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) 𝔸 r := fun r => by
    rw [hmap, ← hcompA, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have heval : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Ideal.Quotient.mk K (Polynomial.eval₂ (aeval y).toRingHom θ H) = Polynomial.aeval θA H := by
    intro H
    rw [Polynomial.hom_eval₂, hθmk, Polynomial.aeval_def]
    congr 1
    exact RingHom.ext hcomp
  refine ⟨d, y, θ, minpoly (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) θA, D, q, u, v, hmon, hD, huv,
    fun H => ?_, fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, heval]
    exact hker H
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, heval, hcomp, hq i, sub_eq_zero]

end Main

end HypersurfacePresentation

theorem HypersurfacePresentation.proof : HypersurfacePresentation.Statement := by
  intro σ _ ι _ K hK hKS
  exact HypersurfacePresentation.hypersurfacePresentation_of K hKS

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadicalPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem fibreMap_eval₂_aeval {σ ι : Type*} {d : ℕ} (t : σ → ℂ)
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) :
    MvPolynomial.map (eval t) (Polynomial.eval₂ (aeval y).toRingHom θ H) =
      Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) (H.map (MvPolynomial.map (eval t))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro s
    simp [MvPolynomial.algebraMap_eq]
  · intro j
    simp

theorem exists_pow_mul_sub_eval₂_mem {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K)
    (p : MvPolynomial ι (MvPolynomial σ ℂ)) :
    ∃ (e : ℕ) (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K := by
  induction p using MvPolynomial.induction_on with
  | C s =>
    refine ⟨0, Polynomial.C (C s), ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨e₁, H₁, h₁⟩ := h₁
    obtain ⟨e₂, H₂, h₂⟩ := h₂
    refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂, ?_⟩
    have e : aeval y D ^ (e₁ + e₂) * (p₁ + p₂) -
        Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂) =
        aeval y D ^ e₂ * (aeval y D ^ e₁ * p₁ - Polynomial.eval₂ (aeval y).toRingHom θ H₁) +
          aeval y D ^ e₁ * (aeval y D ^ e₂ * p₂ - Polynomial.eval₂ (aeval y).toRingHom θ H₂) := by
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, map_pow,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e]
    exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
  | mul_X p i h =>
    obtain ⟨e, H, h⟩ := h
    refine ⟨e + 1, H * q i, ?_⟩
    have e' : aeval y D ^ (e + 1) * (p * X i) - Polynomial.eval₂ (aeval y).toRingHom θ (H * q i) =
        (aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H) * (aeval y D * X i) +
          Polynomial.eval₂ (aeval y).toRingHom θ H *
            (aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i)) := by
      rw [Polynomial.eval₂_mul]
      ring
    rw [e']
    exact K.add_mem (K.mul_mem_right _ h) (K.mul_mem_left _ (hq i))

theorem exists_of_mem_ker_fibreMap {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (w : MvPolynomial ι (MvPolynomial σ ℂ))
    (hw : w ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ)) :
    ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      W.map (MvPolynomial.map (eval t)) = 0 ∧
        aeval y D ^ e * w - Polynomial.eval₂ (aeval y).toRingHom θ W ∈ K := by
  set δ : MvPolynomial ι (MvPolynomial σ ℂ) := aeval y D
  set ev : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) → MvPolynomial ι (MvPolynomial σ ℂ) :=
    Polynomial.eval₂ (aeval y).toRingHom θ
  let J : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)) :=
    { carrier := {w | ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
        W.map (MvPolynomial.map (eval t)) = 0 ∧ δ ^ e * w - ev W ∈ K}
      add_mem' := by
        rintro a b ⟨e₁, W₁, hW₁, h₁⟩ ⟨e₂, W₂, hW₂, h₂⟩
        refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂, ?_, ?_⟩
        · simp [Polynomial.map_add (f := _), Polynomial.map_mul, hW₁, hW₂]
        · have e : δ ^ (e₁ + e₂) * (a + b) - ev (Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂) =
              δ ^ e₂ * (δ ^ e₁ * a - ev W₁) + δ ^ e₁ * (δ ^ e₂ * b - ev W₂) := by
            simp only [ev, δ, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
              map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
            ring
          rw [e]
          exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
      zero_mem' := ⟨0, 0, by simp, by simp [ev]⟩
      smul_mem' := by
        rintro r a ⟨e, W, hW, h⟩
        obtain ⟨e', H, hH⟩ := exists_pow_mul_sub_eval₂_mem K y θ D q hq r
        refine ⟨e' + e, H * W, by simp [Polynomial.map_mul, hW], ?_⟩
        have e'' : δ ^ (e' + e) * (r • a) - ev (H * W) =
            δ ^ e * a * (δ ^ e' * r - ev H) + ev H * (δ ^ e * a - ev W) := by
          simp only [ev, Polynomial.eval₂_mul, smul_eq_mul]
          ring
        rw [e'']
        exact K.add_mem (K.mul_mem_left _ hH) (K.mul_mem_left _ h) }
  have hle : RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤ J := by
    rw [ker_fibreMap, Ideal.map_le_iff_le_comap]
    intro c hc
    refine ⟨0, Polynomial.C (C c), ?_, ?_⟩
    · rw [RingHom.mem_ker] at hc
      simp [hc]
    · simp [ev, MvPolynomial.algebraMap_eq]
  exact hle hw

theorem dvd_of_eval₂_mem_fibre {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
    (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hker : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H)
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (h : Polynomial (MvPolynomial (Fin d) ℂ))
    (hh : Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) h ∈ K.map (MvPolynomial.map (eval t))) :
    ∃ e : ℕ, m.map (MvPolynomial.map (eval t)) ∣
      Polynomial.C (MvPolynomial.map (eval t) D) ^ e * h := by
  have hs : Function.Surjective (eval t : MvPolynomial σ ℂ →+* ℂ) := fun c => ⟨C c, eval_C c⟩
  obtain ⟨H, rfl⟩ := Polynomial.map_surjective _ (MvPolynomial.map_surjective _ hs) h
  rw [← fibreMap_eval₂_aeval] at hh
  obtain ⟨κ, hκ, hκH⟩ := (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective _ hs)).1 hh
  have hw : Polynomial.eval₂ (aeval y).toRingHom θ H - κ ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) := by
    rw [RingHom.mem_ker, map_sub, hκH, sub_self]
  obtain ⟨e, W, hW, hWK⟩ := exists_of_mem_ker_fibreMap K y θ D q hq t _ hw
  refine ⟨e, ?_⟩
  have hmem : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) ∈ K := by
    have e' : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) =
        (aeval y D ^ e * (Polynomial.eval₂ (aeval y).toRingHom θ H - κ) -
          Polynomial.eval₂ (aeval y).toRingHom θ W) + aeval y D ^ e * κ := by
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e']
    exact K.add_mem hWK (K.mul_mem_left _ hκ)
  have hd := Polynomial.map_dvd (MvPolynomial.map (eval t)) ((hker _).1 hmem)
  simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, hW] using hd

theorem Monic.dvd_of_dvd_C_pow_mul_pow {R : Type*} [CommRing R] [IsDomain R] {m u v h : Polynomial R} {c : R}
    (hm : m.Monic) (hc : c ≠ 0) (huv : u * m + v * Polynomial.derivative m = Polynomial.C c) {e N : ℕ}
    (hN : N ≠ 0) (hd : m ∣ Polynomial.C c ^ e * h ^ N) : m ∣ h := by
  have hf : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hfc : algebraMap R (FractionRing R) c ≠ 0 :=
    (map_ne_zero_iff _ hf).2 hc
  have hsep : (m.map (algebraMap R (FractionRing R))).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * u.map (algebraMap R (FractionRing R)),
      Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * v.map (algebraMap R (FractionRing R)), ?_⟩
    have h1 := congrArg (Polynomial.map (algebraMap R (FractionRing R))) huv
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hfc, Polynomial.C_1]
  have hd' : m.map (algebraMap R (FractionRing R)) ∣
      Polynomial.C (algebraMap R (FractionRing R) c) ^ e * (h.map (algebraMap R (FractionRing R))) ^ N := by
    have := Polynomial.map_dvd (algebraMap R (FractionRing R)) hd
    rwa [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_C] at this
  have hu : IsUnit (Polynomial.C (algebraMap R (FractionRing R) c) ^ e) :=
    (Polynomial.isUnit_C.2 (Ne.isUnit hfc)).pow e
  have h2 : m.map (algebraMap R (FractionRing R)) ∣ h.map (algebraMap R (FractionRing R)) :=
    (hsep.squarefree.dvd_pow_iff_dvd hN).1 ((hu.dvd_mul_left).1 hd')
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (hm.map _), ← Polynomial.map_modByMonic _ hm] at h2
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hm]
  exact Polynomial.map_injective _ hf (by rw [h2, Polynomial.map_zero])

theorem mem_map_of_mul_mem_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (K : Ideal R) (hK : K.IsPrime) (b : R) (hb : b ∉ K)
    (h : (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (K ⊔ Ideal.span {b}))
    (g : R') (hg : φ b * g ∈ K.map φ) : g ∈ K.map φ := by
  obtain ⟨a, rfl⟩ := hφ g
  rw [← map_mul] at hg
  obtain ⟨κ, hκ, hκa⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hg
  have hμ : b * a - κ ∈ (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)))
      (Ideal.mem_sup_left hκ), RingHom.mem_ker.2 (by rw [map_sub, hκa, sub_self])⟩
  have h2 := h hμ
  rw [Ideal.mul_sup] at h2
  obtain ⟨κ', hκ', w, hw, hsum⟩ := Submodule.mem_sup.1 h2
  obtain ⟨ν, hν, hνw⟩ := (Ideal.mem_mul_span_singleton (I := RingHom.ker φ)).1 hw
  have hκ'K : κ' ∈ K := (Ideal.mul_le_inf hκ').2
  have hb' : b * (a - ν) ∈ K := by
    have e : b * (a - ν) = κ + κ' := by linear_combination -hsum - hνw
    rw [e]
    exact K.add_mem hκ hκ'K
  have haν : a - ν ∈ K := (hK.mem_or_mem hb').resolve_left hb
  have : φ a = φ (a - ν) := by rw [map_sub, RingHom.mem_ker.1 hν, sub_zero]
  rw [this]
  exact Ideal.mem_map_of_mem φ haν

theorem GenericFibreRadicalPrime.proof (hT : GenericFibreTor.Statement)
    (hP : HypersurfacePresentation.Statement) : GenericFibreRadicalPrime.Statement := by
  intro σ _ ι _ K hK
  classical
  have hs : ∀ t : σ → ℂ, Function.Surjective (eval t : MvPolynomial σ ℂ →+* ℂ) := fun t c => ⟨C c, eval_C c⟩
  by_cases h0 : ∃ s : MvPolynomial σ ℂ, C s ∈ K ∧ s ≠ 0
  · obtain ⟨s, hsK, hs0⟩ := h0
    refine ⟨s, hs0, fun t ht => ?_⟩
    have hu : IsUnit (MvPolynomial.map (eval t) (C s : MvPolynomial ι (MvPolynomial σ ℂ))) := by
      rw [MvPolynomial.map_C]
      exact (Ne.isUnit ht).map C
    rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsK) hu]
    exact fun _ _ => Submodule.mem_top
  push Not at h0
  obtain ⟨d, y, θ, m, D, q, u, v, hm, hD, huv, hker, hq⟩ := hP σ ι K hK h0
  have hb : aeval y D ∉ K := by
    intro hb
    have hdvd : m ∣ Polynomial.C D := (hker _).1 (by simpa using hb)
    have hdeg : m.natDegree = 0 := by
      have := Polynomial.natDegree_le_of_dvd hdvd (by simpa using hD)
      rw [Polynomial.natDegree_C] at this
      omega
    have h1 : m = 1 := hm.natDegree_eq_zero.1 hdeg
    exact hK.ne_top ((Ideal.eq_top_iff_one K).2 (by simpa using (hker 1).2 (by rw [h1])))
  obtain ⟨F₁, hF₁, hF₁t⟩ := hT σ ι (K ⊔ Ideal.span {aeval y D})
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hD
  refine ⟨F₁ * D.coeff μ, mul_ne_zero hF₁ hμ, fun t ht => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at ht
  obtain ⟨ht₁, ht₂⟩ := ht
  set φ : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ := MvPolynomial.map (eval t)
  set ψ : MvPolynomial (Fin d) (MvPolynomial σ ℂ) →+* MvPolynomial (Fin d) ℂ := MvPolynomial.map (eval t)
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ (hs t)
  have hψD : ψ D ≠ 0 := by
    intro h0'
    apply ht₂
    have := congrArg (AddMonoidAlgebra.coeff · μ) h0'
    simpa [ψ, MvPolynomial.coeff_map] using this

  have hnzd : ∀ (k : ℕ) (g : MvPolynomial ι ℂ), φ (aeval y D) ^ k * g ∈ K.map φ → g ∈ K.map φ := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih =>
      intro g hg
      refine ih g (mem_map_of_mul_mem_map φ hφ K hK _ hb (hF₁t t ht₁) _ ?_)
      rw [pow_succ] at hg
      simpa [mul_assoc, mul_comm, mul_left_comm] using hg
  intro g ⟨N, hgN⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [(Ideal.eq_top_iff_one (K.map φ)).2 (by simpa using hgN)]
    exact Submodule.mem_top
  obtain ⟨G, rfl⟩ := hφ g
  obtain ⟨e, H, hH⟩ := exists_pow_mul_sub_eval₂_mem K y θ D q hq G
  set evt := Polynomial.eval₂ (aeval (R := ℂ) fun j => φ (y j)).toRingHom (φ θ)
  have h1 : φ (aeval y D) ^ e * φ G - evt (H.map ψ) ∈ K.map φ := by
    have := Ideal.mem_map_of_mem φ hH
    rwa [map_sub, map_mul, map_pow, fibreMap_eval₂_aeval] at this
  have h2 : evt (H.map ψ ^ N) ∈ K.map φ := by
    have hdv := sub_dvd_pow_sub_pow (φ (aeval y D) ^ e * φ G) (evt (H.map ψ)) N
    have h3 : (φ (aeval y D) ^ e * φ G) ^ N - evt (H.map ψ) ^ N ∈ K.map φ :=
      Ideal.mem_of_dvd _ hdv h1
    have h4 : (φ (aeval y D) ^ e * φ G) ^ N ∈ K.map φ := by
      rw [mul_pow]
      exact Ideal.mul_mem_left _ _ hgN
    have h5 := Ideal.sub_mem _ h4 h3
    rw [sub_sub_cancel] at h5
    simpa [evt, Polynomial.eval₂_pow] using h5
  obtain ⟨e', he'⟩ := dvd_of_eval₂_mem_fibre K y θ m D q hker hq t _ h2
  have huv' : u.map ψ * m.map ψ + v.map ψ * Polynomial.derivative (m.map ψ) = Polynomial.C (ψ D) := by
    have := congrArg (Polynomial.map ψ) huv
    simpa [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.derivative_map] using this
  have hmh : m.map ψ ∣ H.map ψ :=
    Monic.dvd_of_dvd_C_pow_mul_pow (hm.map ψ) hψD huv' hN.ne' he'
  obtain ⟨s, hs'⟩ := hmh
  have hmK : evt (m.map ψ) ∈ K.map φ := by
    have := Ideal.mem_map_of_mem φ ((hker m).2 dvd_rfl)
    rwa [fibreMap_eval₂_aeval] at this
  have h6 : evt (H.map ψ) ∈ K.map φ := by
    rw [hs']
    simp only [evt, Polynomial.eval₂_mul]
    exact Ideal.mul_mem_right _ _ hmK
  exact hnzd e _ (by simpa using Ideal.add_mem _ h1 h6)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAuslanderBuchsbaumDepthLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence

universe u

namespace AuslanderBuchsbaumDepthLower

variable {R : Type u} [CommRing R] [IsLocalRing R]

noncomputable abbrev residueModule (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))

instance (R : Type u) [CommRing R] [IsLocalRing R] : Module.Finite R (residueModule R) :=
  Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm

theorem support_residueModule :
    Module.support R (residueModule R) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

theorem maximalIdeal_smul_top_lt_top (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
  have H : Module.annihilator R M ≠ ⊤ := fun h =>
    not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ H]

theorem subsingleton_ext_of_flat [IsNoetherianRing R] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrs : IsWeaklyRegular R rs) (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Flat R P] :
    ∀ i < rs.length, Subsingleton (Ext (residueModule R) P i) := by
  intro i hi
  rcases subsingleton_or_nontrivial P with hP | hP
  · have hZ : IsZero P := ModuleCat.isZero_of_subsingleton P
    have : Injective P := hZ.injective
    cases i with
    | zero => exact Ext.addEquiv₀.subsingleton_congr.mpr ⟨fun a b => hZ.eq_of_tgt a b⟩
    | succ j => exact Ext.subsingleton_of_injective _ _ j
  · have hreg : IsWeaklyRegular P rs :=
      (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R P) rs).mp
        (hrs.isWeaklyRegular_lTensor (M₂ := P))
    have hreg' : IsRegular P rs :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hreg
    exact ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) (residueModule R)
      support_residueModule.le P (maximalIdeal_smul_top_lt_top P) rs hmem hreg' i hi

theorem subsingleton_ext_of_hasProjectiveDimensionLE [IsNoetherianRing R] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsWeaklyRegular R rs) (ℓ : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M ℓ →
      ∀ i, i + ℓ < rs.length → Subsingleton (Ext (residueModule R) M i) := by
  induction ℓ with
  | zero =>
    intro M _ hM i hi
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
    exact subsingleton_ext_of_flat rs hmem hrs M i (by omega)
  | succ ℓ ih =>
    intro M _ hM i hi
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have h₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ (ℓ + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (ℓ + 1) (by omega)
    have hK : HasProjectiveDimensionLE f.shortComplexKer.X₁ ℓ :=
      hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) h₂ hM
    have e₂ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₂ i) :=
      subsingleton_ext_of_flat rs hmem hrs _ i (by omega)
    have e₁ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₁ (i + 1)) :=
      ih _ hK (i + 1) (by omega)
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' (residueModule R) hS) i (i + 1) rfl)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₂).eq_zero_of_src _)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₁).eq_zero_of_tgt _)

end AuslanderBuchsbaumDepthLower

theorem AuslanderBuchsbaumDepthLower.proof : AuslanderBuchsbaumDepthLower.Statement.{u} := by
  intro R _ _ _ M _ _ _ _ ℓ rs hpd hmem hrs
  obtain ⟨ms, hlen, hms, hreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) (rs.length - ℓ) (ModuleCat.of R M)
    (AuslanderBuchsbaumDepthLower.maximalIdeal_smul_top_lt_top M)
    (AuslanderBuchsbaumDepthLower.residueModule R)
    AuslanderBuchsbaumDepthLower.support_residueModule
    (fun i hi => AuslanderBuchsbaumDepthLower.subsingleton_ext_of_hasProjectiveDimensionLE rs hmem hrs ℓ
      (ModuleCat.of R M) hpd i (by omega))
  exact ⟨ms, hms, hreg.toIsWeaklyRegular, hlen⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularSequenceLengthLeDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

universe u

theorem RegularSequenceLengthLeDim.proof : RegularSequenceLengthLeDim.Statement.{u} := by
  suffices key : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
      rs.length = n → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim R from
    fun R _ _ _ rs hmem hreg => key _ R rs rfl hmem hreg
  intro n
  induction n with
  | zero =>
    intro R _ _ _ rs hlen _ _
    rw [hlen, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro R _ _ _ rs hlen hmem hreg
    obtain _ | ⟨r, rs⟩ := rs
    · simp at hlen
    rw [List.length_cons, Nat.succ_inj] at hlen
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hr, htail⟩ := hreg
    have hrm : r ∈ maximalIdeal R := hmem r (List.mem_cons_self ..)
    set S := R ⧸ Ideal.span {r}
    have hne : Ideal.span {r} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp hrm
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hdim : ringKrullDim S + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hr hrm
    have heq : (r • ⊤ : Submodule R R) = Ideal.span {r} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hS : IsWeaklyRegular S rs :=
      (Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs |>.mp htail
    have hS' : IsWeaklyRegular S (rs.map (algebraMap R S)) :=
      (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hS
    have hmem' : ∀ s ∈ rs.map (algebraMap R S), s ∈ maximalIdeal S := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      refine (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp (hmem t (List.mem_cons_of_mem _ ht)) ?_
      exact isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {r})) t hu
    have h := ih S _ (by rw [List.length_map, hlen]) hmem' hS'
    rw [List.length_map] at h
    rw [← hdim, List.length_cons, Nat.cast_succ]
    exact add_le_add h le_rfl

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric : GroundTheory.Heights₂.Heights.FrameGraphGeneric.Statement :=
  @GroundTheory.Heights₂.Heights.FrameGraphGeneric.proof GroundTheory.Heights₂.Heights.AutoClose.FrameJacobianGeneric GroundTheory.Heights₂.Heights.FrameImplicitGraph.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.OrdDeterminesPlace : GroundTheory.Heights₂.Heights.OrdDeterminesPlace.Statement :=
  @GroundTheory.Heights₂.Heights.OrdDeterminesPlace.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.parametrisation_sheets_connected_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.proof GroundTheory.Heights₂.Heights.AutoClose.sheet_product_analytic_holds GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LengthLocalizedQuotient.{u} : GroundTheory.Heights₂.Heights.LengthLocalizedQuotient.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.LengthLocalizedQuotient.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.LengthCutLocalizedModule

theorem GroundTheory.Heights₂.Heights.AutoClose.CMProjDimCriterion : GroundTheory.Heights₂.Heights.CMProjDimCriterion.Statement :=
  @GroundTheory.Heights₂.Heights.CMProjDimCriterion.proof GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower.proof GroundTheory.Heights₂.Heights.AuslanderBuchsbaumProjDimUpper.proof GroundTheory.Heights₂.Heights.RegularSequenceLengthLeDim.proof GroundTheory.Heights₂.Heights.AutoClose.CMHeightAddDim

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalPrime : GroundTheory.Heights₂.Heights.GenericFibreRadicalPrime.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadicalPrime.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreTor GroundTheory.Heights₂.Heights.HypersurfacePresentation.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationQuotientLength : GroundTheory.Heights₂.Heights.CurveNormalisationQuotientLength.Statement :=
  @GroundTheory.Heights₂.Heights.CurveNormalisationQuotientLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.invariance_of_domain_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.proof GroundTheory.Heights₂.Heights.AutoClose.brouwer_fixed_point_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_inverse_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_jacobian_ne_zero_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane : GroundTheory.Heights₂.Heights.ChartIntSumOffHyperplane.Statement :=
  @GroundTheory.Heights₂.Heights.ChartIntSumOffHyperplane.proof GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof GroundTheory.Heights₂.Heights.AutoClose.ChartChangeSheetNull

theorem GroundTheory.Heights₂.Heights.AutoClose.CMQuotientUnmixed : GroundTheory.Heights₂.Heights.CMQuotientUnmixed.Statement :=
  @GroundTheory.Heights₂.Heights.CMQuotientUnmixed.proof GroundTheory.Heights₂.Heights.AutoClose.CMParameterQuotient GroundTheory.Heights₂.Heights.CMRingUnmixed.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint : GroundTheory.Heights₂.Heights.NormalCurveRegularPoint.Statement :=
  @GroundTheory.Heights₂.Heights.NormalCurveRegularPoint.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveJacobian

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserGradientIndependent : GroundTheory.Heights₂.Heights.UniformiserGradientIndependent.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserGradientIndependent.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveJacobian GroundTheory.Heights₂.Heights.NormalCurvePointDVR.proof
