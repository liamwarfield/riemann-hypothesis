module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNormalisationModelLocalizationX

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaneSliceMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveRegularPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveRegularPoint.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ w ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ V = g '' O

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise

universe u

theorem mem_minimalPrimes_of_mem_associatedPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hpm, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg
  rw [← hpm] at hD
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  by_cases hqp' : q = p
  · exact hqp' ▸ hq
  exfalso
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')
  have : q.IsPrime := hq.1.1
  have hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a}) := by
    have : Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})
  rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
  have hle : q ⊔ Ideal.span {a} ≤ p := sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)
  have h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hdim] at h2 h3
  have h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞) := le_antisymm h3 hD
  have h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞) :=
    ((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2
  rw [h4] at h5
  norm_cast at h5
  omega

theorem mem_nonZeroDivisors_of_not_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp

theorem exists_isRegular_quotSMulTop {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by
  have key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X],
      maximalIdeal B • (⊤ : Submodule B X) < ⊤ := fun X _ _ _ _ => by
    refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
    have H : Module.annihilator B X ≠ ⊤ := fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)
    exact (jacobson_eq_maximalIdeal _ H).ge
  have hne : (y • (⊤ : Submodule B B)) ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ y • (⊤ : Submodule B B) := by rw [h]; exact Submodule.mem_top
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact (mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))
  have : Nontrivial (QuotSMulTop y B) := Submodule.Quotient.nontrivial_iff.mpr hne
  let M : ModuleCat.{u} B := ModuleCat.of B B
  let S := ModuleCat.smulShortComplex M y
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact (M := M) hy
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))
  have hregB : IsRegular B rs := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg
  have hextB : ∀ i < rs.length, Subsingleton (Ext N M i) :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 2 4).mpr
      (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')
  have hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have hex := Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl
    have h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))
    have h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))
  have : Module.Finite B S.X₃ := inferInstanceAs (Module.Finite B (QuotSMulTop y B))
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial (QuotSMulTop y B))
  obtain ⟨rs', hlen, hm', hreg'⟩ :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 2 4).mp hext3
  exact ⟨rs', hlen, hm', hreg'⟩

theorem CMRegularElement.proof : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def UniformiserLocallyInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ U)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PModelLocalizationMaximalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem ModelLocalizationMaximalPoint.proof : ModelLocalizationMaximalPoint.Statement := by
  intro n J q M P hP
  let A := MvPolynomial (Fin n) ℂ
  let R' := MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal
  let L := Localization (normalModelSubmonoid M q)
  let ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
  let φ : A →+* R' := (Ideal.Quotient.mk M.ideal).comp ι
  let _ : Algebra A R' := φ.toAlgebra
  have hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f) := fun _ ↦ rfl

  have hint : Algebra.IsIntegral A R' := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c) := by rw [hφ, rename_C]
      exact h ▸ isIntegral_algebraMap
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p s hp =>
      rw [map_mul]
      refine hp.mul ?_
      cases s with
      | inl i =>
        have h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i)) := by rw [hφ, rename_X]
        exact h ▸ isIntegral_algebraMap
      | inr i =>
        obtain ⟨F, hmon, hF⟩ := M.integral i
        refine ⟨F, hmon, ?_⟩
        rw [RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl,
          ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hF

  let m : Ideal A := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
  let Q : Ideal R' := P.comap (algebraMap R' L)
  have hQm : Q.comap (algebraMap A R') ≤ m := by
    intro f hf
    by_contra hfm
    have hS : algebraMap A R' f ∈ normalModelSubmonoid M q := Submonoid.mem_map_of_mem _ hfm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))

  obtain ⟨Q', hQQ', hQ'prime, hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm
  have hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hf, rfl⟩ hfQ
    apply hf
    have h : f ∈ Q'.comap (algebraMap A R') := hfQ
    change f ∈ Ideal.under A Q' at h
    rw [hQ'm] at h
    exact h
  have hPQ' : P = Q'.map (algebraMap R' L) := by
    have hne : Q'.map (algebraMap R' L) ≠ ⊤ :=
      (IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top
    refine hP.eq_of_le hne ?_
    rw [← IsLocalization.map_under (normalModelSubmonoid M q) L P]
    exact Ideal.map_mono hQQ'
  have hQeq : P.comap (algebraMap R' L) = Q' := by
    rw [hPQ']
    exact IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj
  have hQ'max : Q'.IsMaximal := by
    letI : Q'.IsPrime := hQ'prime
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under Q' (hQ'm ▸ hm)

  let N := P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))
  have hNmax : N.IsMaximal := by
    show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal
    rw [← Ideal.comap_comap, hQeq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax
  have key : ∀ p, p ∈ N ↔ eval w p = 0 := fun p ↦ by
    rw [hw, mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl
  refine ⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩
  · show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    exact P.zero_mem
  · funext i
    have h1 : X i - C (q i) ∈ m := by
      show eval q (X i - C (q i)) = 0
      rw [map_sub, eval_X, eval_C, sub_self]
    rw [← hQ'm, ← hQeq] at h1
    have h2 := (key (rename Sum.inl (X i - C (q i)))).1 h1
    simp only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  · ext p
    rw [RingHom.mem_ker]
    exact key p

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PlaneIdealTwoOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

theorem mdisc_const_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetFormComparison

theorem hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  unfold hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

theorem contDiff_logPot (N : ℕ) : ContDiff ℝ ∞ (HilbertSamuel.ProjFS.logPot (N := N)) := by
  have h : (HilbertSamuel.ProjFS.logPot (N := N)) = fun z => Real.log (1 + euclPot z) := rfl
  rw [h]
  exact (contDiff_const.add (contDiff_euclPot N)).log fun z => by
    have : 0 ≤ euclPot z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

theorem posSemidef_hessC_logPot_sub {N : ℕ} {z : Fin N → ℂ} (hz : ‖z‖ ≤ 1) :
    ((((1 + N : ℝ) ^ 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1).PosSemidef := by
  set m : ℝ := (1 + N) ^ 2 with hm
  have h1 : ContDiffAt ℝ 2 (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w) z :=
    contDiffAt_const.mul (((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have h2 : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * euclPot w) z :=
    contDiffAt_const.mul (((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have e : (m : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1 =
      hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z h1 h2, ReciprocityTheory.AnForm.M.hessC_const_mul',
      ReciprocityTheory.AnForm.M.hessC_const_mul', TubeFormComparison.hessC_euclPot]
    simp [sub_eq_add_neg]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ z (h1.add h2) fun w => ?_
  have hq := ReciprocityTheory.AnForm.M.re_star_dot_hessC
    (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z (star w)
  have hq' : levi (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z w =
      (star (star w) ⬝ᵥ (hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z
        *ᵥ star w)).re := by rw [hq, star_star]
  rw [hq', ← e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec,
    dotProduct_smul, CP.chernCoeff_quadForm, CP.star_dotProduct_self]
  set a : ℝ := ∑ j, ‖(star w) j‖ ^ 2 with ha
  set q : ℝ := 1 + normSqSum z with hqdef
  have hS0 : 0 ≤ normSqSum z := normSqSum_nonneg z
  have hSN : normSqSum z ≤ N := by
    have : ∀ j, ‖z j‖ ^ 2 ≤ 1 := fun j =>
      pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hz)
    calc normSqSum z = ∑ j, ‖z j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin N, (1 : ℝ) := Finset.sum_le_sum fun j _ => this j
      _ = N := by simp
  have hCS := CP.norm_dotProduct_sq_le z (star w)
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : 1 ≤ q := by linarith
  have hpi := Real.pi_pos
  have hval : ((m : ℂ) • (((2 * Real.pi : ℝ) : ℂ) • ((1 / (2 * Real.pi * q) *
      (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) : ℝ) : ℂ)) - (a : ℂ)).re =
      m * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) / q - a := by
    simp only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    field_simp
  rw [hval]
  rw [← ha] at hCS
  have hd : q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 ≤ (1 - q⁻¹) * a := by
    rw [inv_mul_le_iff₀ (by linarith)]
    have : q * ((1 - q⁻¹) * a) = normSqSum z * a := by
      rw [hqdef]
      field_simp
      ring
    rw [this]
    exact hCS
  have hqm : q ^ 2 ≤ m := by
    rw [hm]
    have : q ≤ 1 + N := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hqa : a / q ≤ a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 := by
    have : a / q = q⁻¹ * a := by ring
    nlinarith
  rw [sub_nonneg, le_div_iff₀ (by linarith)]
  have h4 : q ^ 2 * (a / q) = q * a := by
    field_simp
  nlinarith [h4, mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ m),
    mul_le_mul_of_nonneg_right hqm (div_nonneg ha0 (by linarith : (0 : ℝ) ≤ q))]

end SheetFormComparison


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set ComplexSets

noncomputable section

namespace ConeSliceSheetParam

theorem eval_sup_span {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    {x : Fin n → ℂ} (hJ : ∀ q ∈ J, eval x q = 0) (hf : eval x f = 0) :
    ∀ q ∈ J ⊔ Ideal.span {f}, eval x q = 0 := by
  intro q hq
  have hle : J ⊔ Ideal.span {f} ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hJ q hq))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hf)))
  exact RingHom.mem_ker.1 (hle hq)

theorem eval_smul_of_isHomogIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsHomogIdeal J)
    {x : Fin n → ℂ} (hx : ∀ q ∈ J, eval x q = 0) (t : ℂ) : ∀ q ∈ J, eval (t • x) q = 0 := by
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i q), hx _ (hJ q hq i), mul_zero]

theorem eval_linForm_smul {n : ℕ} (ℓ : Fin n → ℂ) (t : ℂ) (x : Fin n → ℂ) :
    eval (t • x) (linForm ℓ) = t * eval x (linForm ℓ) := by
  rw [eval_smul_of_isHomogeneous (SliceIdeal.isHomogeneous_linForm ℓ), pow_one]

theorem slice_isPrime {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} (hJ : IsProjPrime J)
    (hℓ : linForm ℓ ∉ J) : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime := by
  have hP := hJ.isPrime
  have hdeh : ∀ (G : MvPolynomial (Fin n) ℂ) (d : ℕ), G.IsHomogeneous d →
      G ∈ J ⊔ Ideal.span {linForm ℓ - 1} → G ∈ J :=
    fun G d hG hm => ChartDehomog.proof ℂ n J ℓ G d hP hJ.isHomog hℓ hG hm
  have hspan : Ideal.span {linForm ℓ - 1} ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_right
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {a b} hab => ?_⟩
  · exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr
      (hdeh 1 0 (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)))
  obtain ⟨da, A, hA', hAa⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ a
  obtain ⟨db, B, hB', hBb⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ b
  have hAB : A * B ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
    have h : A * B = (A - a) * B + a * (B - b) + a * b := by ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hspan (Ideal.mul_mem_right _ _ hAa))
      (hspan (Ideal.mul_mem_left _ _ hBb))) hab
  rcases hP.mem_or_mem (hdeh _ _ (hA'.mul hB') hAB) with h | h
  · left
    have e : a = A - (A - a) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hAa)
  · right
    have e : b = B - (B - b) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hBb)

end ConeSliceSheetParam


open ConeSliceSheetParam in
theorem ConeSliceSheetParam.proof (hCov : DiscriminantSheetCover.Statement) :
    ConeSliceSheetParam.Statement := by
  classical
  intro n e h J ℓ A hJ hdim hℓ hA
  have hP := hJ.isPrime
  obtain ⟨P, U, D, N, s, hP0, hUD, hdisj, hbad, hnull, hfib⟩ :=
    hCov n e _ A (slice_isPrime hJ hℓ) (SliceDim.proof n e J ℓ hJ hdim hℓ) hA
  set J' := J ⊔ Ideal.span {linForm ℓ - 1} with hJ'
  set M := (h.matᵀ)⁻¹ with hM
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det

  have hslice : ∀ x ∈ zeroSet J', (∀ q ∈ J, eval x q = 0) ∧ eval x (linForm ℓ) = 1 := by
    intro x hx
    refine ⟨fun q hq => hx q (Ideal.mem_sup_left hq), ?_⟩
    have h1 := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_sub, map_one, sub_eq_zero] at h1
  have hval : ∀ k j y, y ∈ U k → s k j y ∈ zeroSet J' ∧ A *ᵥ s k j y = y := by
    intro k j y hy
    have hm : s k j y ∈ ComplexSets.fibre J' A y := by rw [(hfib k y hy).1]; exact ⟨j, rfl⟩
    exact hm

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ), h.pointOf (t • WithLp.toLp 2 (M *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf]
    change h.matᵀ *ᵥ (t • (M *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, hM, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, y, t⟩ ⟨hy, ht⟩ ⟨⟨k', j'⟩, y', t'⟩ ⟨hy', ht'⟩ heq
    simp only at hy ht hy' ht' heq
    have hv := congrArg h.pointOf heq
    rw [hpt, hpt] at hv
    obtain ⟨hZ, hA1⟩ := hval k j y ((hUD k).2.2.1 hy)
    obtain ⟨hZ', hA1'⟩ := hval k' j' y' ((hUD k').2.2.1 hy')
    have hl := congrArg (fun x => eval x (linForm ℓ)) hv
    simp only [eval_linForm_smul, (hslice _ hZ).2, (hslice _ hZ').2, mul_one] at hl
    subst hl
    have hss : s k j y = s k' j' y' := smul_right_injective _ ht hv
    have hyy : y = y' := by rw [← hA1, ← hA1', hss]
    subst hyy
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hy hy'
    subst hkk
    have hjj : j = j' := (hfib k y ((hUD k).2.2.1 hy)).2.1 hss
    subst hjj
    rfl
  ·
    rintro z ⟨⟨⟨k, j⟩, y, t⟩, ⟨hy, ht⟩, rfl⟩
    simp only at hy ht
    intro q hq
    rw [hpt]
    exact eval_smul_of_isHomogIdeal hJ.isHomog (hslice _ (hval k j y ((hUD k).2.2.1 hy)).1).1 t q hq
  ·
    obtain ⟨δ, G, hG, hGf⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ (pullback A P)
    have hGJ : G ∉ J := by
      intro hGm
      apply hP0
      have hm : pullback A P ∈ J' := by
        have e1 : pullback A P = G - (G - pullback A P) := by ring
        rw [e1]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left hGm) (Ideal.mem_sup_right hGf)
      apply hA.injective
      rw [map_zero]
      change (Ideal.Quotient.mkₐ ℂ J') (pullback A P) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    have hZ1 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {linForm ℓ})
      (MassFinite.dim_sup_lt J hP hdim _ hℓ)
    have hZ2 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {G})
      (MassFinite.dim_sup_lt J hP hdim _ hGJ)
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (M *ᵥ s q.1.1 q.1.2 q.2.1) with hF
    let L := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
    have hsub : {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
        F '' {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
        L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) := by
      rintro z ⟨hzC, hzF⟩
      set p := h.pointOf z with hp
      have hzp : L (WithLp.toLp 2 p) = z := by
        change WithLp.toLp 2 (M *ᵥ (h.matᵀ *ᵥ WithLp.ofLp z)) = z
        rw [mulVec_mulVec, hM, nonsing_inv_mul _ hdet, one_mulVec]
      have hpJ : ∀ q ∈ J, eval p q = 0 := hzC
      refine ⟨WithLp.toLp 2 p, ?_, hzp⟩
      by_cases h0 : eval p (linForm ℓ) = 0
      · exact Or.inl (eval_sup_span hpJ h0)
      set c := eval p (linForm ℓ) with hc
      have hpx : p = c • (c⁻¹ • p) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
      have hx : c⁻¹ • p ∈ zeroSet J' :=
        eval_sup_span (eval_smul_of_isHomogIdeal hJ.isHomog hpJ c⁻¹)
          (by rw [map_sub, map_one, eval_linForm_smul, ← hc, inv_mul_cancel₀ h0, sub_self])
      by_cases hyD : A *ᵥ (c⁻¹ • p) ∈ ⋃ k, D k
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.1 hyD
        have hxf : c⁻¹ • p ∈ ComplexSets.fibre J' A (A *ᵥ (c⁻¹ • p)) := ⟨hx, rfl⟩
        rw [(hfib k _ ((hUD k).2.2.1 hk)).1] at hxf
        obtain ⟨j, hj⟩ := hxf
        apply hzF
        refine ⟨⟨⟨k, j⟩, A *ᵥ (c⁻¹ • p), c⟩, ⟨hk, h0⟩, ?_⟩
        rw [← hzp]
        simp only [hF, hj]
        change c • WithLp.toLp 2 (M *ᵥ (c⁻¹ • p)) = WithLp.toLp 2 (M *ᵥ p)
        rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      · have hPy : eval (A *ᵥ (c⁻¹ • p)) P = 0 := hbad hyD
        refine Or.inr (eval_sup_span hpJ ?_)
        have hGx : eval (c⁻¹ • p) G = eval (c⁻¹ • p) (pullback A P) := by
          have h2 := hx _ (Ideal.mem_sup_right hGf)
          rwa [map_sub, sub_eq_zero] at h2
        rw [hpx, eval_smul_of_isHomogeneous hG, hGx, MassFinite.eval_pullback, hPy, mul_zero]
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          (L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
              (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [measure_union_null hZ1 hZ2, mul_zero]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPointOfPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelPointOfPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ∀ P : MaximalSpectrum (curveNormalisation J q),
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
            Ring.ord (pointLocalRing M.ideal w)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnChart.proof (hD : ComplexSets.DiscriminantCover.Statement) (hL : CutOffLimit.Statement) :
    StokesOnChart.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
      (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ) := by
    intro n d J A f g φ hJ hdim hAf hf hg hφ hc
    obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

    have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
      intro x hx hPx
      obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
      obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
      refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
      · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
        exact hw'.1
      · rintro x' hx' -
        rw [hZV] at hx'
        obtain ⟨w, hw, rfl⟩ := hx'
        rw [hAs w hw]
    obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
    obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
    refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
    obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
    obtain ⟨V, hV, hZV, hfV⟩ := hf
    have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
    refine (StokesOffDiscriminant.proof n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
      ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
    rw [hχ0 x hx, zero_mul]
  intro n d J A f g φ hJ hdim hAf hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J A f g φ hJ hdim hAf hf hg hφ hc
  · exact (key n d J A g f φ hJ hdim hAf hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveBranchOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem NormalCurveBranchOrder.proof (hdvr : NormalCurvePointDVR.Statement)
    (hsz : UniformiserBranchSimpleZero.Statement) : NormalCurveBranchOrder.Statement := by
  intro n J M w r φ hJ hdim hr hdiff hinj hmaps hw0 g
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  obtain ⟨hdom, hD⟩ := hdvr _ M.ideal w M.isPrime M.isIntegrallyClosed hdim' hwZ
  have hnear : ∀ q ∈ M.ideal, ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q = 0 := by
    refine fun q hq ↦ Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun τ hτ ↦ hmaps ?_ q hq
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hat0 : ∀ q, eval (φ fun _ ↦ (0 : ℂ)) q = eval w q := fun q ↦ by rw [← hw0]; rfl
  have han := fun q ↦ analyticAt_eval_disc hr hdiff q
  have hne0 : ∀ q, eval w q ≠ 0 → ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q ≠ 0 :=
    fun q hq ↦ (han q).continuousAt.eventually_ne (by simpa [hat0] using hq)
  have hord0 : ∀ q, eval w q ≠ 0 → analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) q) 0 = 0 :=
    fun q hq ↦ analyticOrderAt_eq_zero.2 (Or.inr (by simpa [hat0] using hq))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointLocalRing M.ideal w)
  obtain ⟨t, s₀, hs₀, hts⟩ := pointLocalRing_exists_mul_eq M.ideal w ϖ
  have hassoc : Associated ϖ (algebraMap _ (pointLocalRing M.ideal w) t) :=
    ⟨(isUnit_algebraMap_pointLocalRing _ w s₀ hs₀).unit, hts⟩
  have ht := hassoc.irreducible hϖ
  have ht1 := hsz _ M.ideal w t r φ M.isPrime M.isIntegrallyClosed hdim' ht hr hdiff hinj hmaps hw0
  by_cases hg : algebraMap _ (pointLocalRing M.ideal w) g = 0
  · rw [hg, ord_zero_eq_top_of_dvr, eq_comm, analyticOrderAt_eq_top]
    obtain ⟨s, hs, hsg⟩ := pointLocalRing_exists_mul_mem M.ideal w g hg
    filter_upwards [hnear _ hsg, hne0 s hs] with τ h1 h2
    rw [map_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hg ht
  obtain ⟨a, s, hs, has⟩ := pointLocalRing_exists_mul_eq M.ideal w (v : pointLocalRing M.ideal w)
  have ha : eval w a ≠ 0 := pointLocalRing_eval_ne_zero_of_isUnit M.ideal w hwZ a
    (by rw [← has]; exact v.isUnit.mul (isUnit_algebraMap_pointLocalRing _ w s hs))
  have hrel : algebraMap _ (pointLocalRing M.ideal w) (g * a - t ^ e * s) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, ← has, ← hv]
    ring
  obtain ⟨s', hs', hmem⟩ := pointLocalRing_exists_mul_mem M.ideal w _ hrel
  have heq : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) =ᶠ[𝓝 0]
      (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) := by
    filter_upwards [hnear _ hmem, hne0 s' hs'] with τ h1 h2
    simp only [map_mul, map_sub, map_pow] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)
  have hL : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) 0 =
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) a) 0 :=
    analyticOrderAt_mul (han g) (han a)
  have hR : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) 0 =
      e • analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) s) 0 := by
    rw [← analyticOrderAt_pow (han t)]
    exact analyticOrderAt_mul ((han t).pow e) (han s)
  have hc := analyticOrderAt_congr heq
  rw [hL, hR, ht1, hord0 a ha, hord0 s hs, add_zero, add_zero] at hc
  rw [hc, ← Ring.ord_mul_of_isUnit_right v.isUnit, hv, ord_pow_irreducible_of_dvr ht]
  simp

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalisationModelLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem NormalisationModelLocalization.full : NormalisationModelLocalization.Statement :=
  NormalisationModelLocalization.proof

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PlaceBranchExists.proof (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceHasBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PlaceHasBranch.proof (h₁ : PlaceBranchExists.Statement) (h₂ : PuncturedBranchInOneBranch.Statement)
    (h₃ : PuncturedBranchSameOrder.Statement) : PlaceHasBranch.Statement := by
  intro n I q m c hrad hdim hcov hdisj P
  obtain ⟨N, hN, hNc⟩ := hcov
  obtain ⟨ν, hν⟩ := h₁ n I q hrad hdim P
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]

  have hcont : ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) 0 := by
    have h0 : ContinuousAt ν.toFun (fun _ ↦ (0 : ℂ)) :=
      ν.differentiableOn.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right, hnorm] using ν.radius_pos))
    exact h0.comp (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N := hcont.preimage_mem_nhds (by rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  have hin : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < min ε ν.radius → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image := by
    intro τ _ hτ
    refine hNc ⟨ν.mapsTo ?_, hεN ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hτ.trans_le (min_le_right _ _)
    · rw [dist_zero_right]
      exact hτ.trans_le (min_le_left _ _)
  obtain ⟨b, ρ', hρ', hb⟩ := h₂ n I q m c ν (min ε ν.radius) hrad hdim (lt_min hε ν.radius_pos) hin hdisj
  exact ⟨b, fun f ↦ (hν f).trans (h₃ n I q (c b) ν ρ' hrad hdim hρ' hb f).symm⟩

end GroundTheory.Heights₂.Heights
end
