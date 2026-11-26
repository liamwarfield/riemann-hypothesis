module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem graphChart_of_eq_on_open {n d : ℕ} {Y Y' U : Set (Fin n → ℂ)} {q : Fin n → ℂ}
    (hU : IsOpen U) (hqU : q ∈ U) (hYU : Y' ∩ U = Y ∩ U)
    (h : ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) :
    ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y' ∩ V = g '' O := by
  obtain ⟨A, O, V, g, hO, hV, hqV, hg, hAg, hYV⟩ := h
  refine ⟨A, O ∩ g ⁻¹' U, V ∩ U, g, hg.continuousOn.isOpen_inter_preimage hO hU, hV.inter hU, ⟨hqV, hqU⟩,
    fun y hy => hg y hy.1, fun y hy => hAg y hy.1, ?_⟩
  rw [Set.image_inter_preimage, ← hYV]
  ext x
  constructor
  · rintro ⟨hx, hxV, hxU⟩
    have hx' : x ∈ Y ∩ U := by rw [← hYU]; exact ⟨hx, hxU⟩
    exact ⟨⟨hx'.1, hxV⟩, hxU⟩
  · rintro ⟨⟨hx, hxV⟩, hxU⟩
    have hx' : x ∈ Y' ∩ U := by rw [hYU]; exact ⟨hx, hxU⟩
    exact ⟨hx'.1, hxV, hxU⟩

theorem ringKrullDim_quotient_minimalPrime_add_one {n : ℕ} {V W : Ideal (MvPolynomial (Fin n) ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial (Fin n) ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial (Fin n) ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial (Fin n) ℂ ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem ringKrullDim_quotient_sup_span_lt {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by
  rw [ringKrullDim_quotient, Order.krullDim_lt_coe_iff]
  intro l
  have hLP : L ≤ l.head.1.asIdeal := fun x hx => l.head.2 (Ideal.mem_sup_left hx)
  have hfP : f ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hLP
  let W' : PrimeSpectrum R := ⟨W, hW.1.1⟩
  have hlt : W' < l.head.1 := lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)
  have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1 := by
    exact Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))
  have h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W' := Order.coheight_add_one_le hlt
  have hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R := R) (W : Set R) := by
    ext p
    exact Iff.rfl
  have h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]
    exact hd W hW
  have h3' : Order.coheight W' = (d : ℕ∞) := by exact_mod_cast h3
  have h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← h3']
    push_cast
    calc (l.length : ℕ∞) + 1 ≤ Order.coheight l.head.1 + 1 := by gcongr
      _ ≤ Order.coheight W' := h2
  have h5 : l.length + 1 ≤ d := by exact_mod_cast h4
  omega

theorem graphChart_of_frameGraphGeneric (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by
  obtain ⟨I₀, h, hcard, hhW, hreg⟩ := hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)
  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x i := fun x i => rfl
  have hS : ∀ w i, S w i = w i := fun w i => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun i => by rw [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; rw [hT, hS]
  have hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W := by
    intro x
    have hx : (fun i => T x i) = x := funext fun i => hT x i
    simp only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]
  refine ⟨h, hhW, fun z hz hzh => ?_⟩
  have hzh' : eval (fun i => T z i) h ≠ 0 := by
    have hx : (fun i => T z i) = z := funext fun i => hT z i
    rwa [hx]
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ := hreg (T z) ((hZ z).mp hz) hzh'
  let eI : I₀ ≃ Fin e := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)
  let A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin e =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc W ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨w, hw, hgw⟩ := hmem
      have hΨw : Ψ (fun k => w (eI.symm k)) = w := funext fun i => by simp [hΨ]
      refine ⟨fun k => w (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨw]
      · simp only [hΨw, hgw, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]
        exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]
        exact hmem.2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAdicCompletionRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem AdicCompletionRegular.proof : AdicCompletionRegular.Statement := by
  intro R _ hR M hM hreg
  let B := AdicCompletion M R
  have hfg : M.FG := Ideal.fg_of_isNoetherianRing M
  have : IsLocalRing B := adicCompletion_isLocalRing_of_isMaximal M hfg
  have : IsNoetherianRing B := GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M
  have hmax : (M.map (algebraMap R B)).IsMaximal := AdicCompletion.isMaximal_map_of_le M M le_rfl hfg
  have hmB : M.map (algebraMap R B) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M :=
    (hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm
  have hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra h
    have hs : algebraMap R B s ∈ maximalIdeal B := h
    rw [← hmB] at hs
    have hs' := Ideal.mem_comap.mpr hs
    rw [hc] at hs'
    exact s.2 hs'
  let _ : Algebra (Localization.AtPrime M) B :=
    (IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra
  have : IsScalarTower R (Localization.AtPrime M) B :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have : Module.Flat (Localization.AtPrime M) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance
  have hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) =
      maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]
  have : IsLocalHom (algebraMap (Localization.AtPrime M) B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B :=
      hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)
    exact h1 ha
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularDimGe.proof (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  have hy : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hy
  set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef
  have hU : IsOpen U := hg₁.continuousOn.isOpen_inter_preimage hO₁ hV
  have hUne : U.Nonempty := ⟨t₀, ht₀, hyV⟩
  have hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U :=
    A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)

  have hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u := by
    intro t ht
    have h1 : g₁ t ∈ X ∩ V₁ := hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1
    have h2 : g₁ t ∈ X ∩ V := ⟨h1.1, ht.2⟩
    rw [hXV] at h2
    obtain ⟨u, hu, hgu⟩ := h2
    exact ⟨u, hu, hgu.symm⟩
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff
  apply hz
  refine Set.Subsingleton.finite ?_
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨u₁, hu₁, hg1⟩ := hmem t₁ ht₁.1
  obtain ⟨u₂, hu₂, hg2⟩ := hmem t₂ ht₂.1
  have hz1 : A' (g₁ t₁) = z := ht₁.2
  have hz2 : A' (g₁ t₂) = z := ht₂.2
  rw [hg1, hleft u₁ hu₁] at hz1
  rw [hg2, hleft u₂ hu₂] at hz2
  have hgg : g₁ t₁ = g₁ t₂ := by rw [hg1, hg2, hz1, hz2]
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyMassLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

theorem VarietyMassLower.proof (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by
  intro n d J hJ hd R
  set τ := μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) with hτdef
  have hτ : 0 < τ := TangentGraphLowerDensity.unitBall_pos d
  set m : ℝ≥0∞ := min τ 1 with hmdef
  have hm0 : 0 < m := lt_min hτ one_pos
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmτ : m ≤ τ := min_le_left _ _
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmtop
  refine ⟨(1 / 2) * (1 / 2) ^ (2 * d) * m.toReal, by positivity, fun z hz _ ρ hρ => ?_⟩
  obtain ⟨hρ0, -⟩ := hρ
  obtain ⟨b, I₀, Ω, V, g, w₀, hcard, hΩ, hV, hw₀, hg, hproj, hZV, htan, hdist⟩ :=
    hG n d J hJ hd z hz (ρ / 2) (by linarith)
  have hz₀ : g w₀ ∈ zeroSetEuc J := by
    have h : g w₀ ∈ g '' Ω := ⟨w₀, hw₀, rfl⟩
    rw [← hZV] at h
    exact h.1
  obtain ⟨r₀, hr₀, hlow⟩ := hL n d b I₀ (zeroSetEuc J) Ω V g w₀ hcard hΩ hV hw₀ hg hproj hZV htan
    (1 / 2) ⟨by norm_num, by norm_num⟩
  set t := min (r₀ / 2) (ρ / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ ρ / 2 := min_le_right _ _
  have h1 := hlow t ⟨ht0, htr⟩
  have h2 := hM n d J hJ hd (g w₀) hz₀ t (ρ / 2) ht0 hts
  have hsub : zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2) ⊆ zeroSetEuc J ∩ Metric.ball z ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith))
  have h3 := measure_mono (μ := μH[((2 * d : ℕ) : ℝ)]) hsub
  have key : ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ) ≤
      ENNReal.ofReal (t ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := by
    calc ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ)
        = ENNReal.ofReal ((ρ / 2) ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * t ^ (2 * d)) * τ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          ring
      _ ≤ ENNReal.ofReal ((ρ / 2) ^ (2 * d)) *
            μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) t) := by gcongr
      _ ≤ _ := h2
  have key' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
    ENNReal.ofReal_ne_top).1 key
  have hc : (1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d) =
      ((1 / 2) * (ρ / 2) ^ (2 * d)) * m.toReal := by
    rw [div_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal ((1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d))
      = ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * m := by
        rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ := by gcongr
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := key'
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) := h3

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationMinorOfDetection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.proof : DerivationMinorOfDetection.Statement := by
  intro T _ P _ h f hfP hind hdet
  let A := Localization.AtPrime P
  let K := ResidueField A
  let π : T →+* K := (residue A).comp (algebraMap T A)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    show residue A (algebraMap T A x) = 0 ↔ x ∈ P
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff A P x
  let v : Derivation ℤ T T → Fin h → K := fun D i => π (D (f i))
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφv : ∀ w : Fin h → K, φ w = ∑ i, w i * φ (Pi.single i 1) := fun w => by
      conv_lhs => rw [pi_eq_sum_univ w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    choose a ha using fun i => residue_surjective (R := A) (φ (Pi.single i 1))
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ a
    choose b hb using fun i => hs i (Finset.mem_univ i)
    have hπb : ∀ i, π (b i) = π s * φ (Pi.single i 1) := fun i => by
      simp only [π, RingHom.comp_apply, hb i, Algebra.smul_def, map_mul, ha]
    have hsq := hdet (∑ i, b i * f i) (Ideal.sum_mem _ fun i _ => P.mul_mem_left _ (hfP i)) fun D => by
      have h1 : ∑ i, b i * D (f i) ∈ P := by
        have hD : φ (v D) = 0 := hφ (Submodule.subset_span ⟨D, rfl⟩)
        rw [hφv] at hD
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hπ, map_sum]
        simp only [map_mul, hπb]
        rw [show ∑ i, π s * φ (Pi.single i 1) * π (D (f i)) = π s * ∑ i, v D i * φ (Pi.single i 1) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [v]; ring, hD, mul_zero]
      have hl : ∀ i, D (b i * f i) = b i * D (f i) + f i * D (b i) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hl, Finset.sum_add_distrib]
      exact P.add_mem h1 (Ideal.sum_mem _ fun i _ => P.mul_mem_right _ (hfP i))
    have hbP : ∀ i, b i ∈ P := fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).1
      (hind (fun i => algebraMap T A (b i)) (by simpa only [map_sum, map_mul] using hsq) i)
    have hsP : π s ≠ 0 := fun h0 => s.2 ((hπ s).1 h0)
    have he : ∀ i, φ (Pi.single i 1) = 0 := fun i => by
      have := (hπ (b i)).2 (hbP i)
      rw [hπb] at this
      exact (mul_eq_zero.1 this).resolve_left hsP
    exact hφ0 (LinearMap.ext fun w => by simp [hφv w, he])
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  let bas := Module.Basis.mk hli (by rw [hsp, hspan])
  have hfin : Finite κ := Module.Finite.finite_basis bas
  have hκ : Nat.card κ = h := by rw [← Module.finrank_eq_nat_card_basis bas, Module.finrank_fin_fun]
  let e : Fin h ≃ κ := (finCongr hκ.symm).trans (Finite.equivFin κ).symm
  refine ⟨fun j => a (e j), fun hmem => ?_⟩
  have hunit : IsUnit (Matrix.of fun i j => v (a (e j)) i) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  have hne : π (Matrix.of fun i j => a (e j) (f i)).det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  exact hne ((hπ _).2 hmem)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroSetOpenMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology

noncomputable section

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem ZeroSetOpenMass.proof
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hF : FiniteMapOpen.Statement) : ZeroSetOpenMass.Statement := by
  intro n d W hW hdim x O hO hxO hxZ
  obtain ⟨A, hA⟩ := (hG n d W hW hdim).2.1
  obtain ⟨P, hP0, hPcov⟩ := hD n d W A hW hdim hA
  have hopen := hF n d W (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hW hA.injective hA.finite x hxZ O
    (hO.mem_nhds hxO)
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) =
      fun z => A.mulVec z := funext (eval_linPoly A)
  rw [hfun, eval_linPoly A x] at hopen
  obtain ⟨y, hyS, hPy⟩ := exists_eval_ne_zero_of_isOpen hP0 isOpen_interior
    ⟨_, mem_interior_iff_mem_nhds.mpr hopen⟩
  obtain ⟨z, ⟨hzW, hzO⟩, hzy⟩ := interior_subset hyS
  subst hzy
  obtain ⟨-, -, hloc⟩ := hPcov _ hPy
  obtain ⟨U, V, g, hU, hzU, hV, hzV, hg, hgz, hAg, hZV⟩ := hloc z ⟨hzW, rfl⟩
  set U' := U ∩ g ⁻¹' (O ∩ V) with hU'def
  have hU' : IsOpen U' := hg.continuousOn.isOpen_inter_preimage hU (hO.inter hV)
  have hzU' : A.mulVec z ∈ U' := ⟨hzU, by simp only [Set.mem_preimage, hgz]; exact ⟨hzO, hzV⟩⟩
  have hsub : g '' U' ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O := by
    rintro _ ⟨w, ⟨hwU, hwO, -⟩, rfl⟩
    have hw : g w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := by
      rw [hZV]; exact Set.mem_image_of_mem g hwU
    exact ⟨hw.1, hwO⟩
  have himg : (fun z => A.mulVec z) '' (g '' U') = U' := by
    rw [Set.image_image]
    exact (Set.image_congr fun w (hw : w ∈ U') => hAg w hw.1).trans (Set.image_id' _)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzWith K (fun z : Fin n → ℂ => A.mulVec z) :=
    ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩
  have hpos : 0 < μH[((2 * d : ℕ) : ℝ)] U' := by
    rw [← finrank_real_fin_complex d]
    exact hU'.measure_pos _ ⟨_, hzU'⟩
  have hle := hK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)) (g '' U')
  rw [himg] at hle
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem zeroSet_subset_biUnion_minimalPrimes {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by
  intro x hx
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  exact Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)

theorem withBot_enat_le_pred {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      have hm : m < d := by exact_mod_cast h
      refine ⟨by omega, ?_⟩
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))

theorem minimalPrime_tube_bound (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by
  have hprime : P.IsPrime := hP.1.1
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨hd, hk⟩ := withBot_enat_le_pred hnn (hle.trans_lt hdim)
  obtain ⟨C, hC, hCr⟩ := h n (d - 1) P K hprime hk hK
  refine ⟨C, hC, fun r hr => ?_⟩
  have he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d := by omega
  simpa [he] using hCr r hr

theorem SmallSetTubeVolume.proof (h : PrimeTubeVolume.Statement) : SmallSetTubeVolume.Statement := by
  intro n d I K hdim hK
  set e : ℤ := (2 * n + 2 : ℤ) - 2 * d
  have key : ∀ F : Finset (Ideal (MvPolynomial (Fin n) ℂ)), (↑F : Set _) ⊆ I.minimalPrimes →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (⋃ P ∈ F, zeroSet P ∩ K)) ≤ ENNReal.ofReal (C * r ^ e) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, le_rfl, fun r _ => by simp⟩
    | insert a F ha ih =>
      intro hsub
      obtain ⟨C₁, hC₁, h₁⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      obtain ⟨C₂, hC₂, h₂⟩ := minimalPrime_tube_bound h hdim hK (hsub (Finset.mem_insert_self a F))
      refine ⟨C₂ + C₁, add_nonneg hC₂ hC₁, fun r hr => ?_⟩
      have hre : 0 ≤ r ^ e := zpow_nonneg hr.1.le e
      rw [Finset.set_biUnion_insert, Metric.thickening_union, add_mul,
        ENNReal.ofReal_add (mul_nonneg hC₂ hre) (mul_nonneg hC₁ hre)]
      exact (measure_union_le _ _).trans (add_le_add (h₂ r hr) (h₁ r hr))
  obtain ⟨F, hF⟩ := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).exists_finset_coe
  obtain ⟨C, hC, hCr⟩ := key F hF.le
  refine ⟨C, hC, fun r hr => le_trans (measure_mono (Metric.thickening_subset_of_subset r ?_)) (hCr r hr)⟩
  intro x ⟨hxI, hxK⟩
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 (zeroSet_subset_biUnion_minimalPrimes I hxI)
  rw [← hF] at hP
  exact Set.mem_iUnion₂.2 ⟨P, hP, hxP, hxK⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermPointsOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem isRegularPointOf_ball {d : ℕ} (c : Fin d → ℂ) (ε : ℝ) :
    ∀ y ∈ ball c ε, IsRegularPointOf (ball c ε) y := fun y hy =>
  ⟨hy, d, ContinuousLinearMap.id ℂ _, ball c ε, ball c ε, id, isOpen_ball, isOpen_ball, hy,
    analyticOnNhd_id, fun _ _ => rfl, by simp⟩

theorem IrreducibleGermPointsOffDiscriminant.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement) (hNear : PrimitiveFormSheetedPointsNear.Statement)
    (hConn : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermPointsOffDiscriminant.Statement := by
  intro σ _ X x d A hX hirr hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hPF σ X x d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  have hnear := hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  refine ⟨δ, hδ, hδ0, fun W hW => ?_⟩
  obtain ⟨W₀, hW₀, hiso'⟩ := hiso
  obtain ⟨Nn, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))
  have hr2 : 0 < r / 2 := half_pos hr
  have hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn) := (closedBall_subset_ball (half_lt_self hr)).trans hrsub

  set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X := by
    intro z
    simp only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      have : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨(hcb hz).2.2, fun i => (h0 i).2⟩
      rw [← hXN] at this
      exact ⟨hz, this.1⟩
    · rintro ⟨hz, hzX⟩
      have : z ∈ X ∩ Nn := ⟨hzX, (hcb hz).2.2⟩
      rw [hXN] at this
      exact ⟨hz, fun i => ⟨hz, this.2 i⟩⟩
  have hSc : IsCompact (K ∩ sphere x (r / 2)) := hKc.inter_right isClosed_sphere
  have hAS : A x ∉ A '' (K ∩ sphere x (r / 2)) := by
    rintro ⟨z, ⟨hzK, hzs⟩, hAz⟩
    have hzx : z = x := hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr2.ne hzs
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS
  obtain ⟨ε₂, hε₂, hε₂a⟩ := hδ.exists_ball_analyticOnNhd
  set D := ball (A x) (min ε₁ ε₂) with hD
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ D := hε₂a.mono (ball_subset_ball (min_le_right _ _))

  set T := D \ {y | δ y = 0} with hT
  have hTo : IsOpen T := hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hTc : IsPreconnected T := by
    refine hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_
    obtain ⟨y, hy0, hyD⟩ := ((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists
    exact ⟨y, hyD, hy0⟩

  set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu
  have huo : IsOpen u := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
    obtain ⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩ := hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2
    obtain ⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
    have hAz : A z = t₀ := by rw [← hgt₀]; exact hAg t₀ ht₀
    rw [hAz] at hyT ⊢
    have hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀ :=
      (hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))
    filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg
    have hgX : g t ∈ X ∩ V := hXV ▸ ⟨t, htO, rfl⟩
    exact ⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩
  have hune : (T ∩ u).Nonempty := by
    have hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x :=
      inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
    obtain ⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩ := hnear _ hU
    exact ⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩
  have hucl : closure u ∩ T ⊆ u := by
    rintro y ⟨hycl, hyT⟩
    have hsubK : u ⊆ A '' K := by
      rintro _ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩
      exact ⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl
    obtain ⟨hzcb, hzX⟩ := (hKmem z).mp hzK
    have hzb : z ∈ ball x (r / 2) := by
      refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)
      exact hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩
    exact ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
  have hTu : T ⊆ u := hTc.subset_of_closure_inter_subset huo hune hucl
  filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy
  obtain ⟨-, z, ⟨hzX, hzb⟩, hzy⟩ := hTu ⟨hy, hδy⟩
  exact ⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedPointsNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimitiveFormSheetedPointsNear.exists_root (n : ℕ) (hn : n ≠ 0) (c : Fin n → ℂ) :
    ∃ τ : ℂ, τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0 := by
  set p : Polynomial ℂ := Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  have hlt : (∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 j.isLt)
  have hdeg : p.degree = n := by
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  obtain ⟨τ, hτ⟩ := Complex.exists_root (f := p) (by rw [hdeg]; exact_mod_cast Nat.pos_of_ne_zero hn)
  exact ⟨τ, by simpa [p, Polynomial.eval_finsetSum] using hτ⟩

theorem PrimitiveFormSheetedPointsNear.derivative_ne_zero (n : ℕ) (c : Fin n → ℂ) (τ : ℂ)
    (hs : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hτ : τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 := by
  have h0 : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval τ = 0 := by
    simpa [Polynomial.eval_finsetSum] using hτ
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℂ) h0

theorem PrimitiveFormSheetedPointsNear.proof (hmin : PrimitiveFormMinimalFactorPoints.Statement)
    (hbr : AnalyticSimpleRootBranch.Statement) : PrimitiveFormSheetedPointsNear.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel U hU
  obtain ⟨n, b, hb, hm, hsepm, hpts⟩ :=
    hmin σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (z ∈ X → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) := by
    filter_upwards [hU, hP, eventually_all.2 hrel] with z h1 h2 h3 using ⟨h1, h2, fun hz i => h3 i hz⟩
  obtain ⟨U₁, hU₁sub, hU₁o, hwU₁⟩ := mem_nhds_iff.1 hgood
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using hm.self_of_nhds hirr.1
  have hE : ∀ᶠ y in 𝓝 (A w), (δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
        (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U₁ ∧
          A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
          ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ) ∧
      (δ y ≠ 0 → (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (δ y ≠ 0 → (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (∀ j, AnalyticAt ℂ (a j) y) ∧ (∀ j, AnalyticAt ℂ (b j) y) ∧ AnalyticAt ℂ δ y ∧
      (∀ i j, AnalyticAt ℂ (q i j) y) := by
    filter_upwards [hpts U₁ (hU₁o.mem_nhds hwU₁), hsepm, hsepP,
      eventually_all.2 fun j => (ha j).eventually_analyticAt, eventually_all.2 fun j => (hb j).eventually_analyticAt,
      hδ.eventually_analyticAt, eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt]
      with y h1 h2 h3 h4 h5 h6 h7 using ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨y, hyE, hyδ⟩ := (hE.eventually_nhds.and_frequently (not_eventually.1 hδ0)).exists
  obtain ⟨E, hEsub, hEo, hyE⟩ := mem_nhds_iff.1 hyE
  obtain ⟨hptsy, hsepmy, hsepPy, hay, hby, -, -⟩ := hEsub hyE
  obtain ⟨τ, hτ⟩ := PrimitiveFormSheetedPointsNear.exists_root n hn (fun j => b j y)
  obtain ⟨⟨hzX, hzU₁⟩, hAz, hℓz⟩ := hptsy hyδ τ hτ
  set z : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hz
  have hPτ : τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 := by
    simpa [hAz, hℓz] using (hU₁sub hzU₁).2.1 hzX
  obtain ⟨OP, BP, ψP, hOPo, hyOP, hBPo, hτBP, -, -, hψP⟩ :=
    hbr d N a y τ hay hPτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero N (fun j => a j y) τ (hsepPy hyδ) hPτ)
  obtain ⟨Om, Bm, ψm, hOmo, hyOm, -, -, hψman, hψmy, hψm⟩ :=
    hbr d n b y τ hby hτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero n (fun j => b j y) τ (hsepmy hyδ) hτ)
  have hδc : ContinuousOn δ E := fun t ht => (hEsub ht).2.2.2.2.2.1.continuousAt.continuousWithinAt
  set O : Set (Fin d → ℂ) := (Om ∩ ψm ⁻¹' BP) ∩ OP ∩ (E ∩ δ ⁻¹' {0}ᶜ) with hO
  have hOo : IsOpen O := ((hψman.continuousOn.isOpen_inter_preimage hOmo hBPo).inter hOPo).inter
    (hδc.isOpen_inter_preimage hEo isOpen_compl_singleton)
  set g : (Fin d → ℂ) → σ → ℂ := fun t i => (∑ j, q i j t * ψm t ^ (j : ℕ)) / δ t with hg
  have key : ∀ t ∈ O, g t ∈ X ∩ U₁ ∧ A (g t) = t ∧ ℓ (g t) = ψm t := fun t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩ =>
    (hEsub htE).1 htδ (ψm t) (((hψm t htm).2 (ψm t) (hψm t htm).1).2 rfl)
  have hPψ : ∀ t ∈ O, ψm t = ψP t := fun t ht => by
    obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
    have h := (hU₁sub hgU).2.1 hgX
    rw [hgA, hgℓ] at h
    exact ((hψP t ht.1.2).2 (ψm t) ht.1.1.2).1 h
  set V : Set (σ → ℂ) := U₁ ∩ A ⁻¹' O ∩ ℓ ⁻¹' BP with hV
  refine ⟨z, ⟨hzX, (hU₁sub hzU₁).1⟩, by rw [hAz]; exact hyδ, O, V, g, hOo,
    (hU₁o.inter (hOo.preimage A.continuous)).inter (hBPo.preimage ℓ.continuous),
    ⟨⟨hzU₁, by rw [Set.mem_preimage, hAz]; exact ⟨⟨⟨hyOm, by rw [Set.mem_preimage, hψmy]; exact hτBP⟩, hyOP⟩, hyE, hyδ⟩⟩,
      by rw [Set.mem_preimage, hℓz]; exact hτBP⟩, ?_, fun t ht => (key t ht).2.1, ?_⟩
  · rintro t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩
    obtain ⟨-, -, -, -, -, -, hqt⟩ := hEsub htE
    have hδt : AnalyticAt ℂ δ t := (hEsub htE).2.2.2.2.2.1
    refine AnalyticAt.pi fun i => AnalyticAt.fun_div ?_ hδt htδ
    exact Finset.analyticAt_fun_sum _ fun j _ => (hqt i j).mul ((hψman t htm).pow _)
  · ext z'
    constructor
    · rintro ⟨hz'X, ⟨hz'U, hz'O⟩, hz'B⟩
      refine ⟨A z', hz'O, ?_⟩
      have hs : ℓ z' = ψm (A z') := by
        rw [hPψ _ hz'O]; exact ((hψP _ hz'O.1.2).2 _ hz'B).1 ((hU₁sub hz'U).2.1 hz'X)
      have hδt : δ (A z') ≠ 0 := hz'O.2.2
      funext i
      rw [hg, div_eq_iff hδt, ← hs, ← (hU₁sub hz'U).2.2 hz'X i, mul_comm]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
      exact ⟨hgX, ⟨hgU, by rw [Set.mem_preimage, hgA]; exact ht⟩, by rw [Set.mem_preimage, hgℓ]; exact ht.1.1.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
