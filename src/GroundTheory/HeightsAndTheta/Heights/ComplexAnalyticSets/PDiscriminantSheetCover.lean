module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

namespace DiscriminantSheetCover

theorem volume_zero_set {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0) :
    volume {y : Fin d → ℂ | eval y P = 0} = 0 := by
  set S := {y : Fin d → ℂ | eval y P = 0} with hSdef
  have hS : MeasurableSet S :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  have hnull : μH[((2 * d : ℕ) : ℝ)]
      (zeroSetEuc ((⊥ : Ideal (MvPolynomial (Fin d) ℂ)) ⊔ Ideal.span {P})) = 0 :=
    NullSmaller.proof d d _ (MassFinite.dim_sup_lt ⊥ Ideal.isPrime_bot (space_dim d) P
      (by simpa [Ideal.mem_bot] using hP))
  obtain ⟨c, hc⟩ := SheetAreaCompare.exists_lintegral_volume_eq d
  have h := hc (S.indicator 1)
  rw [lintegral_indicator_one hS] at h
  rw [h]
  have hae : (fun y : EuclideanSpace ℂ (Fin d) => S.indicator (1 : (Fin d → ℂ) → ENNReal) (WithLp.ofLp y))
      =ᵐ[(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d)))] 0 := by
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
    have hyS : WithLp.ofLp y ∈ S := by
      by_contra h'
      exact hy (by simp [Set.indicator_of_notMem h'])
    intro q hq
    rw [bot_sup_eq] at hq
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    have : eval (WithLp.ofLp y) P = 0 := hyS
    simp only [map_mul]
    rw [show (fun i => y i) = WithLp.ofLp y from rfl, this, mul_zero]
  rw [lintegral_congr_ae hae]
  simp

theorem local_sheets {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {P : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (hcov : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (ComplexSets.fibre J A y).Finite ∧ (ComplexSets.fibre J A y).ncard = N ∧
        ∀ x ∈ ComplexSets.fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U)
    (y₀ : Fin d → ℂ) (hy₀ : eval y₀ P ≠ 0) :
    ∃ W : Set (Fin d → ℂ), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ {y | eval y P ≠ 0} ∧
      ∃ s : Fin N → (Fin d → ℂ) → Fin n → ℂ, (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ y ∈ W, ComplexSets.fibre J A y = Set.range (fun j => s j y) ∧ Function.Injective (fun j => s j y) ∧
          ∀ j, IsSheetAt J A (s j y) (s j) := by
  obtain ⟨hfin, hcard, hloc⟩ := hcov y₀ hy₀
  have : Finite (ComplexSets.fibre J A y₀) := hfin
  let e : ComplexSets.fibre J A y₀ ≃ Fin N := Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])
  let x : Fin N → Fin n → ℂ := fun j => (e.symm j).1
  have hx : ∀ j, x j ∈ ComplexSets.fibre J A y₀ := fun j => (e.symm j).2
  have hxinj : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  choose U V g hU hyU hV hxV hg hgy hAg hZ using fun j => hloc (x j) (hx j)
  have hcont : ∀ j, ContinuousAt (g j) y₀ := fun j =>
    (hg j).continuousOn.continuousAt ((hU j).mem_nhds (hyU j))
  have hev : ∀ᶠ w in 𝓝 y₀, (∀ j, w ∈ U j) ∧ eval w P ≠ 0 ∧ ∀ i j, i ≠ j → g i w ≠ g j w := by
    refine (eventually_all.2 fun j => (hU j).mem_nhds (hyU j)).and
      (((MvPolynomial.continuous_eval P).continuousAt.eventually_ne hy₀).and ?_)
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : g i y₀ - g j y₀ ≠ 0 := by
        rw [hgy, hgy]; exact sub_ne_zero.2 fun h => hij (hxinj h)
      filter_upwards [((hcont i).sub (hcont j)).eventually_ne hne] with w hw _
      exact sub_ne_zero.1 hw
  obtain ⟨W, hWsub, hWo, hyW⟩ := mem_nhds_iff.1 hev
  have hgZ : ∀ j, ∀ w ∈ U j, g j w ∈ zeroSet J ∩ V j := fun j w hw => (hZ j).symm ▸ ⟨w, hw, rfl⟩
  refine ⟨W, hWo, hyW, fun w hw => (hWsub hw).2.1, g,
    fun j => (hg j).mono fun w hw => (hWsub hw).1 j, fun w hw => ?_⟩
  obtain ⟨hwU, hwP, hwinj⟩ := hWsub hw
  have hinj : Function.Injective (fun j => g j w) := fun i j h => by_contra fun hij => hwinj i j hij h
  have hsub : Set.range (fun j => g j w) ⊆ ComplexSets.fibre J A w := by
    rintro _ ⟨j, rfl⟩
    exact ⟨(hgZ j w (hwU j)).1, hAg j w (hwU j)⟩
  obtain ⟨hfinw, hcardw, -⟩ := hcov w hwP
  refine ⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfinw).symm, hinj, fun j => ?_⟩
  · rw [hcardw, Set.ncard_range_of_injective hinj, Nat.card_fin]
  · refine ⟨W, hWo, by rw [hAg j w (hwU j)]; exact hw, (hg j).mono fun v hv => (hWsub hv).1 j,
      by rw [hAg j w (hwU j)], fun v hv => ⟨hAg j v ((hWsub hv).1 j), (hgZ j v ((hWsub hv).1 j)).1⟩,
      V j, (hV j).mem_nhds (hgZ j w (hwU j)).2, fun x' hx' _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ : x' ∈ g j '' U j := hZ j ▸ hx'
    rw [hAg j u hu]

end DiscriminantSheetCover

theorem DiscriminantSheetCover.proof (h₁ : ComplexSets.DiscriminantCover.Statement) :
    DiscriminantSheetCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨P, hP, hcov⟩ := h₁ n d J A hJ hdim hA
  have hall : ∀ y : Fin d → ℂ, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ (eval y P ≠ 0 → y ∈ W) ∧
      W ⊆ {y | eval y P ≠ 0} ∧ ∃ s : Fin (projDegree J A) → (Fin d → ℂ) → Fin n → ℂ,
        (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ w ∈ W, ComplexSets.fibre J A w = Set.range (fun j => s j w) ∧ Function.Injective (fun j => s j w) ∧
          ∀ j, IsSheetAt J A (s j w) (s j) := by
    intro y
    by_cases hy : eval y P = 0
    · exact ⟨∅, isOpen_empty, fun h => absurd hy h, Set.empty_subset _, fun _ _ => 0,
        fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    · obtain ⟨W, hWo, hyW, hWP, s, hs, hsW⟩ := DiscriminantSheetCover.local_sheets hcov y hy
      exact ⟨W, hWo, fun _ => hyW, hWP, s, hs, hsW⟩
  choose W hWo hyW hWP s hs hsW using hall
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : {y | eval y P ≠ 0} ⊆ ⋃ k, W (e k) := by
    intro y hy
    have : y ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨y, hyW y hy⟩
    obtain ⟨i, hiT, hyi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact Set.mem_iUnion.2 ⟨k, hyi⟩
  have hcompl : (⋃ k, disjointed (fun k => W (e k)) k)ᶜ ⊆ {y | eval y P = 0} := by
    rw [iUnion_disjointed]
    intro y hy
    by_contra h
    exact hy (hcover h)
  exact ⟨P, fun k => W (e k), disjointed (fun k => W (e k)), fun _ => projDegree J A, fun k => s (e k), hP,
    fun k => ⟨hWo _, MeasurableSet.disjointed (fun i => (hWo _).measurableSet) k, disjointed_le _ k, hs _⟩,
    disjoint_disjointed _, hcompl, measure_mono_null hcompl (DiscriminantSheetCover.volume_zero_set P hP),
    fun k => hsW (e k)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem LocalDimDomain.proof : LocalDimDomain.Statement := by
  intro n e J hJ he q hq
  have := hJ
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hJM : J ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := M.map (Ideal.Quotient.mk J)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ J) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk J y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk J z ∉ M.map (Ideal.Quotient.mk J)
      rw [Ideal.mem_quotient_iff_mem hJM]
      exact hz
    · intro h
      change Ideal.Quotient.mk J y ∉ M.map (Ideal.Quotient.mk J) at h
      rw [Ideal.mem_quotient_iff_mem hJM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt J q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt J q),
    NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) m hm, he]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

theorem SliceIdeal.isHomogeneous_linForm {n : ℕ} (u : Fin n → ℂ) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem SliceIdeal.exists_homogeneous_sub_mem {n : ℕ} (ℓ : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    ∃ d, ∃ G : MvPolynomial (Fin n) ℂ, G.IsHomogeneous d ∧ G - f ∈ Ideal.span {linForm ℓ - 1} := by
  classical
  refine ⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1),
      linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := ((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul
      (homogeneousComponent_isHomogeneous i f)
    convert h using 1
    omega
  · have hsum : (∑ i ∈ Finset.range (f.totalDegree + 1),
          linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f =
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f := by
      conv_lhs => arg 2; rw [← sum_homogeneousComponent f]
      rw [← Finset.sum_sub_distrib]
      simp only [sub_one_mul]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)
    simpa using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurvePointDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurvePointDVR.proof : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimePlaceBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimePlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (curveLocalRing J q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation J q), ∃ ν : VarBranch J 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserBranchSimpleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserBranchSimpleZero.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ)
    (r : ℝ) (φ : (Fin 1 → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) → φ 0 = w →
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem dim_eq_of_height_add {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hsum; exact absurd hsum (WithBot.bot_ne_natCast _)
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h1'
      exact absurd h1' (ENat.natCast_ne_top _)
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have a3 : y + 1 ≤ e + 1 := by exact_mod_cast h1
        have : y = e := by omega
        subst this; rfl

theorem ringKrullDim_component {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime]
    {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ J) (hW : W ∈ (J ⊔ Ideal.span {s}).minimalPrimes)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((d : ℕ) : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have _ : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := W.map (Ideal.Quotient.mk J)
  have _ : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp (by
    have : Ideal.Quotient.mk J s ∈ W' := Ideal.mem_map_of_mem _ hsW
    rwa [h, Ideal.mem_bot] at this))
  have hquot : ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot, hdim] at hform hdrop
  exact dim_eq_of_height_add hdrop (Ideal.map_height_le_one_of_mem_minimalPrimes hW) hform

theorem SliceMultGeneral.proof (hC : CMGeneralPoint.Statement) (hT : TransverseSliceGeneral.Statement)
    (hL : LengthTransverseSlice.Statement) : SliceMultGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  have hdW := ringKrullDim_component hu hW hdim
  obtain ⟨f₁, hf₁W, hf₁⟩ := hC n _ W hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hT n d W hWp hdW
  refine ⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hqf
  obtain ⟨hone, hcm⟩ := hf₁ q hq hqf.1
  obtain ⟨hO, hD⟩ := hf₂ q hq hqf.2
  refine ⟨_, hO, hD, fun L hL' => ?_⟩
  have hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q := by
    simp only [sliceIdeal, sup_right_comm]
  rw [hsl]
  exact hL n d _ W q L hW hdW hq hone hcm hL'

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem BranchLift.proof (hR : RiemannExtensionAnalytic.Statement)
    (hB : BranchOffHypersurface.Statement) (hO : NormalModelOpenMapping.Statement)
    (hP : NormalModelProper.Statement) : BranchLift.Statement := by
  intro n k J p M γ hJ hdim
  set Δ := Metric.ball (0 : Fin k → ℂ) γ.radius with hΔ
  have hγd : DifferentiableOn ℂ γ.toFun Δ := γ.differentiableOn
  have hγZ : ∀ τ ∈ Δ, γ.toFun τ ∈ zeroSetIn J := fun τ hτ => γ.mapsTo hτ
  choose a b hbJ hab using M.birational
  have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun z : Fin n → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      simp only [eval_add]
      exact hp.add hq
    | mul_X p i hp =>
      simp only [eval_mul, eval_X]
      exact hp.mul (differentiable_apply i)
  have hcomp : ∀ q, DifferentiableOn ℂ (fun τ => eval (γ.toFun τ) q) Δ := fun q =>
    (hpoly q).comp_differentiableOn hγd
  set g : (Fin k → ℂ) → ℂ := fun τ => eval (γ.toFun τ) (∏ i, b i) with hg
  have hBJ : (∏ i, b i) ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  have hgne : ∀ V, IsOpen V → V ⊆ Δ → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := fun V hV hVΔ hne =>
    hB n k J _ V γ.toFun hJ hdim hBJ hV hne (hγd.mono hVΔ) (γ.injOn.mono hVΔ)
      fun τ hτ => hγZ τ (hVΔ hτ)
  have hbne : ∀ τ, g τ ≠ 0 → ∀ i, eval (γ.toFun τ) (b i) ≠ 0 := fun τ hτ i h =>
    hτ (by simp only [hg, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
  set f : Fin M.m → (Fin k → ℂ) → ℂ := fun i τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)
  have hgraph : ∀ τ ∈ Δ, g τ ≠ 0 → (Sum.elim (γ.toFun τ) fun i => f i τ) ∈ zeroSetIn M.ideal :=
    fun τ hτ hgτ => M.graph_mem_zeroSetIn a b hab _ (hγZ τ hτ) (hbne τ hgτ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (Δ ∩ {t | g t ≠ 0}) := fun i τ hτ => by
    have h1 := (hcomp (a i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    have h2 := (hcomp (b i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    show DifferentiableWithinAt ℂ (fun τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)) _ τ
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv (hbne τ hτ.2 i))
  have hbdd : ∀ i, ∀ τ ∈ Δ, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f i '' (N ∩ Δ ∩ {t | g t ≠ 0})) := by
    intro i τ hτ
    obtain ⟨ε, hε, hεΔ⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball τ hτ
    have hsub : Metric.closedBall τ (ε / 2) ⊆ Δ :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεΔ
    have hK : Bornology.IsBounded (γ.toFun '' Metric.closedBall τ (ε / 2)) :=
      ((isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hγd.continuousOn.mono hsub)).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hP n J M _ hK)
    refine ⟨Metric.closedBall τ (ε / 2), Metric.closedBall_mem_nhds τ (by linarith),
      isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩⟩
    rintro _ ⟨t, ⟨⟨ht, htΔ⟩, hgt⟩, rfl⟩
    have hw := hC _ ⟨hgraph t htΔ hgt, ⟨t, ht, rfl⟩⟩
    exact (norm_le_pi_norm (Sum.elim (γ.toFun t) fun i => f i t) (Sum.inr i)).trans hw
  choose F hFd hFeq using fun i => hR k Δ g (f i) Metric.isOpen_ball
    ((hpoly _).comp_differentiableOn hγd) hgne (hfd i) (hbdd i)
  set Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ := fun τ => Sum.elim (γ.toFun τ) fun i => F i τ with hΓ
  have hΓd : DifferentiableOn ℂ Γ Δ := by
    refine differentiableOn_pi.2 fun s => ?_
    rcases s with j | i
    · simpa [hΓ] using differentiableOn_pi.1 hγd j
    · simpa [hΓ] using hFd i
  have hdense : Δ ⊆ closure (Δ ∩ {t | g t ≠ 0}) := by
    intro τ hτ
    rw [mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ⟨hto, htΔ⟩, hgt⟩ := hgne (o ∩ Δ) (ho.inter Metric.isOpen_ball)
      Set.inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, hto, htΔ, hgt⟩
  have hΓZ : ∀ τ ∈ Δ, Γ τ ∈ zeroSetIn M.ideal := by
    intro τ hτ q hq
    have heq : Set.EqOn (fun t => eval (Γ t) q) (fun _ => (0 : ℂ)) (Δ ∩ {t | g t ≠ 0}) := by
      intro t ht
      have hΓt : Γ t = Sum.elim (γ.toFun t) fun i => f i t := by
        simp only [hΓ]
        congr 1
        funext i
        exact hFeq i ht
      simp only [hΓt]
      exact hgraph t ht.1 ht.2 q hq
    exact heq.of_subset_closure ((MvPolynomial.continuous_eval q).comp_continuousOn hΓd.continuousOn)
      continuousOn_const Set.inter_subset_left hdense hτ
  have hΓinj : Set.InjOn Γ Δ := fun s hs t ht hst =>
    γ.injOn hs ht (by
      have := congrArg firstCoords hst
      exact this)
  refine ⟨Γ, hΓd, fun τ hτ => ⟨hΓZ τ hτ, rfl⟩, fun V hV hVo => ?_⟩
  exact hO n k J M V Γ hJ hdim hVo (hΓd.mono hV) (hΓinj.mono hV) fun τ hτ => hΓZ τ (hV hτ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem measurable_poincareDeepWeight : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem tubeDeep_term (hR : TubeDeepRankOne.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {P : MvPolynomial (Fin (d + 1)) ℂ} {R : ℝ} {y : Fin (d + 1) → ℂ}
    {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ ComplexSets.fibre J A y) (hs : IsSheetAt J A x s)
    (hy : logAbsSq P y < -Real.exp 1) :
    |(Metric.closedBall 0 R).indicator (fun x => tubeWeight P (A *ᵥ x)) x *
        ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y| =
      (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 *
          ((2 / Real.pi) ^ (d + 1) * poincareDeepWeight (deepMap P s I y 0)) := by
  obtain ⟨U, hU, hxU, hsd, -, hsec, -⟩ := hs
  have hAx : A *ᵥ x = y := hx.2
  rw [hAx] at hxU
  have hP : eval y P ≠ 0 := by
    intro h0
    simp only [logAbsSq, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Real.log_zero] at hy
    linarith [Real.exp_pos 1]
  rw [hR n d A P U s y hU hxU hsd (fun y' hy' => (hsec y' hy').1) hP]
  have hw : ∀ I : Fin d → Fin n,
      poincareDeepWeight (deepMap P s I y 0) = (‖eval y P‖ ^ 2 * logAbsSq P y ^ 2)⁻¹ := by
    intro I
    simp only [deepMap, Matrix.cons_val_zero, poincareDeepWeight]
    exact if_pos hy
  have ht : tubeWeight P y = (logAbsSq P y ^ 2)⁻¹ :=
    if_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  simp only [hw]
  by_cases hxR : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
  · rw [Set.indicator_of_mem hxR, Set.indicator_of_mem hxR, hAx, ht, one_mul]
    have hp : 0 < ‖eval y P‖ := norm_pos_iff.2 hP
    have hl : logAbsSq P y ≠ 0 := by linarith [Real.exp_pos 1]
    rw [abs_of_nonneg (by positivity), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    field_simp
  · simp [Set.indicator_of_notMem hxR]

theorem TubeDeepMass.proof (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hc0 : 0 ≤ (2 / Real.pi) ^ (d + 1) := by positivity
  set g : (Fin (d + 1) → ℂ) → ℝ := fun z => (2 / Real.pi) ^ (d + 1) * poincareDeepWeight (z 0) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z =>
    mul_nonneg hc0 (by unfold poincareDeepWeight; split_ifs <;> positivity)
  have hgm : Measurable g :=
    measurable_const.mul (measurable_poincareDeepWeight.comp (measurable_pi_apply 0))
  have hl : Measurable (logAbsSq P) :=
    ((continuous_norm.comp (MvPolynomial.continuous_eval P)).pow 2).measurable.log
  have hF : ∀ y, {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y =
      sheetSum J A (fun x s => (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y := by
    intro y
    by_cases hy : logAbsSq P y < -Real.exp 1
    · rw [Set.indicator_of_mem (show y ∈ {y | logAbsSq P y < -Real.exp 1} from hy), tubeDens, chartAbsDens, sheetSum, sheetSum]
      refine finsum_congr fun x => finsum_congr fun hx => ?_
      split_ifs with h
      · exact tubeDeep_term hR hx h.choose_spec hy
      · rfl
    · rw [Set.indicator_of_notMem (show y ∉ {y | logAbsSq P y < -Real.exp 1} from hy)]
      have hw0 : ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (I : Fin d → Fin n), g (deepMap P s I y) = 0 := by
        intro s I
        simp only [hg, deepMap, Matrix.cons_val_zero, poincareDeepWeight]
        exact mul_eq_zero_of_right _ (if_neg hy)
      simp [sheetSum, hw0]
  obtain ⟨N, hN⟩ := hC n d J A P R hJ hdim hA
  refine ⟨((measurable_tubeDens hA P R _).indicator (measurableSet_lt hl measurable_const)).aestronglyMeasurable,
    ?_⟩
  have hnn : ∀ y, 0 ≤ {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y :=
    fun y => Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y
  show ∫⁻ y, ‖{y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y‖ₑ < ⊤
  calc _ = ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
            ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) :=
        lintegral_congr fun y => by rw [Real.enorm_eq_ofReal (hnn y), hF y]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z) :=
        hN g hgm hg0
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((2 / Real.pi) ^ (d + 1)) *
          ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R},
            ENNReal.ofReal (poincareDeepWeight (z 0))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ (lintegral_congr fun z => ENNReal.ofReal_mul hc0)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW d R))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRingUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def CMRingUnmixed.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsCohenMacaulayLocalRing A],
    ∀ p ∈ associatedPrimes A A, p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def PrimeBranchDimOne.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMParameterQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

def CMParameterQuotient.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      IsCohenMacaulayLocalRing (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMQuotientUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

def CMQuotientUnmixed.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      ∀ p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)),
        p ∈ (Ideal.span (Set.range x)).minimalPrimes ∧
          ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProjectionLocallyInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StModelLocalizationMaximalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ModelLocalizationMaximalPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (P : Ideal (Localization (normalModelSubmonoid M q))), P.IsMaximal →
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        P.comap ((algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))).comp
            (Ideal.Quotient.mk M.ideal)) =
          RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalModelDisc.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧
          Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧ φ 0 = w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ ν : VarBranch I 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder ν f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionUnramifiedGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjectionUnramifiedGeneric.Statement : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (Q : Ideal (MvPolynomial (α ⊕ β) ℂ)) (r : ℕ)
    (q : Fin r → MvPolynomial (α ⊕ β) ℂ) (t : MvPolynomial (α ⊕ β) ℂ), Q.IsPrime →
    (∀ b : β, ∃ F : Polynomial (MvPolynomial α ℂ), F.Monic ∧
      F.eval₂ (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom (X (Sum.inr b)) ∈ Q) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial (α ⊕ β) ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        ∀ v : α ⊕ β → ℂ, (∀ a : α, v (Sum.inl a) = 0) →
          (∀ j, ∑ s, eval w (pderiv s (q j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
end
