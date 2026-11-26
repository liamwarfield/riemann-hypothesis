module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdFiniteNonZeroDivisor.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ P : MaximalSpectrum (curveNormalisation I q),
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) ≠ ⊤) →
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRadialPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

def RadialPrimitive.Statement : Prop :=
  ∀ (e : ℕ) (a : ℝ → ℝ) (t₀ T : ℝ),
    ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 →
      ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ (∃ R : ℝ, ∀ t, R ≤ t → Q t = 0) ∧
        deriv Q 0 = a 0 ∧ deriv (deriv Q) 0 = 0 ∧
        ∀ t, 0 < t →
          deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - radialTransform (e + 1) a t ∧
            deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * radialTransform (e + 1) a t

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceHasBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PlaceHasBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ b, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def SameOrdersLiftCentre.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : NormalModel J)
    (γ γ' : VarBranch J 1 q) (Γ Γ' : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) →
    (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) →
    DifferentiableOn ℂ Γ' (Metric.ball 0 γ'.radius) →
    (∀ τ ∈ Metric.ball 0 γ'.radius, Γ' τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ' τ) = γ'.toFun τ) →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder γ f = branchOrder γ' f) →
      Γ 0 = Γ' 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdDeterminesPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def OrdDeterminesPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P P' : MaximalSpectrum (curveNormalisation I q),
        (∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))) →
        P = P'

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PlaceOnComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ J : Ideal (MvPolynomial (Fin n) ℂ),
        J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧ ringKrullDim (curveLocalRing J q) = 1 ∧
        ∃ P' : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SliceDim.homogeneousComponent_zero_linForm_sub_one {n : ℕ} (ℓ : Fin n → ℂ) :
    homogeneousComponent 0 (linForm ℓ - 1 : MvPolynomial (Fin n) ℂ) = -1 := by
  rw [homogeneousComponent_zero]
  simp [linForm, coeff_sum, coeff_C_mul, coeff_X]

theorem SliceDim.linForm_sub_one_not_mem {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hH : IsHomogIdeal J) (hJ : J ≠ ⊤) (ℓ : Fin n → ℂ) : linForm ℓ - 1 ∉ J := by
  intro h
  have h0 := hH _ h 0
  rw [SliceDim.homogeneousComponent_zero_linForm_sub_one, neg_mem_iff] at h0
  exact hJ ((Ideal.eq_top_iff_one J).mpr h0)

theorem SliceDim.proof : SliceDim.Statement := by
  intro n e J ℓ hJ hdim hℓ
  have hP := hJ.isPrime
  refine le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice ⟨hP, hdim⟩ hJ.isHomog hℓ)
  set r := Ideal.Quotient.mk J (linForm ℓ - 1) with hr_def
  have hr0 : r ≠ 0 := by
    rw [hr_def, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact SliceDim.linForm_sub_one_not_mem hJ.isHomog hP.ne_top ℓ
  have hr : r ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle : J ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_left
  have hkill : Ideal.Quotient.factor hle r = 0 := by
    rw [hr_def, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact le_sup_right (a := J) (Ideal.subset_span rfl)
  have key := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr hkill
  rw [hdim] at key
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      norm_cast at key
    | coe m =>
      have : m + 1 ≤ e + 1 := by exact_mod_cast key
      exact_mod_cast (by omega : m ≤ e)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongMassNearSmall.proof (hReg : RegMassNearSmall.Statement)
    (hVar : VarMassNearSmall.Statement) : LelongMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ _ hIdim hf hfc δ hδ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hSfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  set M : ℝ := ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun W _ => Nat.cast_nonneg _
  have hδ' : 0 < δ / (M + 1) := by positivity
  obtain ⟨U₀, hU₀, hIU₀, hT⟩ := hReg n d J I u φ f hJ hdim hu hφ hIdim hf.continuous hfc δ hδ
  have hW : ∀ W ∈ S, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
      ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
        |varInt W d (fun x => χ x * f x) φ| ≤ δ / (M + 1) := by
    intro W hWm
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    refine hVar n d W I φ f hWp
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hWm)
      (fun i => ?_) hIdim hf.continuous hfc _ hδ'
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, hWJ.trans hSU, hC⟩
  choose! UW hUW hIUW hLW using hW
  have hU : IsOpen (U₀ ∩ ⋂ W ∈ S, UW W) :=
    hU₀.inter (hSfin.isOpen_biInter fun W hW => hUW W hW)
  have hIU : zeroSet I ⊆ U₀ ∩ ⋂ W ∈ S, UW W :=
    Set.subset_inter hIU₀ (Set.subset_iInter₂ fun W hW => hIUW W hW)
  obtain ⟨χ, hχ, hχ01, hχU, V, hV, hIV, hχ1⟩ := exists_cutoff_near_zeroSet I hU hIU
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
  refine ⟨χ, hχ, ⟨V, hV, hIV, hχ1⟩, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hT χ hχ.continuous hχb (hχU.trans Set.inter_subset_left) ε ⟨hε.1, hε.2.le⟩
  · rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    calc |∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) *
            varInt W d (fun x => χ x * f x) φ|
        ≤ ∑ W ∈ hSfin.toFinset, (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * (δ / (M + 1)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun W hW => ?_)
          have hWS : W ∈ S := hSfin.mem_toFinset.1 hW
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hLW W hWS χ hχ.continuous hχb
            (hχU.trans (Set.inter_subset_right.trans (Set.biInter_subset_of_mem hWS))))
            (Nat.cast_nonneg _)
      _ = M * (δ / (M + 1)) := by rw [← Finset.sum_mul]
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

theorem PosPartIndep.proof (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by
  intro n d J A A' f φ hJ hd hA hA' hf hφ

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', IsSheetAt J A' x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A A' f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have hae : ∀ B B' : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B → IsFiniteProjection J B' →
      (∀ x ∈ zeroSet J, (∃ s, IsSheetAt J B x s) → (∃ s', IsSheetAt J B' x s') → ∃ k, x ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B B' hB hB' hc
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h n d J B B' hJ hd hB hB')] with y hy
    refine hS n d J B f φ E y hB hEd fun x hx hs => hc x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  have hint : ∀ B : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B →
      (∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B hB hB2
    rw [lintegral_congr_ae hB2, lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hB (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  rw [hint A hA (hae A A' hA hA' hcov),
    hint A' hA' (hae A' A hA' hA fun x hx h1 h2 => hcov x hx h2 h1)]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (by exact fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) (by
        intro x hx s' _
        rw [hsum x hx.1, Finset.sum_mul])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) (by
        rintro x ⟨-, rfl⟩ s' hs'
        rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchImageNhdOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchImageNhdOffCentre.proof (h₁ : CurveRegularOffCentre.Statement) :
    BranchImageNhdOffCentre.Statement := by
  intro n I q hdim
  obtain ⟨N, hN, hreg⟩ := h₁ n I q hdim
  refine ⟨N, hN, fun c x hx hxq => ?_⟩
  obtain ⟨⟨σ₀, hσ₀, rfl⟩, hxN⟩ := hx
  obtain ⟨A, O, V, g, -, hV, hxV, -, hAg, hZV⟩ := hreg (c.toFun σ₀) ⟨c.mapsTo hσ₀, hxN⟩ hxq

  let e : ℂ → Fin 1 → ℂ := fun τ _ => τ
  have he_diff : Differentiable ℂ e := differentiable_pi.2 fun _ => differentiable_id
  have he_inj : Function.Injective e := fun a b h => congrFun h 0
  have hσe : e (σ₀ 0) = σ₀ := funext fun i => by fin_cases i; rfl
  have hBe : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, e τ ∈ Metric.ball 0 c.radius := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    rwa [pi_norm_const]
  have ht₀ : σ₀ 0 ∈ Metric.ball (0 : ℂ) c.radius := by
    have h := hσ₀
    rw [← hσe, mem_ball_zero_iff, pi_norm_const] at h
    rwa [mem_ball_zero_iff]
  have hB : Metric.ball (0 : ℂ) c.radius ∈ 𝓝 (σ₀ 0) := Metric.isOpen_ball.mem_nhds ht₀
  let f : ℂ → Fin n → ℂ := fun τ => c.toFun (e τ)
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 c.radius) :=
    c.differentiableOn.comp he_diff.differentiableOn hBe
  have hfV : f ⁻¹' V ∈ 𝓝 (σ₀ 0) :=
    (hfd.continuousOn.continuousAt hB).preimage_mem_nhds (by
      show V ∈ 𝓝 (c.toFun (e (σ₀ 0)))
      rw [hσe]
      exact hV.mem_nhds hxV)
  let Δ : Set ℂ := Metric.ball 0 c.radius ∩ f ⁻¹' V
  have hΔ : Δ ∈ 𝓝 (σ₀ 0) := inter_mem hB hfV

  have hfg : ∀ τ ∈ Δ, f τ = g (A (f τ)) := by
    rintro τ ⟨hτB, hτV⟩
    have h : f τ ∈ zeroSet I ∩ V := ⟨c.mapsTo (hBe τ hτB), hτV⟩
    rw [hZV] at h
    obtain ⟨y, hy, hgy⟩ := h
    rw [← hgy, hAg y hy]
  let φ : ℂ → ℂ := fun τ => A (f τ)
  have hφ : AnalyticAt ℂ φ (σ₀ 0) := (A.differentiable.comp_differentiableOn hfd).analyticAt hB

  have hopen : φ '' Δ ∈ 𝓝 (φ (σ₀ 0)) := by
    rcases hφ.eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have hev : ∀ᶠ τ in 𝓝[≠] (σ₀ 0), (φ τ = φ (σ₀ 0) ∧ τ ∈ Δ) ∧ τ ≠ σ₀ 0 :=
        ((hconst.and hΔ).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨τ, ⟨hτφ, hτΔ⟩, hτne⟩ := hev.exists
      have h1 : f τ = f (σ₀ 0) := by
        calc f τ = g (φ τ) := hfg τ hτΔ
          _ = g (φ (σ₀ 0)) := by rw [hτφ]
          _ = f (σ₀ 0) := (hfg (σ₀ 0) (mem_of_mem_nhds hΔ)).symm
      exact hτne (he_inj (c.injOn (hBe τ hτΔ.1) (hBe _ ht₀) h1))
    · exact hle (Filter.image_mem_map hΔ)
  have hφx : φ (σ₀ 0) = A (c.toFun σ₀) := by
    show A (c.toFun (e (σ₀ 0))) = _
    rw [hσe]
  refine ⟨V ∩ A ⁻¹' (φ '' Δ), inter_mem (hV.mem_nhds hxV)
    (A.continuous.continuousAt.preimage_mem_nhds (hφx ▸ hopen)), ?_⟩
  rintro y ⟨hyZ, hyV, τ, hτΔ, hτy⟩
  have hy : y ∈ g '' O := hZV ▸ ⟨hyZ, hyV⟩
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨e τ, hBe τ hτΔ.1, ?_⟩
  calc c.toFun (e τ) = f τ := rfl
    _ = g (φ τ) := hfg τ hτΔ
    _ = g w := by rw [hτy, hAg w hw]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Metric Filter Topology Set

noncomputable section

namespace BranchInComponent

theorem differentiable_eval {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_open_prod_ne_zero {k : ℕ} {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : U.Nonempty) {ι : Type*} (s : Finset ι) (f : ι → (Fin k → ℂ) → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) (hnz : ∀ i ∈ s, ¬ EqOn (f i) 0 U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, ∏ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, subset_rfl, hU, hne, fun x _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨V, hVU, hVo, ⟨z, hz⟩, hV⟩ :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hnz i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨w, hwV, hw⟩ : ∃ w ∈ V, f a w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hnz a (Finset.mem_insert_self a s)
        (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hVU hz) ?_)
      filter_upwards [hVo.mem_nhds hz] with x hx using hcon x hx
    refine ⟨V ∩ f a ⁻¹' {0}ᶜ, inter_subset_left.trans hVU,
      (hfa.continuousOn.mono hVU).isOpen_inter_preimage hVo isOpen_compl_singleton, ⟨w, hwV, hw⟩, ?_⟩
    rintro x ⟨hxV, hx⟩
    rw [Finset.prod_insert ha]
    exact mul_ne_zero hx (hV x hxV)

theorem proof : BranchInComponent.Statement := by
  classical
  intro n I k q c
  by_contra hcon
  push Not at hcon
  set B : Set (Fin k → ℂ) := ball 0 c.radius with hB
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball (0 : Fin k → ℂ) c.radius).isPreconnected
  have hBne : B.Nonempty := ⟨0, mem_ball_self c.radius_pos⟩
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hch : ∀ J : I.minimalPrimes, ∃ g ∈ (J : Ideal (MvPolynomial (Fin n) ℂ)),
      ¬ EqOn (fun τ => eval (c.toFun τ) g) 0 B := by
    intro J
    have hJ := hcon J J.2
    simp only [Set.MapsTo, not_forall, exists_prop] at hJ
    obtain ⟨τ, hτB, hτZ⟩ := hJ
    simp only [zeroSet, mem_ofPred_eq, not_forall] at hτZ
    obtain ⟨g, hg, hgτ⟩ := hτZ
    exact ⟨g, hg, fun h => hgτ (h hτB)⟩
  choose g hgJ hgnz using hch
  let _ : Fintype I.minimalPrimes := hfin.fintype
  have han : ∀ J : I.minimalPrimes, AnalyticOnNhd ℂ (fun τ => eval (c.toFun τ) (g J)) B := fun J =>
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo
      ((differentiable_eval (g J)).comp_differentiableOn c.differentiableOn)
  obtain ⟨V, hVB, -, ⟨x, hx⟩, hV⟩ := exists_open_prod_ne_zero hBo hBc hBne Finset.univ
    (fun J τ => eval (c.toFun τ) (g J)) (fun J _ => han J) (fun J _ => hgnz J)

  set G : MvPolynomial (Fin n) ℂ := ∏ J : I.minimalPrimes, g J with hG
  have hGrad : G ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro J hJ
    rw [hG, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ⟨J, hJ⟩)]
    exact Ideal.mul_mem_right _ _ (hgJ ⟨J, hJ⟩)
  obtain ⟨N, hN⟩ := hGrad
  have h0 := c.mapsTo (hVB hx) _ hN
  rw [map_pow, hG, map_prod] at h0
  exact hV x hx (pow_eq_zero_iff'.1 h0).1

end BranchInComponent

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchInOneBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem isPreconnected_punctured_ball {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by
  have hH : IsPreconnected {z : ℂ | z.re < Real.log R} := (convex_halfSpace_re_lt _).isPreconnected
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)
    · rintro ⟨hw, hw0⟩
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hw0) hw
  rw [← himage]
  exact hH.image _ Complex.continuous_exp.continuousOn

theorem PuncturedBranchInOneBranch.proof (h₁ : BranchImageNhdOffCentre.Statement) :
    PuncturedBranchInOneBranch.Statement := by
  intro n I q m c ν ρ _ hdim hρ hcov hdisj
  obtain ⟨N, hN, hNc⟩ := h₁ n I q hdim
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]
  have hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius := fun τ hτ ↦ by
    rwa [Metric.mem_ball, dist_zero_right, hnorm]
  have h0r : ‖(0 : ℂ)‖ < ν.radius := by simpa using ν.radius_pos

  have hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ := fun τ hτ ↦
    (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp
      (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N :=
    (hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  obtain ⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius :=
    ⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  let D : Set ℂ := Metric.ball 0 R \ {0}
  have hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R := fun τ hτ ↦
    ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩
  have hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q := by
    intro τ hτ h
    have h' := ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)
    exact (norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)

  let Vb : Fin m → Set ℂ := fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVo : ∀ b, IsOpen (Vb b) := by
    intro b
    rw [isOpen_iff_mem_nhds]
    rintro τ ⟨hτD, hτb⟩
    have hτN : ν.toFun (fun _ ↦ τ) ∈ N := hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)
    obtain ⟨U, hU, hUc⟩ := hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)
    filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU]
      with σ hσD hσU
    exact ⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩
  have hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b') := fun b b' hbb ↦
    Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)
  have hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b := fun τ hτ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))
    exact ⟨b, hτ, hb⟩

  have hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp [hR0.ne']
  obtain ⟨b, hb⟩ := hcovD _ hτ₀
  have hsub : D ⊆ Vb b := by
    refine (isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b)
      (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩
    · exact Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')
    · intro τ hτ
      obtain ⟨b', hb'⟩ := hcovD τ hτ
      by_cases h : b' = b
      · exact Or.inl (h ▸ hb')
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)
  refine ⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩
  · rwa [Metric.mem_ball, dist_zero_right]
  · simpa using norm_pos_iff.1 hτ0

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermFiniteProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermFiniteProjection.exists_of_step (hStep : PrimeGermProjectionStep.Statement) :
    ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime →
      ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
  have key : ∀ (n : ℕ) (σ : Type) [Fintype σ], Fintype.card σ = n → ∀ (w : σ → ℂ) (P : Ideal (holGerms w)),
      P.IsPrime → ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ _ hn w P hP
      by_cases h0 : P = ⊥
      · subst h0
        exact isFiniteGermProjection_bot w
      · exact hStep σ w P hP h0 fun τ _ hτ v Q hQ => ih _ (hn ▸ hτ) τ rfl v Q hQ
  intro σ _ w P hP
  exact key _ σ rfl w P hP

theorem PrimeGermFiniteProjection.proof (hStep : PrimeGermProjectionStep.Statement)
    (hFF : GermProjectionFunctionForm.Statement) : PrimeGermFiniteProjection.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, hA⟩ := PrimeGermFiniteProjection.exists_of_step hStep σ w _ hP
  exact ⟨d, A, hFF σ w k p d A hp hA⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem BranchPlace.proof (h₁ : BranchInComponent.Statement) (h₂ : PrimeBranchPlace.Statement)
    (h₃ : MinimalPrimePlace.Statement) : BranchPlace.Statement := by
  intro n I q c hrad hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2

  let c' : VarBranch J 1 q :=
    { radius := c.radius, radius_pos := c.radius_pos, toFun := c.toFun, differentiableOn := c.differentiableOn,
      injOn := c.injOn, map_zero := c.map_zero, mapsTo := hmaps }

  have hJq : J ≤ RingHom.ker (eval q) := by
    intro g hg
    have h0 := hmaps (Metric.mem_ball_self c.radius_pos) g hg
    rw [c.map_zero] at h0
    exact RingHom.mem_ker.2 h0

  have hdimJ : ringKrullDim (curveLocalRing J q) ≤ 1 := by
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.map_mono hIJ
    rw [← hdim]
    exact ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q) (Ideal.Quotient.factor_surjective hle)
  obtain ⟨P', hP'⟩ := h₂ n J q c' hJp hdimJ
  obtain ⟨P, hP⟩ := h₃ n I J q hrad hJ hJq P'
  exact ⟨P, fun f ↦ (hP f).trans (hP' f)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem TubeCollarMass.proof (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  obtain ⟨C, hCle⟩ := hC n d J A P R hJ hdim hA hP
  have hψ : ∀ k : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) k) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)

  have hI : Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    obtain ⟨K, hK, hle⟩ := hM n (d + 1) J A (fun _ => euclPot) R hJ hdim hA hψ
    have hmeas := (SheetSumMeasurable.proof n (d + 1) J A
      ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) (fun _ => euclPot) hJ hdim hA
      (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hbd : Bornology.IsBounded
        (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
      (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
    have h1 := hle (fun _ => 1) measurable_const
    simp only [enorm_one, setLIntegral_one] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
    exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hF n (d + 1) J hJ hdim R')

  have hl : Measurable (logAbsSq P) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval P).norm.pow 2).measurable
  refine (hI.const_mul C).mono'
    (((measurable_tubeDens hA P R _).indicator (measurableSet_le measurable_const hl)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end
