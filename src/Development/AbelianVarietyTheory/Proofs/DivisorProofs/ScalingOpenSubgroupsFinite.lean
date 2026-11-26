module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BoxCosetSum

variable {F : Type} [Field F] [NumberField F]

theorem continuous_evalV' (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem eventually_evalV_mem_integers (x : FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ v.adicCompletionIntegers F := x.2

theorem isOpen_box (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
  have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 hBf
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have e : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} =
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hT.toFinset, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ⁻¹' (B v : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun v => hBO v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F
      · have : x v ∈ (B v : Set (v.adicCompletion F)) := by rw [hv]; exact h1 v
        exact this
      · exact h2 v hv
  rw [e]
  exact hO.inter (isOpen_biInter_finset fun v _ => (hBo v).preimage (continuous_evalV' v))

def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add (f := _)]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)

theorem mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl

theorem isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)

theorem finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2

theorem eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ B hBo hBO hBf g hg hinv
  classical
  set U := boxSub κ B with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_boxSub κ B hBo hBO hBf
  have hK : IsCompact (tsupport g) := hg
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finprod_indicator_eq κ B hBO hBf]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · rw [Set.indicator_of_mem (show x ∈ {z | z - r0 ∈ boxSub κ B} from hxr0), mul_one]
      have := hinv r0 (x - r0) hxr0
      rwa [add_sub_cancel] at this
    · intro r hr hne
      have hm : x ∉ {z | z - r ∈ boxSub κ B} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {z | z - r ∈ boxSub κ B} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.BoxCosetSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFiniteStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_open_subgroups_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator | exact GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator | (intros; apply GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

def term (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem u_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hy this

theorem hasDerivAt_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y => term σ ν a b m y t)
      (-(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t) y := by
  have hu := u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (t : ℂ)
  have h2 : HasDerivAt (fun y : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a)
      ((a : ℂ) * ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ (a - 1) * (-(((t : ℂ) + (y : ℂ) * I) ^ 2)⁻¹ * I)) y :=
    (((hasDerivAt_inv hu).comp y h1).pow a)
  have h3 : HasDerivAt (fun y : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * y : ℝ) : ℂ) y := by
    have : HasDerivAt (fun y : ℝ => t ^ 2 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add (t ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp y h3
  have h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ m) ((m : ℂ) * (y : ℂ) ^ (m - 1)) y :=
    (hasDerivAt_pow m (y : ℂ)).comp_ofReal
  have h := ((h2.mul h4).mul h5).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  refine h.congr_deriv ?_
  simp only [term, Function.comp_def, Pi.mul_apply, ← inv_pow]
  generalize ((t : ℂ) + (y : ℂ) * I)⁻¹ = v
  rw [show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  rcases a with _ | a <;> rcases m with _ | m <;>
    simp only [Nat.add_sub_cancel, Nat.zero_sub, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add,
      neg_zero, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> push_cast <;> ring

theorem continuous_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (term σ ν a b m y) := by
  unfold term
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a :=
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).inv₀ (u_ne hy)).pow a
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact ((h1.mul h2).mul continuous_const).mul (by fun_prop)

theorem norm_term_le (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a b m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) : ∃ bd : ℝ → ℝ, MeasureTheory.Integrable bd ∧
      ∀ t, ∀ y ∈ Metric.ball y₀ (|y₀| / 2), ‖term σ ν a b m y t‖ ≤ bd t := by
  have hσ' : -1 / 2 < σ.re := hσ
  set c := |y₀| / 2 with hc
  have hc0 : 0 < c := by positivity
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (c ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine ⟨fun t => (3 * c) ^ m * κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2), ?_, ?_⟩
  · exact (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  intro t y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hyl : c ≤ |y| := by
    have := abs_sub_abs_le_abs_sub y₀ y
    rw [abs_sub_comm] at this; rw [hc]; linarith
  have hyu : |y| ≤ 3 * c := by
    have := abs_sub_abs_le_abs_sub y y₀
    rw [hc]; linarith
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hyl; linarith
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  have hnorm : ‖term σ ν a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
    unfold term
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 2
    simp
    ring
  rw [hnorm]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ c ^ 2 := min_le_right _ _
    have h3 : c ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hyl 2
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  have hB : |y| ^ m ≤ (3 * c) ^ m := pow_le_pow_left₀ (abs_nonneg y) hyu m
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * (3 * c) ^ m :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring

theorem ne_zero_of_mem_ball {y₀ y : ℝ} (hy₀ : y₀ ≠ 0) (hy : y ∈ Metric.ball y₀ (|y₀| / 2)) : y ≠ 0 := by
  rintro rfl
  rw [Metric.mem_ball, Real.dist_eq, zero_sub, abs_neg] at hy
  have : 0 < |y₀| := abs_pos.2 hy₀
  linarith

theorem integrable_term (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) : MeasureTheory.Integrable (term σ ν a b m y) := by
  obtain ⟨bd, hbd, h⟩ := norm_term_le σ hσ ν a b m hab hy
  exact hbd.mono' (continuous_term σ ν a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => h t y (Metric.mem_ball_self (by positivity)))

def intT (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) : ℂ := ∫ t : ℝ, term σ ν a b m y t

theorem hasDerivAt_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) :
    HasDerivAt (intT σ ν a b m)
      (-(a : ℂ) * I * intT σ ν (a + 1) b m y₀ + 2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀
        + (m : ℂ) * intT σ ν a b (m - 1) y₀) y₀ := by
  obtain ⟨b1, hb1, h1⟩ := norm_term_le σ hσ ν (a + 1) b m (by omega) hy₀
  obtain ⟨b2, hb2, h2⟩ := norm_term_le σ hσ ν a (b + 1) (m + 1) (by omega) hy₀
  obtain ⟨b3, hb3, h3⟩ := norm_term_le σ hσ ν a b (m - 1) hab hy₀
  have i1 := integrable_term σ hσ ν m (a := a + 1) (b := b) (by omega) hy₀
  have i2 := integrable_term σ hσ ν (m + 1) (a := a) (b := b + 1) (by omega) hy₀
  have i3 := integrable_term σ hσ ν (m - 1) (a := a) (b := b) hab hy₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y t => term σ ν a b m y t)
    (F' := fun y t => -(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t)
    (bound := fun t => ‖-(a : ℂ) * I‖ * b1 t + ‖2 * (-σ - (b : ℂ))‖ * b2 t + ‖(m : ℂ)‖ * b3 t)
    (Metric.ball_mem_nhds y₀ (by positivity))
    (Filter.eventually_of_mem (isOpen_ne.mem_nhds hy₀) fun y hy => (continuous_term σ ν a b m hy).aestronglyMeasurable)
    (integrable_term σ hσ ν m hab hy₀)
    ((((continuous_term σ ν _ _ _ hy₀).const_mul _).add ((continuous_term σ ν _ _ _ hy₀).const_mul _)).add
      ((continuous_term σ ν _ _ _ hy₀).const_mul _)).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t y hy => by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
        rw [norm_mul] <;> gcongr
      · exact h1 t y hy
      · exact h2 t y hy
      · exact h3 t y hy)
    (((hb1.const_mul _).add (hb2.const_mul _)).add (hb3.const_mul _))
    (MeasureTheory.ae_of_all _ fun t y hy => hasDerivAt_term σ ν a b m (ne_zero_of_mem_ball hy₀ hy) t)
  have k2 := key.2
  have hI : (∫ t, (-(a : ℂ) * I * term σ ν (a + 1) b m y₀ t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y₀ t
        + (m : ℂ) * term σ ν a b (m - 1) y₀ t)) = -(a : ℂ) * I * intT σ ν (a + 1) b m y₀ +
        2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀ + (m : ℂ) * intT σ ν a b (m - 1) y₀ := by
    unfold intT
    rw [MeasureTheory.integral_add _ (i3.const_mul _), MeasureTheory.integral_add (i1.const_mul _) (i2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact (i1.const_mul _).add (i2.const_mul _)
  rw [hI] at k2
  exact k2

theorem contDiffOn_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ∀ n : ℕ, ∀ a b m : ℕ, 2 ≤ a + 2 * b → ContDiffOn ℝ n (intT σ ν a b m) {y | y ≠ 0} := by
  intro n
  induction n with
  | zero =>
    intro a b m hab
    exact contDiffOn_zero.2 fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro a b m hab
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne]
    refine ⟨fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have c1 := (contDiffOn_const (c := -(a : ℂ) * I)).mul (ih (a + 1) b m (by omega))
    have c2 := (contDiffOn_const (c := 2 * (-σ - (b : ℂ)))).mul (ih a (b + 1) (m + 1) (by omega))
    have c3 := (contDiffOn_const (c := (m : ℂ))).mul (ih a b (m - 1) hab)
    refine ((c1.add c2).add c3).congr fun y hy => ?_
    exact (hasDerivAt_intT σ hσ ν m hab hy).deriv

theorem hTrans_eq (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : hTrans σ ν y = intT σ ν 2 0 0 y := by
  unfold hTrans intT
  congr 1
  funext t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold term phi
  rw [hnu]
  simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
  congr 2
  have hs : 0 < Real.sqrt (t ^ 2 + y ^ 2) := Real.sqrt_pos.2 hQ
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast hQ.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log hQ.le, Real.log_sqrt hQ.le]
  congr 1
  push_cast
  ring

theorem contDiffOn_hTrans (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ContDiffOn ℝ ∞ (hTrans σ ν) {y | y ≠ 0} := by
  refine (contDiffOn_infty.2 fun n => contDiffOn_intT σ hσ ν n 2 0 0 (by norm_num)).congr fun y hy => ?_
  exact hTrans_eq σ ν hy

end GlobalTheory.HeckeTwo.TermSmooth

namespace GlobalTheory.HeckeTwo

theorem fTerm_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
    ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  intro F _ _ b ν hb σ hσ
  unfold fTerm
  refine contDiffOn_prod fun τ _ => ?_
  have he : ContDiff ℝ ∞ (fun z : Emb F → ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) τ))))).cexp
  have hg : ContDiff ℝ ∞ (fun z : Emb F → ℂ => τ b * (z τ).im) :=
    contDiff_const.mul (Complex.imCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) τ))
  have hh : ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => hTrans σ (τ ν) (τ b * (z τ).im)) (upperHalf F) :=
    (TermSmooth.contDiffOn_hTrans σ hσ (τ ν)).comp hg.contDiffOn
      fun z hz => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact he.contDiffOn.mul hh

end GlobalTheory.HeckeTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTermStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
  ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_contDiffOn | exact GlobalTheory.HeckeTwo.fTerm_contDiffOn | (intros; apply GlobalTheory.HeckeTwo.fTerm_contDiffOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityExpZModAdditiveCharacterProperties
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
open scoped Matrix Nat

namespace GlobalTheory.GaussComplexForm

theorem exists_schwartz_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  intro V _ _ _ Q c hc hQ
  set B : V →L[ℝ] V →L[ℝ] ℂ := -Q with hBdef
  have hBapp : ∀ x y, B x y = -(Q x y) := fun x y => rfl
  have hB : ∀ x, (B x x).re ≤ -(c * ‖x‖ ^ 2) := by
    intro x; rw [hBapp, Complex.neg_re]; linarith [hQ x]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => Complex.exp (B y y)) :=
    Complex.contDiff_exp.comp hq
  refine ⟨⟨fun y => Complex.exp (B y y), hg, ?_⟩, fun x => ?_, fun x p => ?_⟩
  · intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp c hc (k + 2 * n)
    refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
    have hx0 := norm_nonneg x
    have hB0 := norm_nonneg B
    have hfb := GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le B c hB n x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : V => Complex.exp (B y y)) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
          gcongr
          linarith
      _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
          rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
            rw [mul_pow, pow_mul], pow_add]; ring
      _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0
  · show Complex.exp (B x x) = _
    rw [hBapp]
  · have h1 := (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    have h2 : HasFDerivAt (fun y : V => Complex.exp (B y y)) _ x := h1.cexp
    show fderiv ℝ (fun y : V => Complex.exp (B y y)) x p = -(Q x p + Q p x) * Complex.exp (B x x)
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, smul_eq_mul, hBapp]
    ring

end GlobalTheory.GaussComplexForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegFormStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_eq_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  first | exact @GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | exact GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | (intros; apply GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobDeriv

def FrobTwist (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (M : Type) : Type := M

variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]

instance : AddCommGroup (FrobTwist K p M) := inferInstanceAs (AddCommGroup M)

noncomputable instance : Module K (FrobTwist K p M) :=
  Module.compHom M (frobenius K p)

theorem twist_smul (c : K) (m : FrobTwist K p M) :
    c • m = (c ^ p • (show M from m) : M) := by
  show (frobenius K p c) • (show M from m) = _
  rw [frobenius_def]

end GlobalTheory.DI.FrobDeriv

open GlobalTheory.DI.FrobDeriv in
theorem GlobalTheory.DI.frobDeriv_factors_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  intro K _ M _ _ p _ _ φ hφ
  let ψ : K →ₗ[ℤ] FrobTwist K p M := (φ : K →+ M).toIntLinearMap
  have hone : φ 1 = 0 := by
    have h := hφ 1 1
    simp only [mul_one, one_pow, one_smul] at h
    have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  let D : Derivation ℤ K (FrobTwist K p M) :=
    { toLinearMap := ψ
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        show φ (a * b) = a • (show FrobTwist K p M from φ b) + b • (show FrobTwist K p M from φ a)
        rw [twist_smul, twist_smul, hφ]; rfl }
  refine ⟨(D.liftKaehlerDifferential).toAddMonoidHom, ?_, ?_⟩
  · intro c v
    show D.liftKaehlerDifferential (c • v) = _
    rw [LinearMap.map_smul, twist_smul]
    rfl
  · intro a
    show D.liftKaehlerDifferential (KaehlerDifferential.D ℤ K a) = φ a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehlerStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusDerivation_factors_through_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  first | exact @GlobalTheory.DI.frobDeriv_factors_kaehler | exact GlobalTheory.DI.frobDeriv_factors_kaehler | (intros; apply GlobalTheory.DI.frobDeriv_factors_kaehler <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpan
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem finrank_addValuationInteger_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X →
    finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) =>
      (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  intro C _ v N X hX
  let ι : (Fin N → Int0 v) →ₗ[Int0 v] (Fin N → C) := (Algebra.linearMap (Int0 v) C).compLeft (Fin N)
  have hι : Function.Injective ι := by
    intro x y h; funext i; exact Subtype.ext (congrFun h i)
  let L : X →ₗ[Int0 v] (Fin N → C) := ι ∘ₗ X.subtype
  have hL : Function.Injective L := hι.comp Subtype.val_injective
  have hInt : v.toValuation.Integers (Int0 v) := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      change 0 ≤ v (x : C)
      exact (mem_addValuationIntegerRing_iff v _).mp x.property
    · intro x hx
      change 0 ≤ v x at hx
      exact ⟨⟨x, (mem_addValuationIntegerRing_iff v x).mpr hx⟩, rfl⟩
  have : ValuationRing (Int0 v) := ValuationRing.of_integers _ hInt
  have : IsFractionRing (Int0 v) C := hInt.isFractionRing
  have : Module.IsTorsionFree (Int0 v) X := inferInstance
  have : Module.Free (Int0 v) X := free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  let b := Module.Free.chooseBasis (Int0 v) X
  have hli : LinearIndependent (Int0 v) (L ∘ b) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hliC : LinearIndependent C (L ∘ b) := (LinearIndependent.iff_fractionRing (Int0 v) C).mp hli
  have hspan : Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (X : Set (Fin N → Int0 v))) = Submodule.span C (Set.range (L ∘ b)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : L ⟨x, hx⟩ ∈ Submodule.span (Int0 v) (L '' Set.range b) :=
        Submodule.apply_mem_span_image_of_mem_span L (by rw [b.span_eq]; trivial)
      rw [← Set.range_comp] at h1
      exact Submodule.span_le_restrictScalars (Int0 v) C _ h1
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(b k : Fin N → Int0 v), (b k).2, rfl⟩
  rw [hspan, finrank_span_eq_card hliC, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpanStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_int0_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X → finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  first | exact @GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | exact GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | (intros; apply GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentials
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem _root_.GlobalTheory.DI.inTot_delta_Dtot : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by
  intro ι _ E _ d T hmono m c hc
  unfold _root_.GlobalTheory.DI.InTot at hc
  obtain ⟨h0, hmem, hzero⟩ := hc
  have hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0 := by
    unfold _root_.GlobalTheory.DI.delta; simp
  have hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 →
      _root_.GlobalTheory.DI.delta c t ∈ T q t := by
    intro q t hqt
    unfold _root_.GlobalTheory.DI.delta
    refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hq : q + (t.erase i).card = m := by omega
    rcases (t.erase i).eq_empty_or_nonempty with he | hne
    · rw [he, h0]; exact zero_mem _
    · exact hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)
  have hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0 := by
    intro t ht
    unfold _root_.GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    rw [hzero _ (by omega), smul_zero]
  refine ⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.DI.Dtot; simp [hδ0, h0]
  · intro q t hqt
    unfold _root_.GlobalTheory.DI.Dtot
    refine add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)
    rcases q with _ | q
    · rw [hzero t (by omega), map_zero]; exact zero_mem _
    · exact hd q t _ (hmem q t (by omega))
  · intro t ht
    unfold _root_.GlobalTheory.DI.Dtot
    rw [hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentialsStatement
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → ∀ m c, InTot T m c → InTot T (m + 1) (delta c) ∧ ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → InTot T (m + 1) (Dtot d c)) := by
  first | exact @GlobalTheory.DI.inTot_delta_Dtot | exact GlobalTheory.DI.inTot_delta_Dtot | (intros; apply GlobalTheory.DI.inTot_delta_Dtot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWords
open MeasureTheory

namespace GlobalTheory

theorem sobolev_iterated_one_parameter_subgroups_words : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  intro G _ _ _ N c s hs hc
  obtain ⟨enc, hinj, h1, h2⟩ : ∃ enc : List (Fin N) → ℝ, Function.Injective enc ∧
      (∀ l, 1 ≤ ‖enc l‖) ∧ ∀ l, ‖enc l‖ ≤ 2 := by
    have hpos : ∀ l : List (Fin N), (0 : ℝ) < 1 / ((Encodable.encode l : ℝ) + 1) := fun l => by
      positivity
    have hle : ∀ l : List (Fin N), 1 / ((Encodable.encode l : ℝ) + 1) ≤ 1 := fun l => by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (Encodable.encode l : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨fun l => 1 + 1 / ((Encodable.encode l : ℝ) + 1), ?_, fun l => ?_, fun l => ?_⟩
    · intro a b hab
      have h : (1 : ℝ) / ((Encodable.encode a : ℝ) + 1) = 1 / ((Encodable.encode b : ℝ) + 1) :=
        add_left_cancel hab
      rw [one_div, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
      exact Encodable.encode_injective h
    · have := hpos l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    · have := hpos l
      have := hle l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
  have hdec : ∀ l, Function.invFun enc (enc l) = l := Function.leftInverse_invFun hinj
  have hK : 0 ≤ (2 / s + 2 * s * 2 ^ 2) ^ N := by positivity
  refine ⟨(2 / s + 2 * s * 2 ^ 2) ^ N * 4, by positivity, ?_⟩
  intro F hF hD y M hM
  have hM0 : 0 ≤ M :=
    le_trans (integral_nonneg fun t => by positivity) (hM [] (Nat.zero_le _))
  have main := sobolev_iterated_one_parameter_subgroups G ℝ ℂ N 0 c
    (fun p => enc '' {l | l.length ≤ p}) (fun i u => enc (i :: Function.invFun enc u))
    (fun u => F (Function.invFun enc u)) s 2 M y hs (by norm_num) hM0 hc
    (fun p q hpq => Set.image_mono fun l hl => le_trans hl hpq) ?_ ?_ ?_ (enc [])
    ⟨[], Nat.le_refl 0, rfl⟩
  · rw [hdec] at main
    have h4 : ‖enc []‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h2 _) 2
    calc _ ≤ _ := main
      _ ≤ (2 / s + 2 * s * 2 ^ 2) ^ N * M * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hM0)
      _ = _ := by ring
  · rintro p _ ⟨l, hl, rfl⟩
    simp only [hdec]
    exact ⟨hF l, fun i => ⟨⟨i :: l, Nat.succ_le_succ hl, rfl⟩, hD l i⟩⟩
  · rintro p _ _ ⟨l, hl, rfl⟩ i
    have := h1 l
    have := h2 (i :: Function.invFun enc (enc l))
    linarith
  · rintro _ ⟨l, hl, rfl⟩
    simp only [hdec]
    have hl' : l.length ≤ N := by simpa using hl
    exact (hM l hl').trans (le_mul_of_one_le_right hM0 (one_le_pow₀ (h1 l)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWordsStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_norm_le_mul_of_iterated_one_parameter_integral_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  first | exact @GlobalTheory.sobolev_iterated_one_parameter_subgroups_words | exact GlobalTheory.sobolev_iterated_one_parameter_subgroups_words | (intros; apply GlobalTheory.sobolev_iterated_one_parameter_subgroups_words <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeft
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoMul

theorem wirt_const_mul {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirt τ bar (fun z => c * g z) = fun z => c * wirt τ bar g z := by
  funext z
  have h : fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z := by
    have := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) z
    simpa [Pi.smul_def, smul_eq_mul] using this
  simp only [wirt, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtWord_const_mul {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirtWord ws (fun z => c * g z) = fun z => c * wirtWord ws g z := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]

theorem isGood_mul (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ)
    (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ) (hk : DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane)
    (hP : GlobalTheory.HeckeTwo.IsGood P) : GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩
  simp only [wirtWord_const_mul]
  exact hk.mul (h2 w z hz)

end GlobalTheory.HeckeTwoMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeftStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left : ∀ (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ) (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  first | exact @GlobalTheory.HeckeTwoMul.isGood_mul | exact GlobalTheory.HeckeTwoMul.isGood_mul | (intros; apply GlobalTheory.HeckeTwoMul.isGood_mul <;> assumption)
end
end
