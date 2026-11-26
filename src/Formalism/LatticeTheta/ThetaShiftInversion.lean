module

public import Formalism.LatticeTheta.Statement

@[expose] public section

section -- merged from Formalism.LatticeTheta.LatticeSummableDecay
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def LatticeSummableDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (g : V → ℂ) (b : ℝ),
    (Module.finrank ℝ V : ℝ) < b → g =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Summable (fun l : L => g l)

def Periodization [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b → f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    Integrable f ∧ (∀ x : V, Summable (fun l : Λ => f ((l : V) + x))) ∧
    Continuous (fun x : V => ∑' l : Λ, f ((l : V) + x)) ∧
    ∀ (l₀ : Λ) (x : V), ∑' l : Λ, f ((l : V) + ((l₀ : V) + x)) = ∑' l : Λ, f ((l : V) + x)

def UnfoldCoeff [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Integrable f →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume → ∀ μ ∈ dual Λ,
      ∫ y in D, (∑' l : Λ, f ((l : V) + y)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ

def LatticeFourierSeries [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (G : V → ℂ), Continuous G →
    (∀ (l : Λ) (x : V), G ((l : V) + x) = G x) →
    ∀ D : Set V, IsAddFundamentalDomain Λ D volume →
    Summable (fun μ : dual Λ =>
      ∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) →
    ∀ x : V, HasSum (fun μ : dual Λ =>
        (ZLattice.covolume Λ : ℂ)⁻¹ *
          (∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ)))) *
          Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))
      (G x)

def SchwartzDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (f : 𝓢(V, ℂ)) (b : ℝ),
    (f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) ∧
    (𝓕 (f : V → ℂ) : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b))

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.GaussSchwartz
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem schwartz_decay_gaussian : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.LatticeSummableDecay
open MeasureTheory Filter Asymptotics Topology

noncomputable section

namespace Formalism.H

theorem lattice_summable_decay (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeSummableDecay V := by
  intro L _ _ g b hb hg
  obtain ⟨C, hC⟩ := hg.bound
  have hrank : Module.finrank ℤ L = Module.finrank ℝ V := ZLattice.rank ℝ L
  have hsum : Summable fun z : L => ‖z‖ ^ (-b) :=
    ZLattice.summable_norm_rpow L (-b) (by rw [hrank]; linarith)
  have ht : Tendsto (Subtype.val : L → V) cofinite (cocompact V) :=
    L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  filter_upwards [ht.eventually hC] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hz
  exact hz

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.Assembly
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_exp_two_pi_I_mul (r : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem poissonDecay_of (hD : DualIsLattice (V := V)) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) :
    PoissonDecay (V := V) := by
  intro Λ _ _ f hf b hb hfO hFO x
  obtain ⟨hdd, hdz⟩ := hD Λ
  haveI := hdd
  haveI : IsZLattice ℝ (dual Λ) := hdz

  have hphase : (fun v : V => (𝓕 f : V → ℂ) v * Complex.exp (2 * Real.pi * Complex.I * (⟪v, x⟫ : ℝ)))
      =O[cocompact V] (fun v => ‖v‖ ^ (-b)) := by
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun v => ?_)).trans hFO
    rw [norm_mul, norm_exp_two_pi_I_mul, mul_one, one_mul]
  have hsum := h1 (dual Λ) _ b hb hphase
  refine ⟨hsum, ?_⟩
  obtain ⟨hint, hper, hcont, hinv⟩ := h2 Λ f hf b hb hfO

  let B := Module.Free.chooseBasis ℤ Λ
  have hD' := ZLattice.isAddFundamentalDomain B (volume : Measure V)
  have hcoef : ∀ μ : dual Λ,
      ∫ y in ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ Λ), (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ :=
    fun μ => h3 Λ f hint _ hD' μ μ.2
  have hFs : Summable (fun μ : dual Λ => (𝓕 f : V → ℂ) μ) := h1 (dual Λ) _ b hb hFO
  have hG := h4 Λ (fun y => ∑' l : Λ, f ((l : V) + y)) hcont
    (fun l y => by simpa using hinv l y) _ hD' (by simpa only [hcoef] using hFs) x
  simp only [hcoef] at hG
  have hval : (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ, (𝓕 f : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) = ∑' l : Λ, f ((l : V) + x) := by
    rw [← tsum_mul_left, ← hG.tsum_eq]
    congr 1; funext μ; ring
  rw [hval]
  exact (hper x).hasSum

theorem poissonSchwartz_of (hP : PoissonDecay (V := V)) (h6 : SchwartzDecay V) :
    PoissonSchwartz (V := V) := by
  intro Λ _ _ f x
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  exact hP Λ f f.continuous _ hd (h6 f _).1 (h6 f _).2 x

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.UnfoldCoeff
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma unfoldCoeff_char_periodic (Λ : Submodule ℤ V) {μ : V} (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by
  obtain ⟨k, hk⟩ := Submodule.mem_one.1 ((LinearMap.BilinForm.mem_dualSubmodule _).1 hμ l l.2)
  have hk' : ⟪μ, (l : V)⟫ = (k : ℝ) := by simpa using hk.symm
  rw [inner_add_right, hk']
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + (⟪μ, y⟫ : ℂ))) =
      -(2 * (Real.pi : ℂ) * Complex.I * (⟪μ, y⟫ : ℂ)) + -(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_add, ← Int.cast_neg, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem unfoldCoeff_main (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ)
    (hf : Integrable f) (D : Set V) (hD : IsAddFundamentalDomain Λ D volume) (μ : V)
    (hμ : μ ∈ dual Λ) :
    ∫ y in D, (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ := by
  haveI : VAddInvariantMeasure Λ V volume := ⟨fun l s _ => measure_preimage_add volume (l : V) s⟩
  set e : V → ℂ := fun x => Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, x⟫ : ℝ))) with he
  have hper : ∀ (l : Λ) (y : V), e ((l : V) + y) = e y := fun l y =>
    unfoldCoeff_char_periodic Λ hμ l y
  have hcont : Continuous e := by fun_prop
  have hnorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [he, Complex.norm_exp]
    simp
  set g : V → ℂ := fun x => f x * e x with hg
  have hgi : Integrable g :=
    Integrable.mono' hf.norm (hf.aestronglyMeasurable.mul hcont.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp only [hg, norm_mul, hnorm, mul_one, le_refl])
  have hL : ∀ y, (∑' l : Λ, f ((l : V) + y)) * e y = ∑' l : Λ, g ((l : V) + y) := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun l => ?_
    simp only [hg, hper]
  show ∫ y in D, (∑' l : Λ, f ((l : V) + y)) * e y = (𝓕 f : V → ℂ) μ
  simp_rw [hL]
  have h1 : (∑' l : Λ, ∫⁻ y in D, ‖g ((l : V) + y)‖ₑ) = ∫⁻ x, ‖g x‖ₑ :=
    (hD.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)).symm
  have hfin : (∑' l : Λ, ∫⁻ y in D, ‖g ((l : V) + y)‖ₑ) ≠ ⊤ := by
    rw [h1]
    exact hgi.2.ne
  have h2 : (∑' l : Λ, ∫ y in D, g ((l : V) + y)) = ∫ x, g x :=
    (hD.integral_eq_tsum'' g hgi).symm
  rw [integral_tsum (fun l : Λ => (hgi.comp_add_left (l : V)).aestronglyMeasurable.restrict) hfin, h2,
    Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hg, he, smul_eq_mul]
  rw [mul_comm (f x), real_inner_comm μ x]
  congr 2
  push_cast
  ring

theorem unfolding_fourier_coefficient (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : UnfoldCoeff V := by
  intro Λ _ _ f hf D hD μ hμ
  exact unfoldCoeff_main Λ f hf D hD μ hμ

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries
section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.TorusProjIsOpenQuotientMap
section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.InnerDualVecBasis
open MeasureTheory Filter Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev dualB (e : Module.Basis ι ℝ V) : Module.Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate e

theorem inner_dualB (e : Module.Basis ι ℝ V) (i j : ι) :
    ⟪dualB e i, e j⟫ = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j
  simpa using h

def dualVec (e : Module.Basis ι ℝ V) (m : ι → ℤ) : V := ∑ i, m i • dualB e i

theorem dualVec_eq (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m = ∑ i, (m i : ℝ) • dualB e i := by
  unfold dualVec
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm

theorem inner_dualVec_basis (e : Module.Basis ι ℝ V) (m : ι → ℤ) (j : ι) :
    ⟪dualVec e m, e j⟫ = m j := by
  rw [dualVec_eq, sum_inner]
  simp_rw [real_inner_smul_left, inner_dualB]
  simp

theorem dual_span_eq (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) = Submodule.span ℤ (Set.range (dualB e)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e

theorem dualVec_mem (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m ∈ dual (Submodule.span ℤ (Set.range e)) := by
  rw [dual_span_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem dualVec_injective (e : Module.Basis ι ℝ V) : Function.Injective (dualVec e) := by
  intro m n h
  funext j
  have h1 := congrArg (fun x => ⟪x, e j⟫) h
  simp only [inner_dualVec_basis] at h1
  exact_mod_cast h1

theorem dualVec_surjective (e : Module.Basis ι ℝ V) (μ : V)
    (hμ : μ ∈ dual (Submodule.span ℤ (Set.range e))) : ∃ m, dualVec e m = μ := by
  rw [dual_span_eq] at hμ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hμ
  exact ⟨c, hc⟩

def dualEquiv (e : Module.Basis ι ℝ V) : (ι → ℤ) ≃ dual (Submodule.span ℤ (Set.range e)) :=
  Equiv.ofBijective (fun m => ⟨dualVec e m, dualVec_mem e m⟩)
    ⟨fun m n h => dualVec_injective e (congrArg Subtype.val h),
     fun μ => by
      obtain ⟨m, hm⟩ := dualVec_surjective e μ μ.2
      exact ⟨m, Subtype.ext hm⟩⟩

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.FundamentalDomainEqPreimage
open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

abbrev boxIco (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

theorem volume_boxIco : volume (boxIco ι) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Ico]

theorem fundamentalDomain_eq_preimage (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]

theorem integral_fundamentalDomain_eq (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by
  let ψ : V ≃ᵐ (ι → ℝ) := e.equivFunL.toHomeomorph.toMeasurableEquiv
  have hψ : (ψ : V → ι → ℝ) = e.equivFunL := rfl
  set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef
  haveI : ν.IsAddHaarMeasure := by
    rw [hνdef, hψ]; exact e.equivFunL.isAddHaarMeasure_map volume
  have hν : ν = ν.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e) := by
    rw [hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]
  have hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e) := by
    rw [← hbox]
    conv_rhs => rw [hν]
    simp [volume_boxIco]
  have hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν := by
    rw [hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]
    simp only [hψ, ContinuousLinearEquiv.symm_apply_apply]
  rw [hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc,
    ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]

end Formalism.H
end
end

open MeasureTheory Set Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def torusProj (ι : Type*) : (ι → ℝ) → UnitAddTorus ι := fun t i => (t i : UnitAddCircle)

theorem torusProj_isOpenQuotientMap : IsOpenQuotientMap (torusProj ι) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem torusProj_surjective : Function.Surjective (torusProj ι) := by
  intro θ
  choose t ht using fun i => QuotientAddGroup.mk_surjective (θ i)
  exact ⟨t, funext ht⟩

theorem torusProj_eq (s t : ι → ℝ) (h : torusProj ι s = torusProj ι t) :
    ∃ n : ι → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + (k : ℝ) := by
    intro i
    have h1 := congrFun h i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

theorem equivFunL_symm_eq (e : Module.Basis ι ℝ V) (t : ι → ℝ) :
    e.equivFunL.symm t = ∑ i, t i • e i := by
  exact e.equivFun_symm_apply t

theorem periodic_comp (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x)
    (s : ι → ℝ) (n : ι → ℤ) :
    G (e.equivFunL.symm (s + fun i => (n i : ℝ))) = G (e.equivFunL.symm s) := by
  rw [map_add (f := _), add_comm]
  apply hper
  rw [equivFunL_symm_eq]
  refine Submodule.sum_mem _ fun i _ => ?_
  show ((n i : ℝ)) • e i ∈ _
  rw [Int.cast_smul_eq_zsmul ℝ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def torusFun (e : Module.Basis ι ℝ V) (G : V → ℂ) : UnitAddTorus ι → ℂ :=
  fun θ => G (e.equivFunL.symm (Function.surjInv (torusProj_surjective (ι := ι)) θ))

theorem torusFun_proj (e : Module.Basis ι ℝ V) (G : V → ℂ)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (t : ι → ℝ) :
    torusFun e G (torusProj ι t) = G (e.equivFunL.symm t) := by
  obtain ⟨n, hn⟩ := torusProj_eq _ t
    (Function.surjInv_eq (torusProj_surjective (ι := ι)) (torusProj ι t))
  have h1 := periodic_comp e G hper (Function.surjInv (torusProj_surjective (ι := ι)) (torusProj ι t)) n
  rw [← hn] at h1
  exact h1.symm

theorem torusFun_continuous (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    Continuous (torusFun e G) := by
  rw [torusProj_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have h1 : torusFun e G ∘ torusProj ι = fun t => G (e.equivFunL.symm t) :=
    funext (torusFun_proj e G hper)
  rw [h1]
  exact hG.comp e.equivFunL.symm.continuous

def torusFunC (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) :
    C(UnitAddTorus ι, ℂ) :=
  ⟨torusFun e G, torusFun_continuous e G hG hper⟩

theorem mFourier_torusProj (e : Module.Basis ι ℝ V) (m : ι → ℤ) (t : ι → ℝ) :
    UnitAddTorus.mFourier m (torusProj ι t) =
      Complex.exp (2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ)) := by
  have hinner : (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ) = ∑ i, (m i : ℝ) * t i := by
    rw [equivFunL_symm_eq, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, inner_dualVec_basis, mul_comm]
  rw [hinner]
  show (∏ i, fourier (m i) ((t i : ℝ) : UnitAddCircle)) = _
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem boxIoc_ae_eq :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ))
      =ᵐ[volume] boxIco ι := by
  have h1 : ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ)) =
      Set.univ.pi fun i => Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
    ext x
    simp [Set.mem_univ_pi]
  rw [h1]
  rw [volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm

theorem mFourierCoeff_torusFunC (e : Module.Basis ι ℝ V) (G : V → ℂ) (hG : Continuous G)
    (hper : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusFunC e G hG hper) m =
      ∫ t in boxIco ι, G (e.equivFunL.symm t) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ))) := by
  have hS : (Set.univ.pi fun _ : ι => Ioc (0 : ℝ) (0 + 1)) =
      {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext x
    simp [Set.mem_univ_pi]
  have hmp : MeasurePreserving (torusProj ι)
      (volume.restrict {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)})
      (@volume (UnitAddTorus ι)
        (@MeasureSpace.pi ι _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) := by
    have hvol : @volume UnitAddCircle instMeasureSpaceUnitAddCircle =
        @volume UnitAddCircle (AddCircle.measureSpace 1) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp; rfl
    rw [← hS]
    show MeasurePreserving _ ((Measure.pi fun _ => volume).restrict _)
      (Measure.pi fun _ => @volume UnitAddCircle instMeasureSpaceUnitAddCircle)
    rw [Measure.restrict_pi_pi, hvol]
    exact measurePreserving_pi (μ := fun _ => volume.restrict (Ioc (0 : ℝ) (0 + 1)))
      (ν := fun _ => @volume UnitAddCircle (AddCircle.measureSpace 1))
      (fun _ => AddCircle.measurePreserving_mk 1 0)
  have hneg : dualVec e (-m) = -dualVec e m := by
    simp only [dualVec, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  have hmap := integral_map (f := fun θ => UnitAddTorus.mFourier (-m) θ • torusFunC e G hG hper θ)
    hmp.aemeasurable
    ((UnitAddTorus.mFourier (-m)).continuous.smul (torusFunC e G hG hper).continuous).aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [UnitAddTorus.mFourierCoeff]
  refine hmap.trans ?_
  rw [Measure.restrict_congr_set boxIoc_ae_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show UnitAddTorus.mFourier (-m) (torusProj ι t) * torusFun e G (torusProj ι t) = _
  rw [torusFun_proj e G hper, mFourier_torusProj e (-m) t, mul_comm, hneg, inner_neg_left]
  congr 1
  push_cast
  ring
  all_goals first | infer_instance | assumption

end Formalism.H
end
end

open MeasureTheory Set Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem coeff_integrand_periodic (Λ : Submodule ℤ V) (G : V → ℂ)
    (hper : ∀ (l : Λ) (x : V), G ((l : V) + x) = G x) (μ : V) (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    G ((l : V) + y) * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) = ⟪μ, (l : V)⟫ := by
    have hm : innerₗ V μ (l : V) ∈ (1 : Submodule ℤ ℝ) := hμ (l : V) l.2
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp hm
    exact ⟨n, by simpa using hn⟩
  rw [hper l y, inner_add_right, ← hn]
  have h1 : Complex.exp (((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [← mul_one (Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ)))), ← h1, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem lattice_fourier_series (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeFourierSeries V := by
  intro Λ _ _ G hG hper D hD hsum x
  classical
  have : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  have : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let e := b.ofZLatticeBasis ℝ Λ
  have he : Submodule.span ℤ (Set.range e) = Λ := b.ofZLatticeBasis_span ℝ Λ
  have hper' : ∀ l ∈ Submodule.span ℤ (Set.range e), ∀ x, G (l + x) = G x := by
    intro l hl x
    rw [he] at hl
    exact hper ⟨l, hl⟩ x
  set c : V → ℂ := fun μ =>
    ∫ y in D, G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) with hc
  have hF : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain e) volume := by
    have h := ZSpan.isAddFundamentalDomain e volume
    rw [he] at h
    exact h
  have : MeasurableVAdd Λ V := (inferInstance : MeasurableVAdd Λ.toAddSubgroup V)
  have : VAddInvariantMeasure Λ V volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup V volume)
  have hcov : ZLattice.covolume Λ = volume.real (ZSpan.fundamentalDomain e) :=
    ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF
  have hcov0 : (ZLattice.covolume Λ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero Λ volume)
  let g := torusFunC e G hG hper'
  have hmem : ∀ m, dualVec e m ∈ dual Λ := fun m => by
    have h := dualVec_mem e m
    rw [he] at h
    exact h
  have hcoef : ∀ m, c (dualVec e m) = (ZLattice.covolume Λ : ℂ) * UnitAddTorus.mFourierCoeff g m := by
    intro m
    simp only [hc]
    rw [hD.setIntegral_eq hF (fun l y => coeff_integrand_periodic Λ G hper _ (hmem m) l y),
      integral_fundamentalDomain_eq, hcov, mFourierCoeff_torusFunC]
  let E : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) ≃ dual Λ := (dualEquiv e).trans (Equiv.subtypeEquivRight (fun v => by rw [he]))
  have hE : ∀ m, ((E m : dual Λ) : V) = dualVec e m := fun m => rfl
  have hsumE : Summable (fun m => c (dualVec e m)) := by
    have := (E.summable_iff (f := fun μ : dual Λ => c μ)).2 hsum
    exact this
  have hsg : Summable (UnitAddTorus.mFourierCoeff g) := by
    refine (hsumE.mul_left ((ZLattice.covolume Λ : ℂ)⁻¹)).congr fun m => ?_
    rw [hcoef, ← mul_assoc, inv_mul_cancel₀ hcov0, one_mul]
  have hx := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsg
    (torusProj _ (e.equivFunL x))
  have hgx : g (torusProj _ (e.equivFunL x)) = G x := by
    show torusFun e G _ = _
    rw [torusFun_proj e G hper', ContinuousLinearEquiv.symm_apply_apply]
  rw [hgx] at hx
  rw [← E.hasSum_iff]
  convert hx using 1
  funext m
  simp only [Function.comp_apply, hE, smul_eq_mul]
  change ((ZLattice.covolume Λ : ℂ)⁻¹ * c (dualVec e m)) * _ = _
  rw [mFourier_torusProj e, ContinuousLinearEquiv.symm_apply_apply,
    hcoef, ← mul_assoc, inv_mul_cancel₀ hcov0, one_mul]

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.Periodization
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

namespace PoissonPeriodization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma exists_global_bound {f : V → ℂ} (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hO : f =O[cocompact V] (fun v => ‖v‖ ^ (-b))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-b) := by
  obtain ⟨c, hc⟩ := hO.bound
  rw [← cobounded_eq_cocompact] at hc
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hc
  obtain ⟨r, hr⟩ := hc
  set r' := max r 1 with hr'
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) r').exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max (M * (1 + r') ^ b) (|c| * 2 ^ b), by positivity, fun v => ?_⟩
  by_cases hv : ‖v‖ ≤ r'
  · have h1 := hM v (by simpa using hv)
    have hpos : 0 < 1 + ‖v‖ := by positivity
    have hr1 : 0 < 1 + r' := by
      have : 1 ≤ r' := le_max_right _ _
      linarith
    have hone : 1 ≤ (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos b)]
      exact Real.rpow_le_rpow hpos.le (by linarith) hb
    calc ‖f v‖ ≤ M := h1
      _ ≤ M * ((1 + r') ^ b * (1 + ‖v‖) ^ (-b)) :=
          le_mul_of_one_le_right (le_trans (norm_nonneg _) h1) hone
      _ = M * (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_left _ _
  · push_neg at hv
    have hv1 : 1 ≤ ‖v‖ := le_trans (le_max_right _ _) hv.le
    have hb' := hr ‖v‖ (le_trans (le_max_left _ _) hv.le) v rfl
    have hvpos : 0 < ‖v‖ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hb'
    have hk : ‖v‖ ^ (-b) ≤ 2 ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hvpos.le, Real.rpow_neg (by positivity),
        le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by positivity) b),
        inv_mul_le_iff₀ (Real.rpow_pos_of_pos hvpos b),
        ← Real.mul_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hb
    have hnn : 0 ≤ ‖v‖ ^ (-b) := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖f v‖ ≤ c * ‖v‖ ^ (-b) := hb'
      _ ≤ |c| * ‖v‖ ^ (-b) := mul_le_mul_of_nonneg_right (le_abs_self c) hnn
      _ ≤ |c| * (2 ^ b * (1 + ‖v‖) ^ (-b)) := mul_le_mul_of_nonneg_left hk (abs_nonneg c)
      _ = |c| * 2 ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_right _ _

lemma shift_bound {b : ℝ} (hb : 0 ≤ b) {R : ℝ} (hR : 0 ≤ R) (y x : V) (hx : ‖x‖ ≤ R) :
    (1 + ‖y + x‖) ^ (-b) ≤ (1 + R) ^ b * (1 + ‖y‖) ^ (-b) := by
  have h1 : 0 < 1 + ‖y + x‖ := by positivity
  have h2 : 0 < 1 + ‖y‖ := by positivity
  have h3 : 0 < 1 + R := by linarith
  have key : 1 + ‖y‖ ≤ (1 + ‖y + x‖) * (1 + R) := by
    have hyx : ‖y‖ ≤ ‖y + x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y + x) - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖y + x‖ + ‖x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + x)]
  have key' : (1 + ‖y‖) ^ b ≤ ((1 + ‖y + x‖) * (1 + R)) ^ b := Real.rpow_le_rpow h2.le key hb
  rw [Real.mul_rpow h1.le h3.le] at key'
  have hA := Real.rpow_pos_of_pos h1 b
  have hB := Real.rpow_pos_of_pos h2 b
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, le_mul_inv_iff₀ hB, inv_mul_le_iff₀ hA]
  exact key'

lemma summable_one_add_norm (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : ℝ} (hb : (Module.finrank ℝ V : ℝ) < b) :
    Summable (fun l : Λ => (1 + ‖(l : V)‖) ^ (-b)) := by
  classical
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
  have hr : -b < -(Module.finrank ℤ Λ : ℝ) := by
    rw [ZLattice.rank ℝ Λ]
    linarith
  have hs := ZLattice.summable_norm_rpow Λ (-b) hr
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
    (hs.add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases h : l = 0
  · subst h
    simp only [if_pos rfl, ZeroMemClass.coe_zero, norm_zero, add_zero, Real.one_rpow, if_true, ↓reduceIte]
    linarith [Real.rpow_nonneg (le_refl (0 : ℝ)) (-b)]
  · have hl : 0 < ‖(l : V)‖ := norm_pos_iff.mpr (by simpa using h)
    rw [if_neg h, add_zero]
    show (1 + ‖(l : V)‖) ^ (-b) ≤ ‖(l : V)‖ ^ (-b)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hl b) (Real.rpow_le_rpow hl.le (by linarith) hb0.le)

end PoissonPeriodization

open PoissonPeriodization in
theorem poisson_periodization (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Periodization V := by
  unfold Periodization
  intro Λ _ _ f hf b hb hO
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg _) hb.le
  obtain ⟨C, hC0, hC⟩ := exists_global_bound hf hb0 hO
  have hS := summable_one_add_norm Λ hb
  have hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (l : Λ) (x : V), ‖x‖ ≤ R →
      ‖f (↑l + x)‖ ≤ C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by
    intro R hR l x hx
    calc ‖f (↑l + x)‖ ≤ C * (1 + ‖(l : V) + x‖) ^ (-b) := hC _
      _ ≤ C * ((1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (shift_bound hb0 hR (l : V) x hx) hC0
      _ = C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((integrable_one_add_norm hb).const_mul C).mono' hf.aestronglyMeasurable ?_
    exact ae_of_all _ (fun v => hC v)
  · intro x
    exact Summable.of_norm_bounded (hS.mul_left (C * (1 + ‖x‖) ^ b))
        (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
  · refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
    have hcont : ContinuousOn (fun x => ∑' l : Λ, f (↑l + x)) (Metric.ball (0 : V) (‖x₀‖ + 1)) := by
      refine continuousOn_tsum (fun l => (hf.comp (continuous_const.add continuous_id)).continuousOn)
        (hS.mul_left (C * (1 + (‖x₀‖ + 1)) ^ b)) ?_
      intro l x hx
      exact hbound (‖x₀‖ + 1) (by positivity) l x (by simpa using (Metric.mem_ball.mp hx).le)
    exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  · intro l₀ x
    have h := (Equiv.addRight l₀).tsum_eq (fun l : Λ => f (↑l + x))
    simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc] at h
    exact h

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.DualLattice
@[expose] section

noncomputable section

namespace Formalism.H

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma dualLattice_innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  exact (LinearMap.BilinForm.nondegenerate_iff (innerₗ V)
      (fun x => by rw [innerₗ_apply_apply]; exact real_inner_self_nonneg) isSymm_inner).2
      (fun x => by rw [innerₗ_apply_apply]; exact inner_self_eq_zero)

lemma innerₗ_isSymm : LinearMap.BilinForm.IsSymm (innerₗ V) := by
  exact ⟨fun x y => by
      simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _⟩

variable [FiniteDimensional ℝ V]

lemma exists_basis_span_eq (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (e : Module.Basis ι ℝ V),
      Submodule.span ℤ (Set.range e) = Λ := by
  classical
  exact ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, inferInstance,
    Module.Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ Λ),
    Module.Basis.ofZLatticeBasis_span ℝ Λ _⟩

lemma isLattice_of_eq_span {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
  subst h
  refine ⟨inferInstance, ?_⟩
  intro _
  infer_instance

lemma dualLattice_dual_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) =
      Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ V) dualLattice_innerₗ_nondegenerate e)) := LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) dualLattice_innerₗ_nondegenerate e

end Formalism.H
end
end

section -- merged from Formalism.LatticeTheta.LatticeThetaProofs.CovolumeDual
open MeasureTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

lemma covolDual_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

lemma covolDual_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ V) (e : Module.Basis ι ℝ V) :
    o.toBasis.det (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) * o.toBasis.det e = 1 := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  set P := o.toBasis.toMatrix e with hP
  set Q := o.toBasis.toMatrix (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) with hQ
  have hM : Qᵀ * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ k, Qᵀ i k * P k j =
        ⟪LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e i, e j⟫ := by
      simp only [hP, hQ, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← o.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm (o k)]
    rw [hsum]
    have h := LinearMap.BilinForm.apply_dualBasis_left covolDual_nondegenerate e i j
    simp only [innerₗ_apply_apply] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hM, Matrix.det_one]

lemma covolDual_vol_fd {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ V) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def,
    MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]

end Formalism.H
end
end

namespace Formalism.H

section
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem dualIsLattice : DualIsLattice (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  refine isLattice_of_eq_span (LinearMap.BilinForm.dualBasis (innerₗ V)
    dualLattice_innerₗ_nondegenerate e) (dual Λ) ?_
  rw [← he, dualLattice_dual_span_eq e]

theorem dualDual : DualDual (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  rw [← he, dualLattice_dual_span_eq e, dualLattice_dual_span_eq,
    LinearMap.BilinForm.dualBasis_dualBasis _ innerₗ_isSymm]

variable [MeasurableSpace V] [BorelSpace V]

theorem covolumeDual : CovolumeDual (V := V) := by
  intro Λ _ _ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  subst he
  have h := covolDual_det_mul
    ((stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)) e
  set o := (stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)
  set eD := LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e with heD
  have hli : LinearIndependent ℤ e := e.linearIndependent.restrict_scalars' ℤ
  have hliD : LinearIndependent ℤ eD := eD.linearIndependent.restrict_scalars' ℤ
  have heq : Submodule.span ℤ (Set.range eD) = dual (Submodule.span ℤ (Set.range e)) :=
    (dualLattice_dual_span_eq e).symm
  have hb : ((↑) : Submodule.span ℤ (Set.range e) → V) ∘ Module.Basis.span hli = e :=
    funext fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  have hbD : ((↑) : dual (Submodule.span ℤ (Set.range e)) → V) ∘
      (Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq) = eD :=
    funext fun i => by simp [Module.Basis.span_apply]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume
      ((Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq)) o.toBasis,
    ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume (Module.Basis.span hli) o.toBasis, hb, hbD,
    covolDual_vol_fd, mul_one, mul_one, ← abs_inv]
  exact congrArg abs (eq_inv_of_mul_eq_one_left h)

theorem poissonDecay : PoissonDecay (V := V) := poissonDecay_of (dualIsLattice V) (lattice_summable_decay V) (poisson_periodization V)
  (unfolding_fourier_coefficient V) (lattice_fourier_series V)

theorem poissonSchwartz : PoissonSchwartz (V := V) := poissonSchwartz_of (poissonDecay V) (schwartz_decay_gaussian V)

end

end Formalism.H
