module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibFour

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfFS
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def SemisimpleTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → IsSemisimpleRing (Ainf F ⊗[F] E)

theorem exists_dual_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) (c : Fin a → K) :
    ∃ w : Fin M → K, ∀ i, ∑ k, Z i k * w k = c i := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k => ∑ i', c i' * p (Pi.single k 1) i', fun i => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * ∑ i', c i' * p (Pi.single k 1) i' =
      ∑ i', c i' * (p (Z i)) i' := by
    conv_rhs => rw [hZi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => by ring
  rw [e1, ← hι, hp]
  simp [Pi.single_apply]

theorem freeSurj_of (h : SemisimpleTens) : FreeSurj := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX S
  have := h F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E := fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add (f := _)]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

theorem densInf_of_ss (h2 : TensR) (h3 : SemisimpleTens) : DensInf :=
  densInf_of_tens h2 (freeSurj_of h3)

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

theorem semisimpleTens_holds : SemisimpleTens := by
  intro F E _ _ _ _ _ σ _
  classical
  have : IsArtinianRing (Ainf F) :=
    inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F ⊗[F] E) := IsArtinianRing.of_finite (Ainf F) (Ainf F ⊗[F] E)
  let e1 : Ainf F ⊗[F] E ≃ₐ[F] E ⊗[F] Ainf F := Algebra.TensorProduct.comm F (Ainf F) E
  let e2 : E ⊗[F] ((v : InfinitePlace F) → v.Completion) ≃ₐ[F]
      ((v : InfinitePlace F) → E ⊗[F] v.Completion) :=
    Algebra.TensorProduct.piRight F F E (fun v : InfinitePlace F => v.Completion)
  have : ∀ v : InfinitePlace F, IsReduced (E ⊗[F] v.Completion) := fun v =>
    have := isReduced_tens_field F E v.Completion
    isReduced_of_injective (Algebra.TensorProduct.comm F E v.Completion).toRingHom
      (Algebra.TensorProduct.comm F E v.Completion).injective
  have : IsReduced (Ainf F ⊗[F] E) :=
    isReduced_of_injective ((e2.toRingHom).comp e1.toRingHom) (e2.injective.comp e1.injective)
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem densInf_of_tensR (h : TensR) : DensInf := densInf_of_ss h semisimpleTens_holds

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSecSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def SecGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (_hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (_hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (R : Type) [CommRing R] [Algebra F R], IsSemisimpleRing (R ⊗[F] E) →
    ∀ (a : ℕ) (x : Fin a → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) x →
      ∃ q : Fin M → Fin a → R ⊗[F] E, ∀ S : Matrix (Fin a) (Fin a) (R ⊗[F] E),
        S ∈ HermR R σ a →
        gramB R σ J x (fun j k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') = S

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA
noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_one_of_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

theorem ev_int (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)

theorem ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)

end Ann

end VolAAW

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem lcscPolish_holds : LCSCPolish := fun Y _ _ _ _ => TopoPolish.polish_of_lcsc Y

theorem secCtblW_holds : SecCtblW := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem scha_holds : SCHA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  infer_instance

theorem measGrp_holds : MeasGrp := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ⟨inferInstance, inferInstance⟩

end PI.VolStabS
end
end
