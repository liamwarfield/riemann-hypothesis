module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix nonZeroDivisors

noncomputable section
namespace GlobalTheory.FinSupp

theorem exists_den_of_trace_int (F : Type) [Field F] [NumberField F] :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ t : F, (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((a : F) * t) = m) →
      IsIntegral ℤ ((D : F) * t) := by
  classical
  obtain ⟨c, hc, hfr⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, fun t ht => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · have hmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        first | exact one_ne_zero | simp | exact FractionalIdeal.one_ne_zero
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨m, hm⟩ := ht b
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, hm]
      simp
    obtain ⟨y, hy⟩ := hfr t hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) * t = ((e * y : 𝓞 F) : F) := by
      have h1 : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) = ((e : F) * (c : F)) := by
        have := congrArg (fun z : 𝓞 F => (z : F)) he
        simp only [map_mul, map_natCast] at this
        rw [← this]
      rw [h1, mul_assoc]
      have h2 : (y : F) = (c : F) * t := by
        rw [show (y : F) = algebraMap (𝓞 F) F y from rfl, hy, Algebra.smul_def]
      push_cast
      first | rw [h2] | rw [← h2] | exact congrArg (_ * ·) h2.symm | simp [h2]
    rw [this]
    exact (e * y).isIntegral_coe

theorem trace_int_of_finPart {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (s : F)
    (hs : ψ (finPart F (algebraMap F (AF F) s)) = 1) : ∃ m : ℤ, Algebra.trace ℚ F s = m := by
  set x : AF F := algebraMap F (AF F) s with hx
  set z : AF F := x - finPart F x with hzdef
  have hz : At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [map_zero]
      exact hu
    show u * z = 0
    refine Prod.ext ?_ ?_
    · change u.1 * (x.1 - (0 : Ainf F)) = 0
      rw [hu1, zero_mul]
    · change u.2 * (x.2 - x.2) = 0
      rw [sub_self, mul_zero]
  have hψz : ψ z = 1 := by
    have h := hψ.2.1 s
    rw [← hx, show x = z + finPart F x by rw [hzdef, sub_add_cancel], AddChar.map_add_eq_mul, hs, mul_one] at h
    exact h
  have hev : evI F z = mixedEmbedding F s := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x.1 - 0) = _
    rw [sub_zero, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rfl
  have h := hψ.2.2 z hz
  rw [hψz, hev, GlobalTheory.LatVacArith.trace_mixedEmbedding] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h.symm
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : (((Algebra.trace ℚ F s : ℚ) : ℝ) : ℂ) = -(n : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -hn
  refine ⟨-n, ?_⟩
  push_cast
  exact_mod_cast hq

end GlobalTheory.FinSupp

namespace GlobalTheory.FinSupp.DenStd

theorem exists_den : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  intro F _ _
  obtain ⟨D, hD, hint⟩ := GlobalTheory.FinSupp.exists_den_of_trace_int F
  exact ⟨D, hD, fun ψ hψ t ht => hint t fun a => GlobalTheory.FinSupp.trace_int_of_finPart hψ _ (ht a)⟩

end GlobalTheory.FinSupp.DenStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivialStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_standardChar_trivial : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  first | exact @GlobalTheory.FinSupp.DenStd.exists_den | exact GlobalTheory.FinSupp.DenStd.exists_den | (intros; apply GlobalTheory.FinSupp.DenStd.exists_den <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.PoissonReindex.poisson_any : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  have hC1 := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hC1
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : Ctx ψ lam ν a := ⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩
  obtain ⟨hHaar, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have h' : r = 0 := by exact_mod_cast h
    rw [h', zero_smul] at hr
    exact (NeZero.ne μ) hr
  refine ⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩
  set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y' := by
    intro y'
    simp only [hG]
    rw [hr, integral_smul_nnreal_measure, integral_map_equiv]
    simp only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]
    rw [NNReal.smul_def, Complex.real_smul]
  have hΦ's : Φ' ∈ schA F (Fin N) := mem_schA_reidx e hΦ
  have hD : Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's
  have hGs : (fun u => G (T u)) ∈ schA F (Fin N) := mem_schA_reidx e hFΦ
  have hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u) := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, key u]
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hFD : Decay (Fo ψ ν a Φ') := by
    rw [hFeq]
    exact GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)
  have hP := GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD
  let E2 : (Fin N → F) ≃ (κ → F) :=
    { toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j),
      left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }
  have hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u)) := by
    intro H
    simp only [thetaSum, th]
    exact ((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm
  rw [hth G, hth Φ]
  simp only [th] at hP ⊢
  simp only [key, tsum_mul_left]
  rw [hP]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaarStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoisson_summation_anyHaar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  first | exact @GlobalTheory.PoissonReindex.poisson_any | exact GlobalTheory.PoissonReindex.poisson_any | (intros; apply GlobalTheory.PoissonReindex.poisson_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportDenom
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


open Formalism.UG in
theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 := by
  intro F E _ _ _ _ _ n d e
  classical
  set Y : Fin n × Fin d → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    fun j => e.symm (0, fun k => if j = k then 1 else 0) with hY
  let f1 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst (AF F) _ _).comp e.toLinearMap)
  let f2 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd (AF F) _ _).comp e.toLinearMap)
  choose K1 hK1f hK11 hK1 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f1 i)
  choose K2 hK2f hK21 hK2 using fun i => GlobalTheory.T.linear_form_bounded_by_local_constants (f2 i)
  choose KY hKYf hKY1 hKY using fun j => GlobalTheory.T.matrix_entries_bounded_almost_everywhere (Y j)
  have prod_one : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ v, 1 ≤ ∏ i, K i v := fun K hK v => Finset.one_le_prod' fun i _ => hK i v
  have prod_fin : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i, (Function.mulSupport (K i)).Finite) →
      (Function.mulSupport fun v => ∏ i, K i v).Finite := fun K hK =>
    ((Finset.univ : Finset (Fin n × Fin d)).finite_toSet.biUnion fun i _ => hK i).subset
      (Finset.mulSupport_prod _ _)
  have single_le : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ i v, K i v ≤ ∏ i, K i v := fun K hK i v => Finset.single_le_prod' (fun j _ => hK j v) (Finset.mem_univ i)
  set Ka : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v with hKa
  have hKa1 : ∀ v, 1 ≤ Ka v := fun v => one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (prod_one K1 hK11 v) (prod_one K2 hK21 v)) (prod_one KY hKY1 v)
  have hKaf : (Function.mulSupport Ka).Finite :=
    ((((prod_fin K1 hK1f).union (prod_fin K2 hK2f)).subset (Function.mulSupport_mul _ _)).union
      (prod_fin KY hKYf)).subset (Function.mulSupport_mul _ _)
  have hle1 : ∀ i j v, K1 i v * KY j v ≤ Ka v := fun i j v =>
    calc K1 i v * KY j v ≤ (∏ i, K1 i v) * ∏ j, KY j v := mul_le_mul' (single_le K1 hK11 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K1 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        rw [mul_right_comm]
        exact le_mul_of_one_le_right' (prod_one K2 hK21 v)
  have hle2 : ∀ i j v, K2 i v * KY j v ≤ Ka v := fun i j v =>
    calc K2 i v * KY j v ≤ (∏ i, K2 i v) * ∏ j, KY j v := mul_le_mul' (single_le K2 hK21 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K2 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        exact mul_le_mul_left (le_mul_of_one_le_left' (prod_one K1 hK11 v)) _
  refine ⟨((∏ᶠ v, Ka v : ℝ≥0) : ℝ), fun g h => ?_⟩
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0 :=
    fun v => Ka v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) with hB
  have hB1 : ∀ v, 1 ≤ B v := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hKa1 v) (one_le_htOf _ _)) (one_le_htOf _ _)
  have hgf := finite_mulSupport_htFin F g
  have hhf := finite_mulSupport_htFin F h
  have hBf : (Function.mulSupport B).Finite :=
    (((hKaf.union hgf).subset (Function.mulSupport_mul _ _)).union hhf).subset (Function.mulSupport_mul _ _)
  obtain ⟨N, hN, hNle, hNint⟩ := GlobalTheory.SmoothForms.denom_global B hB1 hBf
  have hfin : ∀ {m : ℕ} (k : GL (Fin m) (AF F ⊗[F] E)), ∏ᶠ v, htFin F v (bc (compFin F E v) k) ≤ heightGL F k :=
    fun k => by
      unfold heightGL
      exact le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)
  refine ⟨N, hN, ?_, ?_⟩
  · have e1 : ∏ᶠ v, B v = (∏ᶠ v, Ka v) * (∏ᶠ v, htFin F v (bc (compFin F E v) g)) *
        ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
      rw [hB, finprod_mul_distrib ((hKaf.union hgf).subset (Function.mulSupport_mul _ _)) hhf,
        finprod_mul_distrib hKaf hgf]
    have : (N : ℝ≥0) ≤ (∏ᶠ v, Ka v) * (heightGL F g * heightGL F h) := by
      refine hNle.trans ?_
      rw [e1, mul_assoc]
      exact mul_le_mul_right (mul_le_mul' (hfin g) (hfin h)) _
    exact_mod_cast this
  intro M y hy
  set L : (Fin n × Fin d → AF F) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    e.toLinearMap ∘ₗ sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) ∘ₗ
      e.symm.toLinearMap ∘ₗ LinearMap.inr (AF F) _ _ with hL
  have hLy : e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) =
      ∑ j, y j • L (fun k => if j = k then 1 else 0) := LinearMap.pi_apply_eq_sum_univ L y
  have hsz : ∀ j v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v
      (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j) p.1 p.2))) ≤
      htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h) := fun j v =>
    Finset.sup_le fun p _ => (GlobalTheory.T.finite_abs_matrix_product_le_heights g (Y j) h v p.1 p.2).trans
      (mul_le_mul_left (mul_le_mul_right (hKY j v) _) _)
  have hcomp : ∀ t : Fin n × Fin d → AF F, (∀ j v, ‖evFin F v (t j)‖₊ ≤ B v) →
      (∑ j, y j * t j).1 = 0 ∧ ∀ v, ‖evFin F v (∑ j, y j * t j)‖ ≤ ‖(M : Fv F v)‖ := by
    intro t ht
    refine ⟨?_, fun v => ?_⟩
    · change fstA F (∑ j, y j * t j) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul]
      change (y j).1 * _ = 0
      rw [hy.1 j, zero_mul]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
      rw [map_mul, norm_mul]
      have h1 := hy.2 v j
      have h2 := hNint v (evFin F v (t j)) (ht j v)
      rw [Nat.cast_mul, norm_mul] at h1
      rw [norm_mul] at h2
      calc ‖evFin F v (y j)‖ * ‖evFin F v (t j)‖ ≤ ‖(M : Fv F v)‖ * ‖(N : Fv F v)‖ * ‖evFin F v (t j)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ * (‖(N : Fv F v)‖ * ‖evFin F v (t j)‖) := mul_assoc _ _ _
        _ ≤ ‖(M : Fv F v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ := mul_one _
  have htB : ∀ (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) (K : HeightOneSpectrum (𝓞 F) → ℝ≥0),
      (∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) →
      (∀ j v, K v * KY j v ≤ Ka v) → ∀ j v,
      ‖evFin F v (f (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j)))‖₊ ≤ B v := by
    intro f K hf hK j v
    refine (hf _ v).trans ?_
    refine (mul_le_mul_right (hsz j v) _).trans ?_
    calc K v * (htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h)) =
        K v * KY j v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := by ring
      _ ≤ B v := mul_le_mul_left (mul_le_mul_left (hK j v) _) _
  refine ⟨⟨fun i => ?_, fun v i => ?_⟩, ⟨fun i => ?_, fun v i => ?_⟩⟩
  all_goals rw [hLy]
  all_goals simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).2 v
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).2 v

end GlobalTheory.ThetaDenom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompact
set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.IntegralSum

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_zero' : A.IsForm 0 := by
  constructor
  · intro i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    intro v _
    split_ifs
    erw [Pi.zero_apply, map_zero, Finsupp.zero_apply]
  · intro x x' _
    exact (map_zero _).symm

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem integral_zero_fld : A.integral 0 = 0 := by
  have h := A.integral_sub_of_isForm 0 0 (isForm_zero' A) (isForm_zero' A)
  simpa using h

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_add' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α + β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.add h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.add_apply, map_add, Finsupp.add_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
private theorem isForm_sub' {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.IsForm (α - β) := by
  constructor
  · intro i S
    have h1 := ha.smooth i S
    have h2 := hb.smooth i S
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc
    unfold _root_.GlobalTheory.CxForm.HolAtlas.loc at h1 h2
    refine (h1.sub h2).congr ?_
    intro v hv
    simp only [dif_pos hv]
    erw [Pi.sub_apply, map_sub, Finsupp.sub_apply]
  · intro x x' hx
    simp [ha.compat x x' hx, hb.compat x x' hx]

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem integral_add_of_isForm {α β : A.Fld}
    (ha : A.IsForm α) (hb : A.IsForm β) :
    A.integral (α + β) =
      A.integral α + A.integral β := by
  have hnb : A.IsForm (0 - β) :=
    isForm_sub' A (isForm_zero' A) hb
  have h := A.integral_sub_of_isForm α (0 - β) ha hnb
  have h0 := A.integral_sub_of_isForm 0 β (isForm_zero' A) hb
  rw [integral_zero_fld A] at h0
  rw [show α - (0 - β) = α + β by abel] at h
  rw [h, h0]
  ring

set_option autoImplicit false in
open Set Matrix MeasureTheory in
open scoped ComplexOrder in
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : _root_.GlobalTheory.CxForm.HolAtlas M n) in
variable [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem isForm_and_integral_finset_sum {ι : Type} (s : Finset ι)
    (α : ι → A.Fld) (hα : ∀ j ∈ s, A.IsForm (α j)) :
    A.IsForm (∑ j ∈ s, α j) ∧
      A.integral (∑ j ∈ s, α j) = ∑ j ∈ s, A.integral (α j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨isForm_zero' A, integral_zero_fld A⟩
  | insert a s ha ih =>
    have hs := ih (fun j hj => hα j (Finset.mem_insert_of_mem hj))
    have hA := hα a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨isForm_add' A hA hs.1, ?_⟩
    rw [integral_add_of_isForm A hA hs.1, hs.2]


set_option autoImplicit false in
theorem _root_.GlobalTheory.CxForm.IntegralSum.integral_sum : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (A : _root_.GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld),
    (∀ j, A.IsForm (α j)) →
      A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  intro M _ _ _ _ _ _ n A N α hα
  exact (isForm_and_integral_finset_sum A Finset.univ α (fun j _ => hα j)).2

end GlobalTheory.CxForm.IntegralSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_integral_fin_sum_compact : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  first | exact @GlobalTheory.CxForm.IntegralSum.integral_sum | exact GlobalTheory.CxForm.IntegralSum.integral_sum | (intros; apply GlobalTheory.CxForm.IntegralSum.integral_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeigh
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeigh
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.MovedLat

open Formalism.UG

theorem htFin_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) :
    htFin F v (bc (compFin F E v) g⁻¹) = htFin F v (bc (compFin F E v) g) := by
  rw [map_inv]; exact htOf_inv _ _

theorem finprod_htFin_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) :
    ∏ᶠ v, htFin F v (bc (compFin F E v) g) ≤ heightGL F g :=
  le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)

end GlobalTheory.MovedLat

open Formalism.UG

theorem GlobalTheory.MovedLat.exists_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  intro F E _ _ _ _ _ n d κ _ _ e N hN
  classical
  let f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  let f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)
  choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)
  let Y : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i => e.symm (0, Pi.single i 1)
  choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)
  let Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v
  have hKc1 : ∀ v, 1 ≤ Kc v := fun v =>
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.one_le_prod' fun i _ => hKx i v)
  have hKcf : (Function.mulSupport Kc).Finite := by
    refine ((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_
    refine (Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨j, -, hj⟩ := hv
      exact ⟨j, Function.mulSupport_mul _ _ hj⟩
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨i, -, hi⟩ := hv
      exact ⟨i, hi⟩
  have hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v := fun v =>
    le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)
  have hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v := fun v =>
    le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
  have hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl
  have hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl
  let C0 : ℝ≥0 := ∏ᶠ v, Kc v
  refine ⟨N * C0, 1, fun g h => ?_⟩
  let Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) g)
  let Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) h)
  have hgf : (Function.mulSupport Hg).Finite := finite_mulSupport_htFin F g
  have hhf : (Function.mulSupport Hh).Finite := finite_mulSupport_htFin F h
  let Z : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i =>
    ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
      (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ
  have hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤
      Kx i v * (Hg v * Hh v) := fun i v => by
    refine Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_
    rw [GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]
    calc _ ≤ Hg v * Kx i v * Hh v := mul_le_mul' (mul_le_mul' le_rfl (hKxb i v)) le_rfl
      _ = Kx i v * (Hg v * Hh v) := by ring
  have hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK1b j (Z i) v
    calc _ ≤ K1 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K1 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK1c v i j) le_rfl
  have hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK2b j (Z i) v
    calc _ ≤ K2 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K2 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK2c v i j) le_rfl
  let H : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => Kc v * (Hg v * Hh v)
  have hH1 : ∀ v, 1 ≤ H v := fun v =>
    one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
  have hHf : (Function.mulSupport H).Finite :=
    (hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans
      (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))
  obtain ⟨M, hM0, hMb, hMv⟩ := GlobalTheory.SmoothForms.denom_global H hH1 hHf
  have hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x) := by
    intro x hx v
    refine ⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩
    rw [map_mul, map_natCast]
    push_cast
    ring
  refine ⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩
  have hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h) := by
    refine hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)
    refine mul_le_mul' le_rfl ?_
    rw [finprod_mul_distrib hgf hhf]
    exact mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)
  have := NNReal.coe_le_coe.2 hMH
  push_cast at this ⊢
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeighStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  first | exact @GlobalTheory.MovedLat.exists_scale | exact GlobalTheory.MovedLat.exists_scale | (intros; apply GlobalTheory.MovedLat.exists_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
noncomputable section

open NumberField IsDedekindDomain Polynomial MeasureTheory GroundTheory.Automorphic UpperTheory.V.Af GlobalTheory.HenQ
open scoped ValuativeRel Pointwise

namespace GlobalTheory.HenQ.ShellOp

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}


end General

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Series

end Series

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Hecke

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

theorem lamS_univ' : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

theorem gMat_univ' (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ']

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem central_mem_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h1 : ∀ g, f (g * torusPow F n (fun _ => 1)) = monomialChar (fun _ : Fin n => 1) z * f g := by
    intro g
    have h := hT g
    haveI : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) := ⟨fun p => p.2.2.1 (Finset.mem_univ _)⟩
    have hc : ∀ I : Fintype (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]), (@Finset.univ _ I).card = 1 := by
      intro I
      rw [Subsingleton.elim I Unique.fintype]
      rfl
    rw [integral_minusculeHecke_mul hf, evalAt_satakeTransform_minusculeHecke z le_rfl, evalAt_esymmL, hp,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_congr rfl (fun c _ => by rw [gMat_univ' c]),
      Finset.sum_const, hc, one_smul, lamS_univ', Nat.sub_self, mul_zero,
      pow_zero, mul_one, mul_assoc] at h
    exact mul_left_cancel₀ hK h
  have h2 : ∀ g, f (g * torusPow F n (fun _ => -1)) = monomialChar (fun _ : Fin n => -1) z * f g := by
    intro g
    have h := h1 (g * torusPow F n (fun _ => -1))
    have e : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by funext i; simp
    have e' : torusPow F n (fun _ => -1) * torusPow F n (fun _ => 1) = 1 := by
      have : (fun _ : Fin n => (-1 : ℤ)) = -(fun _ => 1) := rfl
      rw [this, torusPow_neg, inv_mul_cancel]
    rw [mul_assoc, e', mul_one] at h
    rw [h, ← mul_assoc, ← monomialChar_add, e, monomialChar_zero, one_mul]
  intro g
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      f (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    have hiff : g₀ * y ∈ centralSet F n ↔ y ∈ (integralGL F n : Set (GL (Fin n) F)) := by
      rw [mem_centralSet, inv_mul_cancel_left]
      rfl
    by_cases hy : y ∈ (integralGL F n : Set (GL (Fin n) F))
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, one_mul, ← mul_assoc, hf _ _ hy]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy, zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, h2, satakeTransform_centralHecke, map_smul,
    Spherical.monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem minuscule_mem_of (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
  intro g
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc, ← mul_assoc (sqrtQ F ^ _), ← h g]
  rfl

end Hecke

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Global

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {K : Type} [Field K] [NumberField K]

end Global

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

end GlobalTheory.HenQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KinfFinite
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspKinfFin

theorem kinf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀))) := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι _ _ _ _ _ ψ hψ g₀ hK
  classical
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GlobalTheory.CuspRep.GA E d → ℂ) :=
    { toFun := fun φ g => φ (ι g * g₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hV := hψ.1.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map T) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => ψ (x * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)), Submodule.subset_span ⟨⟨_, hK k⟩, rfl⟩, ?_⟩
  funext g
  show ψ (ι g * g₀ * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) = _
  simp only [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspKinfFin
end
