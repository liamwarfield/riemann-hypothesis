module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module

section Lin

end Lin

section Period

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

section Mul

variable {R : Type} [CommRing R] [Algebra Qp R]

theorem _root_.GlobalTheory.DeRhamCompare.comm_mp (b : R) (x : V ⊗[Qp] R) :
    TensorProduct.comm Qp V R (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) b x) =
      b • TensorProduct.comm Qp V R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r =>
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

end Mul

theorem _root_.GlobalTheory.DeRhamCompare.mem_DdR (x : V ⊗[Qp] BdR) :
    x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ ↔ ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x = x := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem _root_.GlobalTheory.DeRhamCompare.mulK_mem (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) x ∈
      _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
  rw [_root_.GlobalTheory.DeRhamCompare.mem_DdR] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[Qp] BdR,
      _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V)
        (algebraMap K BdR c) y) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c)
        (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v r => simp [_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR, _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mulPeriod]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [key, hx g]

theorem _root_.GlobalTheory.DeRhamCompare.finite_DdR [FiniteDimensional LL V] (h : _root_.Formalism.MainNotions.N.IsDR PD ρ) :
    FiniteDimensional LL (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := by
  have hK : FiniteDimensional Qp K := by cases PD; assumption
  unfold _root_.Formalism.MainNotions.N.IsDR at h
  by_cases hV : Module.finrank LL V = 0
  · have hsV : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hzero : ∀ z : V ⊗[Qp] BdR, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul v r => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    have hsub : Subsingleton (_root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :=
      ⟨fun x y => Subtype.ext (by rw [hzero x, hzero y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem _root_.GlobalTheory.DeRhamCompare.FildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR
  refine inf_le_inf_left _ ?_
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    PD.Fil_anti a
  rintro x ⟨y, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

end Period

section Comparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def DdRK : Submodule K (BdR ⊗[Qp] V) where
  carrier := {y | (TensorProduct.comm Qp V BdR).symm y ∈ DdR PD ρ}
  zero_mem' := by simp
  add_mem' := fun hx hy => by
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' := fun c y hy => by
    obtain ⟨x, rfl⟩ := (TensorProduct.comm Qp V BdR).surjective y
    simp only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] at *
    rw [← algebraMap_smul BdR, ← comm_mp (LL := LL), LinearEquiv.symm_apply_apply]
    exact mulK_mem PD ρ c x hy

theorem _root_.GlobalTheory.DeRhamCompare.mem_DdRK (y : BdR ⊗[Qp] V) :
    y ∈ _root_.GlobalTheory.DeRhamCompare.DdRK PD ρ ↔ (TensorProduct.comm Qp V BdR).symm y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  Iff.rfl

def toK (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) : DdRK PD ρ :=
  ⟨TensorProduct.comm Qp V BdR x, by rw [mem_DdRK, LinearEquiv.symm_apply_apply]; exact hx⟩

end Comparison

section Filtered

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

end Filtered

end GlobalTheory.DeRhamCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumberFieldPrimeZetaSumAddLogIsBigO
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.ChebCyc

private theorem tsum_logFactor_add_log_sub_one_isBigO_one (K : Type) [Field K] [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) + Real.log (s - 1))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hT := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hL := ((Real.continuousAt_log hr).tendsto.comp hT).isBigO_one ℝ
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  rw [norm_mul, _root_.GlobalTheory.Mem.ZetaPole.norm_dedekindZeta_eq_exp K hs]
  have hs1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hs1, Real.log_mul (sub_ne_zero.2 hs.ne') (Real.exp_pos _).ne', Real.log_exp]
  ring

private theorem tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one (K : Type) [Field K]
    [NumberField K] :
    (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hN : ∀ P : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm P.asIdeal :=
    fun P => _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
  have hC := _root_.GlobalTheory.Mem.RayPrimes.logSum_sub_bounded (fun P : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm P.asIdeal) hN (fun _ => 1) (fun _ => by simp)
    (fun s hs => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2)
  have hC' : (fun s : ℝ => (((∑' P : HeightOneSpectrum (𝓞 K),
      _root_.GlobalTheory.Mem.ZetaPole.logFactor (Ideal.absNorm P.asIdeal) s) -
      ∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine hC.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
    congr 1
    · refine tsum_congr fun P => ?_
      rw [_root_.GlobalTheory.Mem.ZetaPole.ofReal_logFactor (by linarith [hN P]) (by linarith), one_mul]
    · refine tsum_congr fun P => ?_
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), one_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg]
  rw [← isBigO_norm_left]
  exact hC'.norm_left.congr_left fun s => Complex.norm_real _

theorem _root_.GlobalTheory.ChebCyc.primeSum_add_log_isBigO : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  intro K _ _
  refine ((tsum_logFactor_add_log_sub_one_isBigO_one K).sub
    (tsum_logFactor_sub_tsum_absNorm_rpow_isBigO_one K)).congr_left fun s => ?_
  ring

end GlobalTheory.ChebCyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise

namespace GlobalTheory.UnramCocycle

theorem conj_mem_ine_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ

  have hmem : ∀ y : Ω, y ∈ g • A ↔ g⁻¹ y ∈ A := fun y =>
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
  have hgg : ∀ y : Ω, g⁻¹ (g y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine ⟨?_, fun x hx => ?_⟩
  · have h' : σ • (g • A) = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h', inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, hmem, hgg]
      exact (ValuationSubring.valuation_le_one_iff A x).1 hx
    have hy := hval (g x) hx'
    have e : (g⁻¹ * σ * g) x - x = g⁻¹ (σ (g x) - g x) := by
      rw [map_sub, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    rw [e]
    rw [valuation_lt_one_iff'] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨(hmem _).1 hy1, ?_⟩
    rcases hy2 with h0 | h0
    · left
      rw [h0, map_zero]
    · right
      rwa [← map_inv₀, ← hmem]

def kerSub {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : Subgroup Γ where
  carrier := {n | x.1 n = 0 ∧ ∀ m, ρ n m = m}
  one_mem' := ⟨by simpa using x.2.2 1 1, fun m => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [x.2.2, ha, hb]; simp, fun m => ?_⟩
    rw [map_mul, mul_apply_eq_comp, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    · have h := x.2.2 a a⁻¹
      rw [mul_inv_cancel, h1, ha, ha', zero_add] at h
      exact h.symm
    · conv_lhs => rw [← ha' m]
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

theorem kerSub_normal {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : (kerSub ρ x).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨hx, hρ⟩ := hn
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    ·
      rw [x.2.2, x.2.2, hx, map_zero, add_zero, map_mul, mul_apply_eq_comp, hρ, ← x.2.2,
        mul_inv_cancel, h1]
    · rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hρ,
        ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

theorem kerSub_isClosed {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (hρ : ContAction ρ) (x : Z1 ρ) :
    IsClosed (kerSub ρ x : Set Γ) := by

  have h1 : IsClosed {n : Γ | x.1 n = 0} := isClosed_eq x.2.1 continuous_const
  have hc : Continuous fun p : Γ × M => ρ p.1 p.2 := hρ
  have h2 : IsClosed {n : Γ | ∀ m, ρ n m = m} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun m =>
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact h1.inter h2

theorem vanish_on_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ ρ hρ A S htriv x hx
  have := kerSub_normal ρ x

  have hle : NS Ω S ≤ kerSub ρ x := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ (kerSub_isClosed ρ hρ x)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop] at hσ
    obtain ⟨v, hv, B, hB, hσB⟩ := hσ

    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hB
    have hσ' : σ ∈ Ine (F := F) (g • A.1 v) := by rw [hg, mem_Ine]; exact hσB
    have hc := conj_mem_ine_of_smul (A.1 v) g σ hσ'

    have hzero : x.1 (g⁻¹ * σ * g) = 0 := by
      have hu := hx v hv
      unfold Formalism.GaloisCohomology.unrAt H1ur at hu
      rw [LinearMap.mem_ker] at hu
      unfold resH1 at hu
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hu
      obtain ⟨m, hm⟩ := hu
      have hmem : g⁻¹ * σ * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hc
      have h := hm ⟨⟨g⁻¹ * σ * g, hmem⟩, (Subgroup.mem_subgroupOf).2 hc⟩

      have h' : x.1 (g⁻¹ * σ * g) = ρ (g⁻¹ * σ * g) m - m := h
      rw [htriv v hv (A.1 v) (A.2 v) _ hc, sub_self] at h'
      exact h'
    have hk : g⁻¹ * σ * g ∈ kerSub ρ x := ⟨hzero, htriv v hv (A.1 v) (A.2 v) _ hc⟩
    have h := (kerSub_normal ρ x).conj_mem _ hk g
    have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rwa [e] at h
  exact fun n hn => hle hn

end GlobalTheory.UnramCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_unramified_outside_vanish_on_kernel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  first | exact @GlobalTheory.UnramCocycle.vanish_on_NS | exact GlobalTheory.UnramCocycle.vanish_on_NS | (intros; apply GlobalTheory.UnramCocycle.vanish_on_NS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnit
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Move

variable {K : UQ} (B : InvAlg K)

theorem det_trace_ne_zero (hP : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hP
  have hk : ∀ k : Fin (Module.finrank K.E B.A),
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * ∑ l, v l • e l) = 0 := by
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ w : B.A, Algebra.trace K.E B.A ((∑ l, v l • e l) * w) = 0 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hb k, mul_comm, hk k, smul_zero]
  have hz0 : ∑ l, v l • e l = 0 :=
    (Sandwich.traceForm_nondegenerate B hP).1 _ (fun w => by rw [Algebra.traceForm_apply]; exact hall w)
  apply hv
  apply e.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, hz0, map_zero]

theorem mem_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (z : B.A) :
    z ∈ mulLat K.O (y : B.A) M ↔ ((y⁻¹ : B.Aˣ) : B.A) * z ∈ M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_inv (M : Submodule K.O B.A) (y : B.Aˣ) :
    mulLat K.O ((y⁻¹ : B.Aˣ) : B.A) (mulLat K.O (y : B.A) M) = M := by
  ext z
  rw [mem_mulLat, mem_mulLat, inv_inv, Units.inv_mul_cancel_left]

theorem mulLat_mem_Lin (y : B.Aˣ) (hy : B.σ (y : B.A) = y) (M : Submodule K.O B.A) (hM : M ∈ B.Lin) :
    mulLat K.O (y : B.A) M ∈ B.Lin := by
  obtain ⟨⟨hfg, hsp⟩, hg, hσ⟩ := hM
  have hyi : B.σ ((y⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((y⁻¹ : B.Aˣ) : B.A) = B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  refine ⟨⟨hfg.map _, ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ((mulLat K.O (y : B.A) M : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (y : B.A)) '' (M : Set B.A) := by
      rw [mulLat, Submodule.map_coe]
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    exact ⟨((y⁻¹ : B.Aˣ) : B.A) * x, by simp⟩
  · rw [mem_mulLat] at hz ⊢
    rw [mul_left_comm]
    exact hg _ hz
  · rw [mem_mulLat] at hz ⊢
    have := hσ _ hz
    rwa [map_mul, hyi] at this

theorem sgnLat_mulLat (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by
  classical
  obtain ⟨e, he, -⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B M hM hσ
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (y : B.A))
    (LinearMap.mulLeft K.E ((y⁻¹ : B.Aˣ) : B.A)) (by ext x; simp) (by ext x; simp)
  let e' := e.map f
  have he' : ∀ l, e' l = (y : B.A) * e l := fun l => rfl
  have hspan : mulLat K.O (y : B.A) M = Submodule.span K.O (Set.range e') := by
    rw [← he, mulLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hN : Algebra.norm K.E (y : B.A) ≠ 0 := (y.isUnit.map (Algebra.norm K.E)).ne_zero
  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e' l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) * Algebra.leftMulMatrix e (y : B.A) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [he' l]
    conv_lhs => rw [← e.sum_repr ((y : B.A) * e l)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [hspan, SgnBasis.sgnLat_span_basis, ← he, SgnBasis.sgnLat_span_basis, hmat, Matrix.det_mul,
    ← Algebra.norm_eq_matrix_det, Desc.eta_mul (det_trace_ne_zero B hP e) hN, mul_comm]

theorem inDual_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (t : B.A) :
    InDual B t (mulLat K.O (y : B.A) M) ↔ InDual B ((y : B.A) * t) M := by
  unfold InDual
  constructor
  · intro h z hz
    have := h ((y : B.A) * z) (by rw [mem_mulLat, Units.inv_mul_cancel_left]; exact hz)
    have e : t * ((y : B.A) * z) = (y : B.A) * t * z := by ring
    rwa [e] at this
  · intro h z hz
    rw [mem_mulLat] at hz
    have := h _ hz
    have e : (y : B.A) * t * (((y⁻¹ : B.Aˣ) : B.A) * z) = t * z := by
      rw [mul_comm (y : B.A) t, mul_assoc, Units.mul_inv_cancel_left]
    rwa [e] at this

theorem term_mulLat {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by
  classical
  unfold term dlt
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indM
    have e : ((y⁻¹ : B.Aˣ) : B.A) * ((∏ j ∈ J, π j) * ((y : B.A) * u)) = (∏ j ∈ J, π j) * u := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    simp only [mem_mulLat, e]
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indD
    have e : (y : B.A) * ((∏ j ∈ J, π j) * s) = (∏ j ∈ J, π j) * ((y : B.A) * s) := by ring
    simp only [inDual_mulLat, e]

theorem HH_mul_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A),
    B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  intro K B ι π I I' u s y hB hy
  obtain ⟨⟨yu, rfl⟩, hσ⟩ := hy
  have hσ' : B.σ ((yu⁻¹ : B.Aˣ) : B.A) = ((yu⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) = 1 := by
      conv_lhs => rw [← hσ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((yu⁻¹ : B.Aˣ) : B.A) = B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) * ((yu⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  unfold HH
  rw [mul_finsum_mem]
  symm
  refine finsum_mem_eq_of_bijOn (fun M => mulLat K.O (yu : B.A) M) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun M => mulLat K.O ((yu⁻¹ : B.Aˣ) : B.A) M) ⟨fun M _ => ?_, fun M _ => ?_⟩
      (fun M hM => mulLat_mem_Lin B yu hσ M hM) (fun M hM => ?_)
    · exact mulLat_inv B M yu
    · have := mulLat_inv B M yu⁻¹
      rwa [inv_inv] at this
    · have := mulLat_mem_Lin B yu⁻¹ hσ' M hM
      exact this
  · intro M hM
    rw [sgnLat_mulLat B hB.2 M hM.1 hM.2.2 yu, term_mulLat]
    ring

end GlobalTheory.UnitLemma.Move
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnitStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A), B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  first | exact @GlobalTheory.UnitLemma.Move.HH_mul_unit | exact GlobalTheory.UnitLemma.Move.HH_mul_unit | (intros; apply GlobalTheory.UnitLemma.Move.HH_mul_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtale
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_char (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := ψ x)).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
  have h1 : ψ (z - x) = 1 := hψ.1 _ (by simpa [dist_eq_norm] using hz)
  calc ψ x = ψ x * ψ (z - x) := by rw [h1, mul_one]
    _ = ψ z := by rw [← AddChar.map_add_eq_mul]; congr 1; abel

theorem kerK_eq (A : Et F E) (ψ : AddChar F ℂ) :
    A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
  funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]

theorem continuous_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (y : A.K) :
    Continuous fun x => A.kerK ψ x y := by
  have hl : Continuous ((Algebra.trace F A.K).comp (LinearMap.mulRight F y)) :=
    IsModuleTopology.continuous_of_linearMap _
  exact ((continuous_char ψ hψ).comp hl).congr (fun x => by simp [Et.kerK, Et.psiK])

theorem integrable_mul_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f : A.K → ℂ} (hf : IsTest f) (y : A.K) :
    Integrable (fun x => f x * A.kerK ψ x y) μ :=
  (hf.1.continuous.mul (continuous_kerK A ψ hψ y)).integrable_of_hasCompactSupport hf.2.mul_right

theorem fourB_sub (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f g : A.K → ℂ} (hf : IsTest f) (hg : IsTest g) (y : A.K) :
    fourB μ (A.kerK ψ) (f - g) y = fourB μ (A.kerK ψ) f y - fourB μ (A.kerK ψ) g y := by
  unfold fourB
  rw [← integral_sub (integrable_mul_kerK A ψ hψ μ hf y) (integrable_mul_kerK A ψ hψ μ hg y)]
  congr 1; funext x; simp [sub_mul]

theorem lintegral_sq_eq_ofReal {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {g : X → ℂ} (hg : IsTest g) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc : Continuous fun x => ‖g x‖ ^ 2 := (hg.1.continuous.norm).pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ g) := hg.2.comp_left (by simp)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable [Unram F E]

theorem isTest_fourB (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) : IsTest (fourB μK (A.kerK ψ) f) := by
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  rw [kerK_eq A ψ]
  exact (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd).2 μK hsd.1 f hf

theorem plancherel (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) :
    ∫⁻ y, ‖fourB μK (A.kerK ψ) f y‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μK := by
  haveI := hsd.1
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hB := kerK_eq A ψ
  have hP := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd μK
    hsd.1).2 (hB ▸ hsd) f hf
  rw [lintegral_sq_eq_ofReal μK (isTest_fourB A ψ hψ μK hsd hf), lintegral_sq_eq_ofReal μK hf, hB, hP]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def box (A : Et F E) (c : F) : Set A.K := {z | c • z ∈ A.OK}

theorem isOpen_box (A : Et F E) (hO : IsOpen A.OK) (c : F) : IsOpen (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isClosed_box (A : Et F E) (hO : IsClosed A.OK) (c : F) : IsClosed (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isCompact_box (A : Et F E) (hO : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsCompact (box A c) :=
  (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).2 hO

theorem isTest_indicator_box (A : Et F E) {u : A.K → ℂ} (hu : IsLocallyConstant u) (hOo : IsOpen A.OK)
    (hOc : IsClosed A.OK) (hOk : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsTest ((box A c).indicator u) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_box A hOk hc) (isClosed_box A hOc c)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ box A c
  · filter_upwards [(isOpen_box A hOo c).mem_nhds hx, (IsLocallyConstant.iff_eventually_eq u).1 hu x] with y hy h
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, h]
  · filter_upwards [(isClosed_box A hOc c).isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem fourB_indicator_box (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by
  unfold fourB
  have h : ∀ x, (box A c).indicator u x * A.kerK ψ x y = (box A c).indicator (fun x => u x * A.kerK ψ x y) x :=
    fun x => by by_cases hx : x ∈ box A c <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator hM]
  congr 1; funext z
  rw [Et.kerK, neg_mul, neg_neg, mul_comm z y]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

theorem eq_zero_of_tendsto_fourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd u hu hT hlim
  haveI := hsd.1
  obtain ⟨-, -, -, -, -, -, -, -, hnull, hOo, hOk, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hOc : IsClosed A.OK := by
    have hRo : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by rw [← hR] at hOo; exact hOo
    rw [← hR]; exact R.toAddSubgroup.isClosed_of_isOpen hRo
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1
  have hne : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n (norm_pos_iff.1 hϖ0)
  have hpow' : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hpow, Eventually.of_forall hne⟩
  set M : ℕ → Set A.K := fun n => box A (ϖ ^ n) with hMdef
  have hMm : ∀ n, MeasurableSet (M n) := fun n => (isOpen_box A hOo _).measurableSet
  set g : ℕ → A.K → ℂ := fun n => (M n).indicator u with hgdef
  have hg : ∀ n, IsTest (g n) := fun n => isTest_indicator_box A hu hOo hOc hOk (hne n)
  have hTc : ∀ n, Continuous (fourB μK (A.kerK ψ) (g n)) := fun n =>
    (isTest_fourB A ψ hψ μK hsd (hg n)).1.continuous
  have huc : Continuous u := hu.continuous
  have hum : Measurable fun z => ‖u z‖ₑ ^ 2 := (huc.measurable.enorm).pow_const 2
  set b : ℕ → ENNReal := fun n => ∫⁻ z, (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z ∂μK with hbdef
  have hev : ∀ z : A.K, ∀ᶠ n in atTop, z ∈ M n := by
    intro z
    have ht : Tendsto (fun n : ℕ => ϖ ^ n • z) atTop (𝓝 0) := by
      simpa using hpow.smul_const z
    exact ht (hOo.mem_nhds h0)
  have hb : Tendsto b atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μK)
      (F := fun n z => (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z) (f := fun _ => 0) (fun z => ‖u z‖ₑ ^ 2)
      (fun n => hum.indicator (hMm n).compl) (fun n => ae_of_all _ fun z => Set.indicator_le_self _ _ z) hT.ne
      (ae_of_all _ fun z => tendsto_const_nhds.congr'
        ((hev z).mono fun n hn => (Set.indicator_of_notMem (fun h : z ∈ (M n)ᶜ => h hn) _).symm))
    simpa using this
  have hlimF : ∀ y : A.K, IsUnit y → Tendsto (fun n => fourB μK (A.kerK ψ) (g n) y) atTop (𝓝 0) := by
    intro y hy
    exact ((hlim (-y) hy.neg).comp hpow').congr fun n => (fourB_indicator_box A ψ μK u _ (hMm n) y).symm
  have hae : ∀ᵐ y ∂μK, IsUnit y := ae_iff.2 (hnull μK hsd.1)
  have key : ∀ N, ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK ≤ b N := by
    intro N
    rw [← plancherel A ψ hψ μK hsd (hg N)]
    have hFd : ∀ n, ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK
        = ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK := by
      intro n
      have := plancherel A ψ hψ μK hsd (f := g N - g n) ⟨(hg N).1.sub (hg n).1, (hg N).2.sub (hg n).2⟩
      simp only [Pi.sub_apply] at this
      rw [← this]
      congr 1; funext y
      rw [fourB_sub A ψ hψ μK (hg N) (hg n) y]
    have hpt : ∀ n x, ‖g N x - g n x‖ₑ ^ 2 ≤
        (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x := by
      intro n x
      by_cases h1 : x ∈ M N <;> by_cases h2 : x ∈ M n <;> simp [g, h1, h2]
    have hle : ∀ n, ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK ≤ b N + b n := by
      intro n
      calc _ ≤ ∫⁻ x, ((M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK :=
            lintegral_mono (hpt n)
        _ = b N + b n := lintegral_add_left (hum.indicator (hMm N).compl) _
    have hliminf : ∀ᵐ y ∂μK,
        liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop
          = ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 := by
      filter_upwards [hae] with y hy
      have ht := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((tendsto_const_nhds (x := fourB μK (A.kerK ψ) (g N) y)).sub (hlimF y hy)))
      simpa [Function.comp_def] using ht.liminf_eq
    calc ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 ∂μK
        = ∫⁻ y, liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop ∂μK :=
          lintegral_congr_ae (hliminf.mono fun y h => h.symm)
      _ ≤ liminf (fun n => ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK) atTop :=
          lintegral_liminf_le' fun n => ((((hTc N).sub (hTc n)).measurable.enorm).pow_const 2).aemeasurable
      _ = liminf (fun n => ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK) atTop := by simp_rw [hFd]
      _ ≤ liminf (fun n => b N + b n) atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = b N := by
          have : Tendsto (fun n => b N + b n) atTop (𝓝 (b N + 0)) := tendsto_const_nhds.add hb
          simpa using this.liminf_eq
  have hsplit : ∀ N, ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := by
    intro N
    calc ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK
        = ∫⁻ x, (‖g N x‖ₑ ^ 2 + (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK := by
          congr 1; funext x
          by_cases h : x ∈ M N <;> simp [g, h]
      _ = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := lintegral_add_right _ (hum.indicator (hMm N).compl)
  have hT0 : ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = 0 := by
    refine le_antisymm ?_ (by simp)
    have h2 : Tendsto (fun N => b N + b N) atTop (𝓝 0) := by simpa using hb.add hb
    exact ge_of_tendsto' h2 fun N => (hsplit N).trans_le (add_le_add (key N) le_rfl)
  have hae0 : u =ᵐ[μK] 0 := by
    filter_upwards [(lintegral_eq_zero_iff hum).1 hT0] with z hz
    simpa using hz
  exact (Continuous.ae_eq_iff_eq μK huc continuous_const).1 hae0

end GlobalTheory.PlancherelZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  first | exact @GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | exact GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | (intros; apply GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier <;> assumption)
end
end
