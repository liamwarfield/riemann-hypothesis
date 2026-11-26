module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisCoboundaryEventuallyMemPrimePowLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryMemLatticeInvLOfMonodromyEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemLatticeOnKummerTowerGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemLatticeOnKummerTowerGalois
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleKinf

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G] {T : LocLat G ℚ_[l] K O}

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp [map_mul]

theorem isCrisVal_add (P : PhiMod O K l e a ι) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T)
    {w w' : ι → OW l O} {b b' : TW (OB l O) T} (h : IsCrisVal t ϖ P jB w b)
    (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, hw, hb⟩ := h
  obtain ⟨m', c', hm', hw', hb'⟩ := h'
  refine ⟨m * m', m' • c + m • c', ?_, ?_, ?_⟩
  · rw [map_mul]; exact hm.mul hm'
  · rw [map_add (f := _), inclL_smul, inclL_smul, ← hw, ← hw', smul_smul, smul_smul, smul_add, map_mul,
      mul_comm (inclO l O m) (inclO l O m')]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      ext1 i
      simp [map_add (f := _), map_mul]
    rw [e1, map_add (f := _), map_smul, map_smul, ← hb, ← hb', map_mul, smul_add, smul_smul, smul_smul,
      mul_comm (toB l O m') (toB l O m)]

theorem cocycle_mem_lattice_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hpot g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, hσ, -, hval, rfl⟩ := hpot
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_muSemidirectCyclic_cover_of_mem_GKinf_coeffs l a e O K t ϖ (sQ l g) hg

  have hσfix : actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) :=
    GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc g γ hγ σ σ (hσ γ).symm

  have hyfix : R.I.act (sQ l g) g (toW t ϖ D.toPhiMod ⟨y, hy⟩) = toW t ϖ D.toPhiMod ⟨y, hy⟩ :=
    R.desc g γ hγ ⟨y, hy⟩ ⟨y, hy⟩ (((Descent.mem_invOf _).1 hyY).2 γ).symm

  set w := R.I.act (sQ l g) g m₀ - m₀ with hw
  have hφw : phiW t ϖ D.toPhiMod w = w := by
    have h1 : phiW t ϖ D.toPhiMod w - w =
        R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀ - m₀) - (phiW t ϖ D.toPhiMod m₀ - m₀) := by
      rw [hw, map_sub, map_sub, R.I.act_phiW]; abel
    rw [hm₀, hyfix, sub_self] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨x, hx⟩ : w ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hφw
  obtain ⟨-, huniq, -, hofT, hgal⟩ :=
    (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp
  have h2 : IsCrisVal t ϖ D.toPhiMod R.jB (R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀))
      (actB (sQ l) T g b₀) := hgal g (R.stable g) _ _ hval
  have h3 : R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀) = phiW t ϖ D.toPhiMod m₀ + R.I.ofT x := by
    rw [R.I.act_phiW, hx, ← hφw, hw, map_sub]; abel
  rw [h3] at h2
  have h4 := huniq _ _ _ h2 (GlobalTheory.CocycleKinf.isCrisVal_add D.toPhiMod R.jB hval (hofT x))
  refine ⟨-x, ?_⟩
  rw [map_sub, hσfix, h4, tmul_neg]
  abel

end GlobalTheory.CocycleKinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemLatticeOnKummerTowerGaloisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | exact GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | (intros; apply GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticePrimePowSmulTendstoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticePrimePowSmulTendstoZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TContNbhd

theorem norm_le_one_of_isIntegral' {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_le (LL : FinExt l) (r : ℤ_[l]) : ‖algebraMap ℤ_[l] ↥LL.1 r‖ ≤ 1 := by
  change ‖((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l)‖ ≤ 1
  have : ((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l]) := rfl
  rw [this, norm_algebraMap']
  exact PadicInt.norm_le_one r

theorem norm_le_one_of_mem (LL : FinExt l) (c : ↥(OL LL)) : ‖(c : ↥LL.1)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (R := ℤ_[l]) (norm_algebraMap_le LL) c.2

theorem norm_natCast_lt_one (LL : FinExt l) : ‖(l : ↥LL.1)‖ < 1 := by
  change ‖((l : ↥LL.1) : PadicAlgCl l)‖ < 1
  have : ((l : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) → ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := by
  intro l _ LL T U hU
  classical
  obtain ⟨s, hs⟩ := T.L.fg
  let f : (↥s → ↥LL.1) → T.V := fun a => ∑ t : ↥s, a t • (t : T.V)
  have hf : Continuous f := continuous_finsetSum _ fun t _ => (continuous_apply t).smul continuous_const
  have h0 : f 0 = 0 := by simp [f]
  have hpre : f ⁻¹' U ∈ nhds (0 : ↥s → ↥LL.1) := hf.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_lt_one LL)
  refine ⟨m, fun x hx => ?_⟩
  rw [← hs] at hx
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hx
  let a : ↥s → ↥LL.1 := fun t => (l : ↥LL.1) ^ m * ((c t : ↥(OL LL)) : ↥LL.1)
  have ha : ‖a‖ < ε := by
    refine (pi_norm_lt_iff hε).2 fun t => ?_
    calc ‖a t‖ = ‖(l : ↥LL.1)‖ ^ m * ‖((c t : ↥(OL LL)) : ↥LL.1)‖ := by simp [a, norm_pow]
      _ ≤ ‖(l : ↥LL.1)‖ ^ m * 1 := by gcongr; exact norm_le_one_of_mem LL (c t)
      _ < ε := by rw [mul_one]; exact hm
  have hfa : f a = ((l : ↥LL.1) ^ m) • x := by
    rw [← hc, Finset.smul_sum]
    simp only [f, a]
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul]
    congr 1
    exact algebraMap_smul (↥LL.1) (c t) (t : T.V)
  have : a ∈ f ⁻¹' U := hball (mem_ball_zero_iff.2 ha)
  rw [Set.mem_preimage, hfa] at this
  exact this
end GlobalTheory.TContNbhd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticePrimePowSmulTendstoZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) → ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := by
  first | exact @GlobalTheory.TContNbhd.main | exact GlobalTheory.TContNbhd.main | (intros; apply GlobalTheory.TContNbhd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulBcrisGaloisLatticeInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TContInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, -, -⟩ := GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  haveI : Nontrivial (Per.BdR l) := ⟨(GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.exists_pair_ne⟩
  exact ι.domain_nontrivial

theorem zl_bcris_injective (l : ℕ) [Fact l.Prime] : Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  haveI := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) z) := by
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]
    exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)
  exact hu.ne_zero hz

theorem includeLeft_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (zl_bcris_injective l)
  intro x y hxy
  apply (TensorProduct.rid ℤ_[l] O).symm.injective
  apply h
  simpa [Algebra.TensorProduct.algebraMap_apply] using hxy

theorem one_tmul_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] :
    Function.Injective (fun x : M => (1 : OB l O) ⊗ₜ[O] x) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap O (OB l O)) (includeLeft_injective l O)
  intro x y hxy
  apply (TensorProduct.lid O M).symm.injective
  apply h
  simpa [← Algebra.TensorProduct.one_def] using hxy

end GlobalTheory.TContInj

theorem GlobalTheory.TContInj.main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  intro l _ LL T
  haveI : Module.Free (↥(OL LL)) ↥T.L.T := T.L.free
  exact GlobalTheory.TContInj.one_tmul_injective l ↥(OL LL) ↥T.L.T
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrime
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CobCont

set_option synthInstance.maxHeartbeats 400000

theorem inj1 : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL),
    Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  exact @_root_.GlobalTheory.TContInj.main

theorem nbhd : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) →
    ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero

theorem cont1 : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l),
      ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem o_smul_mem (T : QLat LL) (o : ↥(OL LL)) (x : T.V) (hx : x ∈ T.L.T) : (o : ↥LL.1) • x ∈ T.L.T := by
  have := T.L.T.smul_mem o hx
  rwa [← algebraMap_smul ↥LL.1 o x] at this

theorem lpow_smul_mem (T : QLat LL) (n : ℕ) (x : T.V) (hx : x ∈ T.L.T) : (l : ↥LL.1) ^ n • x ∈ T.L.T := by
  have := o_smul_mem T ((l : ↥(OL LL)) ^ n) x hx
  simpa using this

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem actB_tmul_one (T : QLat LL) (g : Gl l) (x : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] T.actT g x := by
  simp [actB, TWact]

theorem galOB_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (o : OB l O) :
    galOB O (g * h) o = galOB O g (galOB O h o) := by
  induction o using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w =>
    exact congrArg (fun z => a ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ w)

theorem actT_mul (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) : T.actT (g * h) x = T.actT g (T.actT h x) :=
  Subtype.ext (by
    show T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h x)
    rw [map_mul]; rfl)

theorem actB_tmul (T : QLat LL) (g : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T g (o ⊗ₜ[↥(OL LL)] x) = (galOB ↥(OL LL) (sQ l g) o) ⊗ₜ[↥(OL LL)] T.actT g x :=
  TensorProduct.map_tmul _ _ _ _

set_option maxHeartbeats 1000000 in
theorem actB_mul_a (T : QLat LL) (g h : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T (g * h) (o ⊗ₜ[↥(OL LL)] x) = actB (sQ l) T g (actB (sQ l) T h (o ⊗ₜ[↥(OL LL)] x)) := by
  have e1 := actB_tmul T (g*h) o x
  have e2 := actB_tmul T h o x
  have e3 := actB_tmul T g (galOB _ (sQ l h) o) (T.actT h x)
  refine e1.trans (Eq.trans ?_ ((congrArg (actB (sQ l) T g) e2).trans e3).symm)
  refine congrArg₂ (fun a b => a ⊗ₜ[↥(OL LL)] b) ?_ (actT_mul T g h x)
  rw [map_mul]
  exact galOB_mul' _ _ o

theorem actB_mul (T : QLat LL) (g h : Gl l) (y : TW (OB l ↥(OL LL)) T) :
    actB (sQ l) T (g * h) y = actB (sQ l) T g (actB (sQ l) T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o x => exact actB_mul_a T g h o x

theorem abs_cocycle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (Fg Fh Fgh : M →ₗ[R] M)
    (hmul : ∀ y, Fgh y = Fg (Fh y)) (b y1 y2 y3 : M) (r : R) (e1 : y1 = r • (Fg b - b))
    (e2 : y2 = r • (Fh b - b)) (e3 : y3 = r • (Fgh b - b)) : y3 = Fg y2 + y1 := by
  rw [e3, e2, e1, hmul, map_smul, map_sub, ← smul_add]
  congr 1
  abel

theorem pow_le_mem (T : QLat LL) {k n : ℕ} (hk : k ≤ n) (v : T.V) (hv : (l : ↥LL.1) ^ k • v ∈ T.L.T) :
    (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact lpow_smul_mem T _ _ hv


set_option maxHeartbeats 2000000 in
theorem cocycle (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c)
    (g h : Gl l) : c (g * h) = c g + T.ρ g (c h) := by
  obtain ⟨n1, h1⟩ := exists_pow_smul_mem T (c g)
  obtain ⟨n2, h2⟩ := exists_pow_smul_mem T (c h)
  obtain ⟨n3, h3⟩ := exists_pow_smul_mem T (c (g * h))
  have m1 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h1
  have m2 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h2
  have m3 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h3
  have e1 := hc g _ ⟨_, m1⟩ rfl
  have e2 := hc h _ ⟨_, m2⟩ rfl
  have e3 := hc (g * h) _ ⟨_, m3⟩ rfl
  have key : (⟨_, m3⟩ : ↥T.L.T) = T.actT g ⟨_, m2⟩ + ⟨_, m1⟩ := by
    apply inj1 l LL T
    have := abs_cocycle (actB (sQ l) T g) (actB (sQ l) T h) (actB (sQ l) T (g * h)) (actB_mul T g h) _ _ _ _ _ e1 e2 e3
    refine this.trans ?_
    refine (congrArg (· + _) (actB_tmul_one T g _)).trans ?_
    exact (TensorProduct.tmul_add _ _ _).symm
  have key' := congrArg (fun z : ↥T.L.T => (z : T.V)) key
  simp only [Submodule.coe_add] at key'
  change (l : ↥LL.1) ^ (n1 + n2 + n3) • c (g * h) =
    T.ρ g ((l : ↥LL.1) ^ (n1 + n2 + n3) • c h) + (l : ↥LL.1) ^ (n1 + n2 + n3) • c g at key'
  rw [map_smul, ← smul_add] at key'
  have hl : ((l : ↥LL.1) ^ (n1 + n2 + n3)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  rw [smul_right_injective T.V hl key', add_comm]

theorem c_one (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c) :
    c 1 = 0 := by
  have h := cocycle T b c hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem contAt_one (hl2 : l ≠ 2) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V)
    (hc : IsCobOf (sQ l) T b c) : ContinuousAt c 1 := by
  rw [ContinuousAt, c_one T b c hc]
  intro U hU
  obtain ⟨m, hm⟩ := nbhd l LL T U hU
  rw [Filter.mem_map]
  filter_upwards [cont1 l hl2 LL T b c hc m] with g hg
  obtain ⟨x, hx, e⟩ := hg
  rw [Set.mem_preimage, e]
  exact hm x hx

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  intro l _ hl2 LL T b c hc
  refine ⟨?_, cocycle T b c hc⟩
  have h1 := contAt_one hl2 T b c hc
  have hρ : ∀ g : Gl l, Continuous (T.ρ g) := fun g =>
    IsModuleTopology.continuous_of_linearMap (T.ρ g)
  rw [continuous_iff_continuousAt]
  intro g0
  have e : c = fun g => c g0 + T.ρ g0 (c (g0⁻¹ * g)) := by
    funext g
    rw [← cocycle T b c hc, mul_inv_cancel_left]
  rw [e]
  refine continuousAt_const.add ((hρ g0).continuousAt.comp ?_)
  refine ContinuousAt.comp (f := fun g => g0⁻¹ * g) ?_ (continuous_const.mul continuous_id).continuousAt
  simpa using h1

end GlobalTheory.CobCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_mem_cocycles_odd_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  first | exact @GlobalTheory.CobCont.main | exact GlobalTheory.CobCont.main | (intros; apply GlobalTheory.CobCont.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.MonZero

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem galOB_mul (g h : GQ l) (r : OB l O) :
    galOB O (g * h) r = galOB O g (galOB O h r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o w =>
    simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun z => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 g h w)

theorem actB_mul (T : LocLat (Gl l) ℚ_[l] K O) (g h : Gl l) (x : TW (OB l O) T) :
    actB (sQ l) T (g * h) x = actB (sQ l) T g (actB (sQ l) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r t =>
    have ht : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, galOB_mul, ht]

theorem actB_one_tmul (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (t : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l O) ⊗ₜ[O] t) = (1 : OB l O) ⊗ₜ[O] T.actT g t := by
  simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem step_mul {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b) (g h k : Gl l)
    (hg : g = h * k) (hh : sQ l h ∈ GK (ϖ.field a)) (hk : sQ l k ∈ ϖ.GKinf) :
    ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  obtain ⟨xk, hxk⟩ := GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois l a e O K t ϖ ι η H D T R y hy b hb k hk
  obtain ⟨xh, hxh⟩ := GlobalTheory.T.potentialCocycle_mem_lPow_lattice l a e O K t ϖ ι η H D T R hηH hlH y hy c hc b hb h hh
    (GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero hF l a e O K t ϖ hl2 ι η H D T R y hy hM b hb h hh)
  refine ⟨(l : O) ^ c • T.actT h xk + xh, ?_⟩
  have e1 : actB (sQ l) T g b - b = actB (sQ l) T h (actB (sQ l) T k b - b) + (actB (sQ l) T h b - b) := by
    rw [hg, actB_mul, map_sub]; abel
  rw [e1, hxk, actB_one_tmul, smul_add, hxh, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]

theorem cob_of (T : LocLat (Gl l) ℚ_[l] K O) (b : TW (OB l O) T) (c : ℕ) (X : Gl l → ↥T.L.T)
    (hX : ∀ g, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] X g) :
    IsCobOf (sQ l) T b (fun g => ((l : K) ^ c)⁻¹ • (X g : T.V)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  intro g n x hx
  apply smul_cancel T c
  rw [smul_comm ((l : O) ^ c) ((l : O) ^ n), hX g, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [← algebraMap_smul K ((l : O) ^ c), ← algebraMap_smul K ((l : O) ^ n), map_pow, map_pow, map_natCast, hx,
    smul_comm ((l : K) ^ n), smul_smul ((l : K) ^ c), mul_inv_cancel₀ hne, one_smul]

theorem exists_cob {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b)
    (hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf) :
    ∃ κ : Gl l → T.V, IsCobOf (sQ l) T b κ ∧ ∀ g, (l : K) ^ c • κ g ∈ T.L.T := by
  have hX : ∀ g : Gl l, ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
    intro g
    obtain ⟨h, k, hg, hh, hk⟩ := hdec g
    exact step_mul t ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb g h k hg hh hk
  choose X hX using hX
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine ⟨_, cob_of T b c X hX, fun g => ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact (X g).2

end GlobalTheory.BKGal.MonZero

theorem GlobalTheory.BKGal.classOf_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  intro hF l _ a e _ _ ϖ LL _ _ ι _ _ η H D T R Pl AI hstd hηH hlH y hy hM c hc
  have hl2 : l ≠ 2 := by omega
  obtain ⟨b, hb⟩ := (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).1 y hy
  have hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf := by
    intro g
    obtain ⟨h, hh, k, hk, hgk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).1 (sQ l g)
    let hG : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
    refine ⟨hG, hG⁻¹ * g, (mul_inv_cancel_left hG g).symm, hh, ?_⟩
    have e1 : sQ l (hG⁻¹ * g) = k := by
      rw [map_mul, map_inv, show sQ l g = h * k from hgk]
      show h⁻¹ * (h * k) = k
      group
    rw [e1]; exact hk
  obtain ⟨κ, hcob, hT⟩ := GlobalTheory.BKGal.MonZero.exists_cob (thetaW a LL) ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb hdec
  have hcl : R.ClassOf y κ := ⟨b, hb, hcob⟩
  have hZ1c : κ ∈ continuousCocycles T.ρ := GlobalTheory.T.coboundary_mem_cocycles_odd_prime l hl2 LL T b κ hcob
  obtain ⟨β, -, -, -, hf⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hstd
  have hZ1f : κ ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := (hf κ hZ1c).2 ⟨b, hcob⟩
  refine ⟨(l : ↥LL.1) ^ c • κ, ?_, (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).2.2.1 y κ c hcl⟩
  refine ⟨⟨(continuousCocycles T.ρ).smul_mem _ hZ1c, ?_⟩, (finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ).smul_mem _ hZ1f⟩
  intro g _
  exact hT g
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisClass_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  first | exact @GlobalTheory.BKGal.classOf_of_mon_eq_zero | exact GlobalTheory.BKGal.classOf_of_mon_eq_zero | (intros; apply GlobalTheory.BKGal.classOf_of_mon_eq_zero <;> assumption)
end
