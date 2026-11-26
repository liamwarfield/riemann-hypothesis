module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.ValueFil

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem toB_tmul_pt {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Per.Ainf l) :
    toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w := by
  rw [GlobalTheory.RingIface.aB_alg]
  rfl

theorem core_ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) := by
  rw [GlobalTheory.RingIface.aB_alg, C.ι_j, GlobalTheory.MemLoc.LogEx.algebraMap_acris, C.j_cris.on0, Subalgebra.coe_algebraMap]
  rfl

theorem one_mem_filZero : (1 : Per.BdR l) ∈ Per.FilD l 0 :=
  (GlobalTheory.MemLoc.filD_laws l).2.1

theorem alg_mem_filZero (u : Per.BdRp l) : algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filZero

theorem isUnit_aDp_of_theta {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    IsUnit (GlobalTheory.MemLoc.aDp l x) :=
  (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hx)

theorem ι_mem_filZero_of_mul (C : GlobalTheory.MemLoc.Core l) {d : Per.Bcris l} {x : Per.Ainf l} {n : ℕ}
    (hd : d * Per.aB l x ^ n = 1) (hx : IsUnit (GlobalTheory.MemLoc.aDp l x)) : C.ι d ∈ Per.FilD l 0 := by
  obtain ⟨v, hv⟩ := hx
  have h1 : C.ι d * algebraMap (Per.BdRp l) (Per.BdR l) ((v : Per.BdRp l) ^ n) = 1 := by
    rw [map_pow, hv, ← core_ι_aB, ← map_pow, ← map_mul, hd, map_one]
  have h2 : C.ι d = algebraMap (Per.BdRp l) (Per.BdR l) (((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
    calc C.ι d = C.ι d * algebraMap (Per.BdRp l) (Per.BdR l)
          ((v : Per.BdRp l) ^ n * ((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
          rw [← mul_pow, Units.mul_inv, one_pow, map_one, mul_one]
      _ = _ := by rw [map_mul, ← mul_assoc, h1, one_mul]
  rw [h2]
  exact alg_mem_filZero _

theorem theta_σA_ne_zero (g : Per.Gq l) {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    (Per.θ l (Per.σA g x) : ℂ_[l]) ≠ 0 := by
  intro h
  apply hx
  have h' : Per.σC g (Per.θ l x : ℂ_[l]) = 0 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, ← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2,
      (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact h
  rw [← norm_eq_zero, ← GlobalTheory.RingBasics.norm_σC g, h', norm_zero]

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWact_TWincl (h : GQ l) (T : LocLat G ℚ_[l] K O) (g : G) (z : TW (OA l O) T) :
    TWact (galOB O h) T g (TWincl (toB l O) T z) = TWincl (toB l O) T (TWact (galOA O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    rw [toB, AlgHom.comp_apply, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem smul_TWincl_mem (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l 0) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ Submodule.span O {w : TW (OB l O) T |
      ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, core_ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add (f := _), mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add (f := _), smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.ValueFil


open GlobalTheory.BKGal.ValueFil in
theorem GlobalTheory.BKGal.value_mem_filtration_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hy m₀ h1

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ

  obtain ⟨hMA, -⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
    ⟨y, hy⟩ hyY.1 m₀ h1
  obtain ⟨-, hK2, hK3, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
  obtain ⟨z, hz⟩ := hK2 _ hMA

  have hLA : ∀ (c : OA l O) {v : ι → OW l O}, v ∈ LA t ϖ D.toPhiMod → inclO l O c • v ∈ LA t ϖ D.toPhiMod := by
    rintro c _ ⟨d, rfl⟩
    exact ⟨fun i => c * d i, inclL_smul_coord t ϖ D.toPhiMod c d⟩
  have hT : ∀ z' : TW (OA l O) T, inclO l O (1 ⊗ₜ (muOf ε ^ H)) • R.I.j.symm (TWincl (inclO l O) T z') ∈
      LA t ϖ D.toPhiMod := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
    | tmul c x =>
      have e1 : TWincl (inclO l O) T (c ⊗ₜ[O] x) = inclO l O c • ((1 : OW l O) ⊗ₜ[O] x) := by
        rw [smul_tmul', smul_eq_mul, mul_one]; rfl
      rw [e1, map_smul, smul_comm]
      exact hLA c (hK3 x)
    | add c c' hc hc' => rw [map_add (f := _), map_add (f := _), smul_add]; exact add_mem hc hc'
  obtain ⟨cc, hcc⟩ := hT z
  rw [← hz, LinearEquiv.symm_apply_apply] at hcc

  have hB := R.cmp cc ((1 ⊗ₜ (muOf ε ^ H) : OA l O) • z) (by
    rw [hcc, map_smul, hz, TWincl_smul])
  rw [TWincl_smul] at hB

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [GlobalTheory.RingIface.aB_alg]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  have hνu : IsUnit (Per.aB l (muOf δ)) := by
    have e2 : Per.aB l (muOf ε) = Per.aB l (GlobalTheory.MemLoc.xi ε) * Per.aB l (muOf δ) := by
      rw [← map_mul]
      exact congrArg (Per.aB l) (GlobalTheory.MemLoc.TFil.mu_eq ε)
    rw [e2] at hμu
    exact isUnit_of_mul_isUnit_right hμu
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h
  set n := η + (H + η) with hn
  set d : Per.Bcris l := ((hνu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ n with hd
  have hdn : d * Per.aB l (muOf δ) ^ n = 1 := by
    rw [hd, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  have hm : ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))) : OA l O) =
      (1 ⊗ₜ (muOf ε ^ H)) * ((1 ⊗ₜ (muOf δ ^ η)) * (1 ⊗ₜ (muOf δ ^ (H + η)))) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  refine ⟨((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z,
    ⟨(1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))), cc, ?_, ?_, ?_⟩, ?_⟩
  · have hu : IsUnit (Per.aB l (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η)))) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      exact (hμu.pow H).mul ((hνu.pow _).mul (hνu.pow _))
    have := hu.map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    rw [toB_tmul_pt]
    exact this
  · rw [hcc, hm, map_mul, map_mul, mul_smul, mul_smul]
  · rw [hB, smul_smul]
    congr 1
    rw [toB_tmul_pt, toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    have hdn' : d * Per.aB l (muOf δ) ^ (η + (H + η)) = 1 := hdn
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    linear_combination (Per.aB l (muOf ε) ^ H) * hdn'
  · intro g _ C
    refine sub_mem ?_ (smul_TWincl_mem C T (ι_mem_filZero_of_mul C hdn (isUnit_aDp_of_theta hθν)) z)
    change TWact (galOB O (sQ l g)) T g (((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z) ∈ _
    rw [TWact_smul, TWact_TWincl]
    have hg : Per.σB (sQ l g) d * Per.aB l (Per.σA (sQ l g) (muOf δ)) ^ n = 1 := by
      rw [← (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.1, ← map_pow, ← map_mul, hdn, map_one]
    exact smul_TWincl_mem C T (ι_mem_filZero_of_mul C hg
      (isUnit_aDp_of_theta (theta_σA_ne_zero (sQ l g) hθν))) _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTameStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_mem_filtration_zero_tame : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_mem_filtration_zero | exact GlobalTheory.BKGal.value_mem_filtration_zero | (intros; apply GlobalTheory.BKGal.value_mem_filtration_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DeRhamIdent

section Generic

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
  [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem TWincl_inj {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G ℚ_[l] K O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem fix_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) (r : R)
    (hr : IsUnit r) (m : M) (h : f (r • m) = r • m) : f m = m := by
  obtain ⟨u, rfl⟩ := hr
  have h2 := congrArg (fun y => ((u⁻¹ : Rˣ) : R) • y) h
  simp only [← map_smul, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

end Generic

section Incl

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ι : Type)

theorem inclV_apply (c : ι → OA l O) (i : ι) : inclV l O ι c i = inclO l O (c i) := rfl

theorem inclV_smul (r : OA l O) (c : ι → OA l O) : inclV l O ι (r • c) = inclO l O r • inclV l O ι c := by
  funext i
  simp only [inclV_apply, Pi.smul_apply, smul_eq_mul, map_mul]

theorem inclV_inj [Module.Free ℤ_[l] O] : Function.Injective (inclV l O ι) := fun c d h =>
  funext fun i => inclO_injective (congrFun h i)

end Incl

end GlobalTheory.DeRhamIdent

namespace GlobalTheory.DeRhamIdent

open GlobalTheory.DeRhamIdent


set_option maxHeartbeats 2000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨⟨ε, hε⟩, hεall⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2

  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  set u : (OD l O)ˣ := hu.unit with hudef
  have hu' : (u : OD l O) = toOD l O ν := hu.unit_spec
  have hV := inclV_inj l O ι

  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  have hsum : ∀ c : ι → OA l O,
      inclV l O ι c = ∑ i, inclO l O (c i) • inclV l O ι (Pi.single i 1) := by
    intro c
    funext j
    simp [inclV_apply, Finset.sum_apply, Pi.single_apply]
  have hJ0 : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ν ^ α • z' = ∑ i, c i • z i := by
    intro c z' h
    apply TWincl_inj (inclO l O) inclO_injective T
    calc TWincl (inclO l O) T (ν ^ α • z') = inclO l O (ν ^ α) • I.j (inclV l O ι c) := by
          rw [TWincl_smul, h]
      _ = ∑ i, inclO l O (c i) • I.j (inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← I.j.map_smul, hsum c, Finset.smul_sum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, I.j.map_smul]
      _ = TWincl (inclO l O) T (∑ i, c i • z i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hz i, TWincl_smul]
  let w : ι → TW (OD l O) T := fun i => ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • TWincl (toOD l O) T (z i)
  let jD : (ι → OD l O) →ₗ[OD l O] TW (OD l O) T := ∑ i, (LinearMap.proj i).smulRight (w i)
  have hjD : ∀ d, jD d = ∑ i, d i • w i := fun d => by
    simp [jD, LinearMap.sum_apply]
  have hJ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z' := by
    intro c z' h
    have h2 : toOD l O (ν ^ α) • TWincl (toOD l O) T z' =
        ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← TWincl_smul, hJ0 c z' h, map_sum]
      simp only [TWincl_smul]
    rw [hjD]
    calc ∑ i, toOD l O (c i) • w i
        = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • (toOD l O (ν ^ α) • TWincl (toOD l O) T z') := by rw [h2]
      _ = TWincl (toOD l O) T z' := by
          rw [smul_smul, map_pow, ← hu', ← mul_pow, Units.inv_mul, one_pow, one_smul]

  have hK1' : ∀ x, ∃ y, inclV l O ι y = inclO l O (ν ^ β) • I.ofT x := fun x => LinearMap.mem_range.1 (hK1 x)
  choose Cx hC using hK1'
  let C : ↥T.L.T →ₗ[O] (ι → OA l O) :=
    { toFun := Cx
      map_add' := fun x y => hV (by rw [map_add (f := _), hC, hC, hC, map_add (f := _), smul_add])
      map_smul' := fun o x => hV (by rw [map_smul, hC, hC, map_smul, RingHom.id_apply, smul_comm]) }
  let CA : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) := LinearMap.liftBaseChange (OA l O) C
  have hP1 : ∀ z' : TW (OA l O) T,
      inclV l O ι (CA z') = inclO l O (ν ^ β) • I.j.symm (TWincl (inclO l O) T z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]
    | tmul b x =>
      have e1 : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
        simp [TWincl, TensorProduct.smul_tmul']
      have e2 : I.j.symm ((1 : OW l O) ⊗ₜ[O] x) = I.ofT x := rfl
      rw [e1, I.j.symm.map_smul, e2, LinearMap.liftBaseChange_tmul, inclV_smul]
      change inclO l O b • inclV l O ι (Cx x) = _
      rw [hC, smul_comm]
  let ψ : TW (OD l O) T →ₗ[OD l O] (ι → OD l O) := ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β •
    LinearMap.liftBaseChange (OD l O) (((toOD l O).toLinearMap.compLeft ι) ∘ₗ C)
  have hP2 : ∀ z' : TW (OA l O) T,
      ψ (TWincl (toOD l O) T z') = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β • fun i => toOD l O (CA z' i) := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      funext i
      simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← smul_add]
      congr 1
      funext i
      simp
    | tmul b x =>
      simp only [ψ, CA, TWincl, LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, LinearMap.liftBaseChange_tmul]
      congr 1
      funext i
      simp [C, LinearMap.compLeft, map_mul]
  have hΨ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ψ (TWincl (toOD l O) T z') = fun i => toOD l O (c i) := by
    intro c z' h
    have h1 : CA z' = ν ^ β • c := hV (by rw [hP1, ← h, I.j.symm_apply_apply, inclV_smul])
    rw [hP2, h1]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu', ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have h1 : jD ∘ₗ ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d x
    have e0 : d ⊗ₜ[O] x = d • ((1 : OD l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e0, map_smul, map_smul]
    congr 1
    have hx : I.j (inclV l O ι (Cx x)) = TWincl (inclO l O) T ((ν ^ β) ⊗ₜ[O] x) := by
      rw [hC, I.j.map_smul, I.j_ofT]
      simp [TWincl, TensorProduct.smul_tmul']
    have e3 : TWincl (toOD l O) T ((ν ^ β) ⊗ₜ[O] x) = ((u : OD l O) ^ β) • ((1 : OD l O) ⊗ₜ[O] x) := by
      simp [TWincl, TensorProduct.smul_tmul', hu']
    refine fix_of_unit (jD ∘ₗ ψ) ((u : OD l O) ^ β) ((Units.isUnit u).pow β) _ ?_
    rw [← e3, LinearMap.comp_apply, hΨ _ _ hx, hJ _ _ hx]
  have h2 : ψ ∘ₗ jD = LinearMap.id := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    have hzi : I.j (inclV l O ι (Pi.single i (ν ^ α))) = TWincl (inclO l O) T (z i) := by rw [hc, hz i]
    have e4 : (fun j => toOD l O ((Pi.single i (ν ^ α) : ι → OA l O) j)) =
        ((u : OD l O) ^ α) • (LinearMap.single (OD l O) (fun _ => OD l O) i 1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hu', map_pow]
      · simp [Pi.single_apply, hj]
    refine fix_of_unit (ψ ∘ₗ jD) ((u : OD l O) ^ α) ((Units.isUnit u).pow α) _ ?_
    rw [← e4, LinearMap.comp_apply, hJ _ _ hzi, hΨ _ _ hzi]
  exact ⟨LinearEquiv.ofLinear jD ψ h1 h2, fun c z' h => hJ c z' h⟩

end GlobalTheory.DeRhamIdent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  first | exact @GlobalTheory.DeRhamIdent.main | exact GlobalTheory.DeRhamIdent.main | (intros; apply GlobalTheory.DeRhamIdent.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalCharacterOfRegularCharacterGLn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalCharacterOfRegularCharacterGLn
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.CuspGL
open scoped Classical

noncomputable section

namespace GlobalTheory.GreenRegular

theorem pow_modEq_pow_mod {g : ℕ} (d : ℕ) (hg : 0 < g) (m : ℕ) : g ^ m ≡ g ^ (m % d) [MOD g ^ d - 1] := by
  have h1 : g ^ d ≡ 1 [MOD g ^ d - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul]
  calc (g ^ d) ^ (m / d) * g ^ (m % d) ≡ 1 ^ (m / d) * g ^ (m % d) [MOD g ^ d - 1] :=
        (h1.pow _).mul_right _
    _ = g ^ (m % d) := by rw [one_pow, one_mul]

theorem filter_modEq_congr {g d a b l : ℕ} (h : a ≡ b [MOD g ^ d - 1]) :
    ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]) =
      (Finset.range d).filter fun i => b * g ^ i ≡ l [MOD g ^ d - 1] :=
  Finset.filter_congr fun i _ =>
    ⟨fun h' => ((h.symm.mul_right _).trans h'), fun h' => ((h.mul_right _).trans h')⟩

theorem card_filter_le_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card ≤
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine Finset.card_le_card_of_injOn (fun i => (i + c) % d) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    refine ((pow_modEq_pow_mod d hg (i + c)).symm.mul_left a).trans ?_
    rw [pow_add, mul_comm (g ^ i), ← mul_assoc]
    exact hi.2
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    have h1 : i + c ≡ j + c [MOD d] := hij
    have h2 := Nat.ModEq.add_right_cancel' c h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] at h2

theorem card_filter_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) (hc : c ≤ d) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card =
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine le_antisymm (card_filter_le_shift hg hd a c l) ?_
  have e : a ≡ a * g ^ c * g ^ (d - c) [MOD g ^ d - 1] := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]
    calc a = a * 1 := (mul_one a).symm
      _ ≡ a * g ^ d [MOD g ^ d - 1] := (Nat.modEq_sub (Nat.one_le_pow _ _ hg)).symm.mul_left a
  rw [filter_modEq_congr e]
  exact card_filter_le_shift hg hd (a * g ^ c) (d - c) l

end GlobalTheory.GreenRegular

namespace GlobalTheory.GreenRegular

theorem exists_cusp_of_regular : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  intro g _ d hd K _ _ hK
  have hgp : g.Prime := Fact.out
  have hg : 0 < g := hgp.pos
  have hcF : Nat.card (ZMod g) = g := Nat.card_zmod g
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]
  have hcardU : Nat.card Kˣ = g ^ d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  have hN0 : 0 < g ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hgp.one_lt
    omega
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField (ZMod g)
  let ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let lam : Kˣ →* ℂˣ := (Units.map θ₀).comp (Units.map (ι : K →* AlgebraicClosure (ZMod g)))
  have hlam : ∀ u : Kˣ, ((lam u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) := fun u => rfl
  have hlam_inj : Function.Injective lam := by
    intro u v h
    have h' := congrArg Units.val h
    rw [hlam, hlam] at h'
    exact Units.ext (ι.injective (hθ₀ _ _ ((map_ne_zero ι).2 u.ne_zero) ((map_ne_zero ι).2 v.ne_zero) h'))
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (lam γ) (g ^ d - 1) := by
    rw [← hcardU, ← orderOf_eq_card_of_forall_mem_zpowers hγ, ← orderOf_injective lam hlam_inj γ]
    exact IsPrimitiveRoot.orderOf _
  have hmod : ∀ u : Kˣ, u ^ (g ^ d - 1) = 1 := fun u => by
    rw [← hcardU]; exact pow_card_eq_one'
  have hpow_eq : ∀ a b : ℕ, lam ^ a = lam ^ b ↔ a ≡ b [MOD g ^ d - 1] := by
    intro a b
    constructor
    · intro h
      have h1 := congrArg (fun f : Kˣ →* ℂˣ => f γ) h
      simp only [MonoidHom.pow_apply] at h1
      rwa [pow_eq_pow_iff_modEq, ← hprim.eq_orderOf] at h1
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, pow_eq_pow_iff_modEq]
      exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hmod, map_one])) h
  have hpow : ∀ θ : Kˣ →* ℂˣ, ∃ k, θ = lam ^ k := by
    intro θ
    have h1 : θ γ ^ (g ^ d - 1) = 1 := by rw [← map_pow, hmod, map_one]
    haveI : NeZero (g ^ d - 1) := ⟨hN0.ne'⟩
    have h1' : ((θ γ : ℂˣ) : ℂ) ^ (g ^ d - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨k, -, hk0⟩ := (IsPrimitiveRoot.coe_units_iff.2 hprim).eq_pow_of_pow_eq_one h1'
    have hk : lam γ ^ k = θ γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk0)
    refine ⟨k, MonoidHom.ext fun u => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hk]
  let kOf : (Kˣ →* ℂˣ) → ℕ := fun θ => (hpow θ).choose
  have hkOf : ∀ θ, θ = lam ^ kOf θ := fun θ => (hpow θ).choose_spec
  have hreg : ∀ θ, IsRegularChar g d θ → ∀ i : ℕ, 0 < i → i < d →
      ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1] := by
    intro θ hθ i hi hid hc
    rw [hcF] at hc
    have e : θ ^ g ^ i = θ ^ g ^ 0 := by
      rw [hkOf θ, ← pow_mul, ← pow_mul, pow_zero, mul_one]
      exact (hpow_eq _ _).2 hc
    exact absurd (hθ i 0 hid hd e) hi.ne'
  have hadd : ∀ k, IsAdditive (rootSum θ₀ k) := fun k => (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ k).1
  have hfr : 0 < Module.finrank (ZMod g) (Fin d → ZMod g) := by rw [Module.finrank_fin_fun]; exact hd
  refine ⟨fun θ x => (-1) ^ (d - 1) *
    psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g))),
    fun θ hθ => ⟨?_, ?_, ?_⟩, fun θ θ' hθ hθ' => ?_⟩
  · exact GlobalTheory.ParamLabel.isCusp_psi θ₀ hθ₀ hd (hreg θ hθ)
  · show (-1) ^ (d - 1) * psi _ _ (Matrix.toLin' ((1 : Gn g d) : Matrix (Fin d) (Fin d) (ZMod g))) = _
    have h1 := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico (ZMod g) (Fin d → ZMod g) (rootSum θ₀ (kOf θ)) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) θ₀ (kOf θ)).2 hfr
    rw [Units.val_one, Matrix.toLin'_one, ← Module.End.one_eq_id, h1, Module.finrank_fin_fun, hcF,
      show ((-1 : ℂ)) ^ (d - 1) = ∏ i ∈ Finset.Ico 1 d, (-1 : ℂ) by rw [Finset.prod_const, Nat.card_Ico],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro y hy z hz
    show (-1) ^ (d - 1) * psi _ _ _ = _
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod g) (Fin d → ZMod g) _ (hadd (kOf θ)) (Matrix.toLin' (y : Mt g d))
      (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [h, Matrix.charpoly_toLin']
    congr 1
    have hz' : aeval (ι (z : K)) (y : Mt g d).charpoly = 0 := by rw [aeval_algHom_apply, hz, map_zero]
    have hnd : (y : Mt g d).charpoly.natDegree = d := by simp
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    rw [GlobalTheory.GreenExists.rootsBar_eq hy hz', hnd, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    conv_rhs => rw [hkOf θ]
    show θ₀ (ι ↑z ^ g ^ i) ^ kOf θ = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam, Units.val_pow_eq_pow_val, map_pow ι]
  · have hsign : ((-1 : ℂ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have hunit : ∀ G : Module.End (ZMod g) (Fin d → ZMod g), IsUnit G →
        ∃ x : Gn g d, Matrix.toLin' (x : Mt g d) = G := by
      intro G hG
      have hM : IsUnit (LinearMap.toMatrix' G) :=
        hG.map (LinearMap.toMatrixAlgEquiv' : Module.End (ZMod g) (Fin d → ZMod g) ≃ₐ[ZMod g] Mt g d)
      exact ⟨hM.unit, by rw [IsUnit.unit_spec, Matrix.toLin'_toMatrix']⟩
    have hxU : ∀ x : Gn g d, IsUnit (Matrix.toLin' (x : Mt g d)) := fun x =>
      x.isUnit.map (Matrix.toLinAlgEquiv' : Mt g d ≃ₐ[ZMod g] Module.End (ZMod g) (Fin d → ZMod g))
    have heqU : ∀ k k' : ℕ, (∀ x : Gn g d, psi (rootSum θ₀ k) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
        psi (rootSum θ₀ k') (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d))) → ∀ l : ℕ,
        ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) =
          ipGL (psi (rootSum θ₀ k') (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
      intro k k' h l
      refine finsum_mem_congr rfl fun G hG => ?_
      obtain ⟨x, rfl⟩ := hunit G hG
      rw [h x]
    have hgram : ∀ k l : ℕ, ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g))
        (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = glCard (ZMod g) d *
          (((Finset.range d).filter fun i => k * g ^ i ≡ l [MOD g ^ d - 1]).card : ℂ) := by
      intro k l
      have h := GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ hfr k l
      rwa [Module.finrank_fin_fun, hcF] at h
    have hGL : glCard (ZMod g) d ≠ 0 := by
      unfold glCard
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    constructor
    · intro hτ
      have hx : ∀ x : Gn g d, psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
          psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) :=
        fun x => mul_left_cancel₀ hsign (congrFun hτ x)
      have e1 := heqU _ _ hx (kOf θ')
      rw [hgram, hgram] at e1
      have h2 := mul_left_cancel₀ hGL e1
      have hmem : 0 ∈ (Finset.range d).filter fun i => kOf θ' * g ^ i ≡ kOf θ' [MOD g ^ d - 1] := by
        rw [Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
        exact ⟨hd, Nat.ModEq.refl _⟩
      have hne : ((Finset.range d).filter fun i => kOf θ * g ^ i ≡ kOf θ' [MOD g ^ d - 1]).Nonempty := by
        rw [← Finset.card_pos]
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h3 := (Finset.card_pos.2 ⟨0, hmem⟩).ne'
        rw [h0, Nat.cast_zero] at h2
        exact h3 (by exact_mod_cast h2.symm)
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i, hi.1, ?_⟩
      rw [hkOf θ', hkOf θ, ← pow_mul]
      exact ((hpow_eq _ _).2 hi.2).symm
    · rintro ⟨i, hi, hθi⟩
      have hk : kOf θ' ≡ kOf θ * g ^ i [MOD g ^ d - 1] := by
        rw [← hpow_eq, pow_mul, ← hkOf θ, ← hkOf θ']
        exact hθi
      funext x
      refine congrArg (fun t : ℂ => (-1 : ℂ) ^ (d - 1) * t) ?_
      have hcl : ∀ k : ℕ, IsClassFn (psi (rootSum θ₀ k) (Fin d → ZMod g)) := fun k e G =>
        GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj (ZMod g) _ _ _ e G
      have hexp := fun k : ℕ => GlobalTheory.T.primitiveClassFunction_expansion_rootSums (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ _ (hcl k)
        (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod g) (Fin d → ZMod g) _ (hadd k)) hfr _ (hxU x)
      have e1 := hexp (kOf θ)
      have e2 := hexp (kOf θ')
      rw [Module.finrank_fin_fun, hcF] at e1 e2
      have hsum : ∀ l : ℕ, ipGL (psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = ipGL (psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
        intro l
        rw [hgram, hgram, filter_modEq_congr hk, card_filter_shift hg hd _ _ _ hi.le]
      rw [Finset.sum_congr rfl fun l _ => by rw [hsum l]] at e1
      exact mul_left_cancel₀ (mul_ne_zero hGL (Nat.cast_ne_zero.2 hd.ne')) (e1.trans e2.symm)

end GlobalTheory.GreenRegular
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalCharacterOfRegularCharacterGLnStatement
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ, (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧ ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 → τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧ (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  first | exact @GlobalTheory.GreenRegular.exists_cusp_of_regular | exact GlobalTheory.GreenRegular.exists_cusp_of_regular | (intros; apply GlobalTheory.GreenRegular.exists_cusp_of_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMulMem
namespace GlobalTheory.SpanMulInertiaEigenvalues

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem span_mul_mem {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (ha : a ∈ Formalism.L2.SG.LocVol.OEv v) (hb : b ∈ Formalism.L2.SG.LocVol.OEv v) :
    a * b ∈ Formalism.L2.SG.LocVol.OEv v := by
  unfold Formalism.L2.SG.LocVol.OEv at *
  rw [SetLike.mem_coe] at *
  set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ
    with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    refine ⟨x * y, Set.mem_univ _, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _
    rw [map_mul, map_mul]
  have key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S,
      x * y ∈ Submodule.span (v.adicCompletionIntegers F) S := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hSmul x hx y hy)
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  induction ha using Submodule.span_induction with
  | mem x hx => exact key x hx b hb
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}, a ∈ Formalism.L2.SG.LocVol.OEv v → b ∈ Formalism.L2.SG.LocVol.OEv v → a * b ∈ Formalism.L2.SG.LocVol.OEv v :=
  fun v _ _ ha hb => span_mul_mem v ha hb

end GlobalTheory.SpanMulInertiaEigenvalues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverse
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.descend_rightInverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  intro l _ K bk τ hτ M
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB M
  obtain ⟨t, ht⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  refine ⟨r, fun d d' n R a h => ?_⟩
  refine ⟨∑ k ∈ t.support, t k • (a.map (TB.c k)), fun i j => ?_⟩
  have hl : ∀ k (y : Ainf l), TB.c k ((l : Ainf l) ^ n * y) = (l : bk.S) ^ n * TB.c k y := by
    intro k y
    have e : (l : Ainf l) ^ n = bk.ev ((l : bk.S) ^ n) := by rw [map_pow, map_natCast]
    rw [e, TB.c_mul]
  obtain ⟨y, hy⟩ := h i j
  rw [Matrix.sub_apply] at hy
  have hy' := sub_eq_iff_eq_add.1 hy
  have hG : (R * ∑ k ∈ t.support, t k • (a.map (TB.c k))) i j = ∑ k ∈ t.support, t k * TB.c k ((R.map bk.ev * a) i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, TB.c_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sub_apply, hG, hy']
  simp only [map_add (f := _), hl, mul_add, Finset.sum_add_distrib]
  refine ⟨∑ k ∈ t.support, t k * TB.c k y, ?_⟩
  rw [← ht]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finsupp.sum, Finset.mul_sum]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero, sub_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_inverse_mod_pow_of_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  first | exact @GlobalTheory.BKLim.descend_rightInverse | exact GlobalTheory.BKLim.descend_rightInverse | (intros; apply GlobalTheory.BKLim.descend_rightInverse; all_goals assumption)
end
end
