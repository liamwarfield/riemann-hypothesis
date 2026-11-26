module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKExp

theorem muPow_smul_crisVal_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hEM : y ∈ D.toPhiMod.EM η := hyY.1
  obtain ⟨-, hLA⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm
  obtain ⟨c, hc⟩ := hLA
  have hU := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  obtain ⟨z, hz⟩ := ((GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩
  have hC := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := rfl
  have hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n := by
    intro n
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
    intro n
    rw [hpow, e1]
    exact (hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef
  obtain ⟨u, hu⟩ := hunit (H + η)
  have hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀)
      ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i))) := by
    refine ⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩
    rw [← hu, smul_smul, Units.mul_inv, one_smul]
  have hb0 := hC _ _ _ hb hval
  have hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i)) := by
    rw [hb0, ← hu, smul_smul, Units.mul_inv, one_smul]
  set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'
  have hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c' := by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hc', map_mul]
  rw [hL] at hz
  have hcmp := R.cmp c' z hz
  refine ⟨z, ?_⟩
  rw [← hcmp]
  have e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m := by
    rw [hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]
    ring_nf
  have e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m := by
    first
    | rw [e2, map_mul]
    | rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]; ring_nf
  rw [e3, mul_smul, hmain, ← map_smul]
  congr 1
  funext i
  simp [hc', map_mul]

end GlobalTheory.BKExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  first | exact @GlobalTheory.BKExp.muPow_smul_crisVal_integral | exact GlobalTheory.BKExp.muPow_smul_crisVal_integral | (intros; apply GlobalTheory.BKExp.muPow_smul_crisVal_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensor
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  first | exact @GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | exact GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  first | exact @GlobalTheory.BKGal.muPow_smul_actB_sub_mem | exact GlobalTheory.BKGal.muPow_smul_actB_sub_mem | (intros; apply GlobalTheory.BKGal.muPow_smul_actB_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBound
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Count

section Coord

variable {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def cfO {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) : O ⊗[ℤ_[l]] R →ₗ[ℤ_[l]] R :=
  (TensorProduct.lid ℤ_[l] R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem cfO_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) (r : R) :
    cfO f (o ⊗ₜ[ℤ_[l]] r) = f o • r := by
  simp [cfO]

theorem cfO_mul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (β : R)
    (y : O ⊗[ℤ_[l]] R) : cfO f (((1 : O) ⊗ₜ[ℤ_[l]] β) * y) = β * cfO f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul o r => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cfO_tmul, cfO_tmul, mul_smul_comm]

theorem cfO_map {R R' : Type} [CommRing R] [Algebra ℤ_[l] R] [CommRing R'] [Algebra ℤ_[l] R']
    (f : O →ₗ[ℤ_[l]] ℤ_[l]) (φ : R →ₐ[ℤ_[l]] R') (y : O ⊗[ℤ_[l]] R) :
    cfO f (Algebra.TensorProduct.map (AlgHom.id O O) φ y) = φ (cfO f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o r => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, cfO_tmul, cfO_tmul, map_smul]

theorem cfO_natCast_smul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (m : ℕ)
    (y : O ⊗[ℤ_[l]] R) : cfO f ((m : O) • y) = (m : R) * cfO f y := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]

theorem cfO_smul_one {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) :
    cfO f (o • (1 : O ⊗[ℤ_[l]] R)) = algebraMap ℤ_[l] R (f o) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, cfO_tmul,
    Algebra.smul_def, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [Algebra O LL] [TopologicalSpace LL]

def cfT {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) :
    TW R T →ₗ[O] R :=
  (TensorProduct.rid O R).toLinearMap ∘ₗ TensorProduct.map LinearMap.id g

theorem cfT_tmul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (s : R) (t : ↥T.L.T) : cfT T g (s ⊗ₜ[O] t) = g t • s := by
  simp [cfT]

theorem cfT_incl {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) (φ : R →ₐ[O] R') (z : TW R T) :
    cfT T g (TWincl φ T z) = φ (cfT T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s t => rw [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      cfT_tmul, cfT_tmul, map_smul]

theorem cfT_smul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (r : R) (z : TW R T) : cfT T g (r • z) = r * cfT T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul s t => rw [TensorProduct.smul_tmul', cfT_tmul, cfT_tmul, smul_eq_mul, mul_smul_comm]

end Coord

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem toB_algebraMap (q : ℤ_[l]) :
    acrisToBcris l (ainfToAcris l (algebraMap ℤ_[l] (Ainf l) q)) = algebraMap ℤ_[l] (Per.Bcris l) q := by
  rw [AlgHom.commutes, AlgHom.commutes]

theorem le_of_bound {n c v j : ℕ} (hj : 2 * j < l - 1) (h : (l - 1) * n ≤ (l - 1) * (c + v) + 2 * j) :
    n ≤ c + v := by
  have h1 : (l - 1) * n < (l - 1) * (c + v + 1) := by
    rw [mul_add, mul_one]; omega
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h1)

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

theorem count : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ),
    2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T),
    (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x →
    toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w →
    ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T hl2 ε hε j n c hj u x w h1 h2
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bT := latBasis T
  have hr0 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hr : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) =
      (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l (ainfToAcris l (muOf ε)) ^ j) := by
    rw [map_pow, hr0, Algebra.TensorProduct.tmul_pow, one_pow]
  have hlO : ∀ m : ℕ, (l : O) ^ m = ((l ^ m : ℕ) : O) := fun m => by push_cast; rfl
  have key : ∀ k i, (l : ℤ_[l]) ^ (n - c) ∣ bO.coord k (bT.coord i x) := by
    intro k i
    by_cases ha : bO.coord k (bT.coord i x) = 0
    · rw [ha]; exact dvd_zero _
    have e1 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h1
    have e2 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h2
    rw [hlO, map_smul, cfO_natCast_smul, cfT_tmul, cfO_smul_one] at e1
    rw [hr, cfT_smul, cfO_mul, hlO, map_smul, cfO_natCast_smul, cfT_incl, toOB, cfO_map] at e2
    set U := cfO (bO.coord k) (cfT T (bT.coord i) u)
    set a := bO.coord k (bT.coord i x)
    set W' := cfO (bO.coord k) (cfT T (bT.coord i) w)
    have e3 : acrisToBcris l ((l : Per.Acris l) ^ n * W') = acrisToBcris l
        (ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ c * a))) := by
      rw [map_mul, map_mul, ← e2, map_pow, map_natCast, map_mul, toB_algebraMap, map_mul, ← e1]
      push_cast
      simp only [map_pow]
      ring
    have e4 := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l e3
    have hne : (l : ℤ_[l]) ^ c * a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) ha
    have hb := GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris l hl2 ε hε j n ((l : ℤ_[l]) ^ c * a) hne ⟨W', e4.symm⟩
    rw [PadicInt.valuation_p_pow_mul c a ha] at hb
    have hv : n - c ≤ a.valuation := by have := le_of_bound hj hb; omega
    exact Ideal.mem_span_singleton.1 ((PadicInt.mem_span_pow_iff_le_valuation a ha (n - c)).2 hv)
  choose q hq using key
  let x' : ↥T.L.T := bT.equivFun.symm fun i => bO.equivFun.symm fun k => q k i
  have hx' : (l : O) ^ (n - c) • x' = x := by
    apply bT.equivFun.injective
    funext i
    rw [map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply, smul_eq_mul]
    apply bO.equivFun.injective
    funext k
    rw [show (l : O) ^ (n - c) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ (n - c)) by rw [map_pow, map_natCast],
      ← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, ← hq k i]
    rfl
  refine ⟨(l : O) ^ (c + (n - c) - n) • x', smul_cancel T (n - c) ?_⟩
  have e5 : (l : O) ^ (n - c) • ((l : O) ^ c • u) = (l : O) ^ (c + (n - c) - n) • ((l : O) ^ n • u) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e5, h1, ← hx', TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_smul,
    smul_smul, mul_comm]

end GlobalTheory.BKGal.Count
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBoundStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ), 2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T), (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w → ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  first | exact @GlobalTheory.BKGal.Count.count | exact GlobalTheory.BKGal.Count.count | (intros; apply GlobalTheory.BKGal.Count.count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImage
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalTaylor

section Lemmas

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l)
    (T : LocLat G ℚ_[l] K O) (g : G) (β : OB l O) (v : TW (OB l O) T) :
    actB s T g (β • v) = galOB O (s g) β • actB s T g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [actB, TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

theorem taylor_iC (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (f : ZMod a → S O K e)
    (r : ℕ) : ∃ M₀, ∀ M ≥ M₀, (l : OCr l O) ^ r ∣ galOCr O g (ϖ.iC t K f) -
      ∑ i ∈ Finset.range M, ϖ.muDiv a O g i *
        ϖ.iC t K (fun τ => ⟨descN K i (f τ), descN_mem_S e i (f τ).2⟩) := by
  choose N hN using fun τ => ϖ.taylor_S a O K g (f τ) r
  refine ⟨Finset.univ.sup N, fun M hM => ?_⟩
  choose z hz using fun τ => hN τ M ((Finset.le_sup (Finset.mem_univ τ)).trans hM)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem toBcris_of_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (P : PhiMod O K l e a ι) {m : Vec K a ι}
    (h : m ∈ P.MM) (h' : m ∈ P.MMl) (k : ι) :
    toBcris t ϖ P ⟨m, h'⟩ k = toOB l O (toCris t ϖ P ⟨m, h⟩ k) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem descConn_xiExt (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) :
    Polynomial.aeval P.conn (descPochhammer K i) (P.xiExt w) =
      P.xiExt (fun τ j => descN K i (w τ j)) := by
  induction i generalizing w with
  | zero => simp [descN]
  | succ i ih =>
    rw [descPochhammer_succ_right, map_mul, mul_apply_eq_comp, map_sub, Polynomial.aeval_X, map_natCast,
      LinearMap.sub_apply, Module.End.natCast_apply, PhiMod.conn_xiExt, ← map_nsmul, ← map_sub, ih]
    congr 1
    funext τ j
    simp only [descN, descPochhammer_succ_right, map_mul, mul_apply_eq_comp, map_sub, Polynomial.aeval_X,
      map_natCast, LinearMap.sub_apply, Module.End.natCast_apply, Pi.sub_apply, Pi.smul_apply]
    rfl

theorem aeval_descPochhammer_mem {V R : Type} [AddCommGroup V] [Module K V] [CommRing R] [Module R V]
    (W : Submodule R V) (φ : Module.End K V) (hφ : ∀ m ∈ W, φ m ∈ W) (n : ℕ) :
    ∀ m ∈ W, Polynomial.aeval φ (descPochhammer K n) m ∈ W := by
  induction n with
  | zero => intro m hm; simpa using hm
  | succ n ih =>
    intro m hm
    rw [descPochhammer_succ_right, map_mul, mul_apply_eq_comp, map_sub, Polynomial.aeval_X, map_natCast,
      LinearMap.sub_apply, Module.End.natCast_apply]
    exact ih _ (sub_mem (hφ m hm) (nsmul_mem hm n))

theorem descConn_mem (P : PhiMod O K l e a ι) (hP : ∀ m ∈ P.MM, P.conn m ∈ P.MM) {v : Vec K a ι} {c : ℕ}
    (hv : (l : K) ^ c • P.conn v ∈ P.MM) (i : ℕ) :
    (l : K) ^ c • Polynomial.aeval P.conn (descPochhammer K (i + 1)) v ∈ P.MM := by
  rw [descPochhammer_succ_left, mul_comm, map_mul, mul_apply_eq_comp, Polynomial.aeval_X, ← LinearMap.map_smul,
    Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, map_one]
  exact aeval_descPochhammer_mem P.MM (P.conn - 1) (fun m hm => sub_mem (hP m hm) hm) i _ hv

theorem pow_smul_mem_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : K) ^ n • f ∈ S O K e := by
  obtain ⟨m, hm⟩ := mem_away.1 hf
  refine ⟨m, fun n hn => ?_⟩
  have e1 : (l : K) ^ n • f = (l : K⟦X⟧) ^ (n - m) * ((l : K⟦X⟧) ^ m * f) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn, smul_eq_C_mul, map_pow, map_natCast]
  rw [e1]
  exact mul_mem (pow_mem (natCast_mem _ l) _) (by simpa using hm)

theorem pow_smul_mem_S_fin {κ : Type} [Fintype κ] {f : κ → K⟦X⟧} (hf : ∀ p, f p ∈ invL l (S O K e)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p, (l : K) ^ n • f p ∈ S O K e := by
  choose N hN using fun p => pow_smul_mem_S (hf p)
  exact ⟨Finset.univ.sup N, fun n hn p => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)⟩

theorem exists_pow_smul_mem_MM (P : PhiMod O K l e a ι) {x : Vec K a ι} (hx : x ∈ P.MMl) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : K) ^ n • x ∈ P.MM := by
  obtain ⟨n₀, h⟩ := pow_smul_mem_S_fin (κ := ZMod a × ι) (f := fun p => (P.mxInv p.1 *ᵥ x p.1) p.2)
    (fun p => mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hx p.1)) p.2)
  refine ⟨n₀, fun n hn => mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun j => ?_)⟩
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply]
  exact h n hn (τ, j)

theorem exists_pow_smul_mem_Mext (P : PhiMod O K l e a ι) {w : Vec K a ι}
    (hw : w ∈ P.Mext (invL l (S O K e))) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ τ j, (l : K) ^ n • w τ j ∈ S O K e := by
  obtain ⟨n₀, h⟩ := pow_smul_mem_S_fin (κ := ZMod a × ι) (f := fun p => w p.1 p.2)
    (fun p => mem_vecs.1 (mem_tot.1 hw p.1) p.2)
  exact ⟨n₀, fun n hn τ j => h n hn (τ, j)⟩

theorem toBcris_xiExt (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (P : PhiMod O K l e a ι) {W : Vec K a ι}
    (hW : ∀ τ j, W τ j ∈ S O K e) (h : P.xiExt W ∈ P.MMl)
    (hx : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl) (k : ι) :
    toBcris t ϖ P ⟨P.xiExt W, h⟩ k =
      ∑ j, toOB l O (ϖ.iC t K fun τ => ⟨W τ j, hW τ j⟩) * toBcris t ϖ P ⟨_, hx j⟩ k := by
  have hsum : (⟨P.xiExt W, h⟩ : P.MMl) = ∑ j, (⟨(fun τ => W τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => le_away _ _ (hW τ j)) (hx j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt W = _
    rw [Submodule.coe_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [eq_sum_bas W, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => W τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toBcris_apply, toBcris_apply, ← ϖ.iB_of_mem t K, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end Lemmas

theorem lpow_galDiff_eq_jB_toOB : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ℕ), (l : K) ^ c • D.conn σ.1 ∈ D.MM → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ z : ι → OCr l O, (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB fun i => toOB l O (z i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R σ c hc g hg
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  let g' : ↥(GK (ϖ.field a)) := ⟨sQ l g, hg⟩
  have hxi := (GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2
  have nsm : ∀ (n : ℕ) (v : Vec K a ι), (l : K) ^ n • v = (l ^ n) • v := fun n v => by
    rw [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow]

  have hxj : ∀ j : ι, D.toPhiMod.xi (fun _ => Pi.single j 1) ∈ D.toPhiMod.MMl := fun j => by
    rw [PhiMod.xi_apply, cst_single, hxi]
    exact mem_tot.2 fun τ => mem_vecs.2 fun i => by
      simp only [bas, Pi.single_apply]
      split_ifs <;> simp
  let X : ι → ι → OB l O := fun j => toBcris t ϖ D.toPhiMod ⟨_, hxj j⟩
  have hv : ∀ j, actB (sQ l) T g (R.jB (X j)) = R.jB (X j) := fun j => R.horiz g hg _ (hxj j)

  obtain ⟨w, hw⟩ := D.toPhiMod.xiExt.surjective σ.1
  have hwM : w ∈ D.toPhiMod.Mext (invL l (S O K e)) := (hxi w).1 (hw ▸ σ.2)
  obtain ⟨n₁, hn₁⟩ := exists_pow_smul_mem_Mext D.toPhiMod hwM
  choose m₀ hm₀ using fun j => exists_pow_smul_mem_MM D.toPhiMod (hxj j)
  set n₂ := Finset.univ.sup m₀ with hn₂
  have hX2 : ∀ j, (l : K) ^ n₂ • D.toPhiMod.xi (fun _ => Pi.single j 1) ∈ D.toPhiMod.MM := fun j =>
    hm₀ j n₂ (Finset.le_sup (Finset.mem_univ j))
  set W : Vec K a ι := (l : K) ^ n₁ • w with hWdef
  have hWS : ∀ τ j, W τ j ∈ S O K e := hn₁ n₁ le_rfl
  have hWσ : D.toPhiMod.xiExt W = (l : K) ^ n₁ • σ.1 := by rw [hWdef, map_smul, hw]
  have hWM : D.toPhiMod.xiExt W ∈ D.toPhiMod.MMl := by rw [hWσ, nsm]; exact nsmul_mem σ.2 _

  let Wi : ℕ → Vec K a ι := fun i τ j => descN K (i + 1) (W τ j)
  have hWi : ∀ i τ j, Wi i τ j ∈ S O K e := fun i τ j => descN_mem_S e (i + 1) (hWS τ j)
  have hWiM : ∀ i, D.toPhiMod.xiExt (Wi i) ∈ D.toPhiMod.MMl := fun i =>
    (hxi _).2 (mem_tot.2 fun τ => mem_vecs.2 fun j => le_away _ _ (hWi i τ j))
  let Pi' : ℕ → Vec K a ι := fun i => Polynomial.aeval D.toPhiMod.conn (descPochhammer K (i + 1)) σ.1
  have hPi : ∀ i, (l : K) ^ c • Pi' i ∈ D.toPhiMod.MM := fun i =>
    descConn_mem D.toPhiMod (fun m hm => D.conn_mem_MM hm) hc i
  have hxiWi : ∀ i, D.toPhiMod.xiExt (Wi i) = (l : K) ^ n₁ • Pi' i := fun i => by
    rw [← descConn_xiExt, hWσ, map_smul]
  let y : ℕ → ι → OCr l O := fun i => toCris t ϖ D.toPhiMod ⟨_, hPi i⟩
  let u : ι → ι → OCr l O := fun j => toCris t ϖ D.toPhiMod ⟨_, hX2 j⟩
  let Y : ℕ → ι → OB l O := fun i => toBcris t ϖ D.toPhiMod ⟨_, hWiM i⟩
  have hF : ∀ i k, (l : OB l O) ^ c * Y i k = (l : OB l O) ^ n₁ * toOB l O (y i k) := fun i k => by
    have hsub : (l ^ c) • (⟨D.toPhiMod.xiExt (Wi i), hWiM i⟩ : D.toPhiMod.MMl) =
        (l ^ n₁) • (⟨(l : K) ^ c • Pi' i, D.toPhiMod.ext_mono (le_away _ _) (hPi i)⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul, hxiWi]
      rw [← nsm, ← nsm, smul_smul, smul_smul, mul_comm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [this, toBcris_of_mem t ϖ D.toPhiMod (hPi i)]
  have hG : ∀ j k, (l : OB l O) ^ n₂ * X j k = toOB l O (u j k) := fun j k => by
    have hsub : (l ^ n₂) • (⟨_, hxj j⟩ : D.toPhiMod.MMl) =
        (⟨(l : K) ^ n₂ • D.toPhiMod.xi (fun _ => Pi.single j 1), D.toPhiMod.ext_mono (le_away _ _) (hX2 j)⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul]
      rw [← nsm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [this, toBcris_of_mem t ϖ D.toPhiMod (hX2 j)]

  let β : ι → OCr l O := fun j => ϖ.iC t K fun τ => ⟨W τ j, hWS τ j⟩
  have hA : ∀ k, toBcris t ϖ D.toPhiMod σ k * (l : OB l O) ^ n₁ = ∑ j, toOB l O (β j) * X j k := fun k => by
    have hsub : (l ^ n₁) • σ = (⟨D.toPhiMod.xiExt W, hWM⟩ : D.toPhiMod.MMl) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul, hWσ]
      rw [← nsm]
    have := congrArg (fun x => toBcris t ϖ D.toPhiMod x k) hsub
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow] at this
    rw [mul_comm, this, toBcris_xiExt t ϖ D.toPhiMod hWS hWM hxj k]
  have hb : (l ^ n₁) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, toOB l O (β j) • R.jB (X j) := by
    rw [← map_nsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← LinearEquiv.map_smul, ← map_sum]
    congr 1
    ext k
    simpa only [Pi.smul_apply, Finset.sum_apply, nsmul_eq_mul, Nat.cast_pow,
      smul_eq_mul, mul_comm] using hA k
  have hgb : (l ^ n₁) • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) =
      ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • R.jB (X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [nsmul_sub, ← map_nsmul, hb, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [actB_smul, hv, galOB_toOB, map_sub, sub_smul]

  choose M₀ hM₀ using fun j => taylor_iC t ϖ g' (fun τ => ⟨W τ j, hWS τ j⟩) (n₁ + n₂)
  set M := Finset.univ.sup M₀ with hM
  have hε : ∀ j, ∃ ε : OCr l O, galOCr O (sQ l g) (β j) - β j = ∑ i ∈ Finset.range M,
      ϖ.muDiv a O g' (i + 1) * ϖ.iC t K (fun τ => ⟨Wi i τ j, hWi i τ j⟩) + (l : OCr l O) ^ (n₁ + n₂) * ε := by
    intro j
    obtain ⟨ε, hε⟩ := hM₀ j (M + 1) ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))
    refine ⟨ε, ?_⟩
    rw [Finset.sum_range_succ'] at hε
    have h0 : ϖ.muDiv a O g' 0 * ϖ.iC t K (fun τ => ⟨descN K 0 (W τ j), descN_mem_S e 0 (hWS τ j)⟩) = β j := by
      have h1 : ϖ.muDiv a O g' 0 = 1 := by
        simp [PiSys.muDiv, dpow_zero, Algebra.TensorProduct.one_def]
      rw [h1, one_mul]
      congr 1
      funext τ
      exact Subtype.ext (by simp [descN])
    rw [h0] at hε
    linear_combination hε
  choose ε hε using hε
  let z : ι → OCr l O := fun k => ∑ i ∈ Finset.range M, ϖ.muDiv a O g' (i + 1) * y i k +
    (l : OCr l O) ^ c * ∑ j, ε j * u j k
  refine ⟨z, ?_⟩
  have cancel : ∀ (N : ℕ) (A B : TW (OB l O) T), (l ^ N) • A = (l ^ N) • B → A = B := by
    intro N A B h
    rw [← Nat.cast_smul_eq_nsmul (OB l O), ← Nat.cast_smul_eq_nsmul (OB l O), Nat.cast_pow] at h
    exact ((isUnit_l_OB (l := l) (O := O)).pow N).smul_left_cancel.1 h
  have key : ∀ k, (l : OB l O) ^ n₂ * (l : OB l O) ^ c *
      ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) * X j k =
      (l : OB l O) ^ (n₁ + n₂) * toOB l O (z k) := fun k => by
    have hstar : ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) * X j k =
        ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * Y i k +
          (l : OB l O) ^ (n₁ + n₂) * ∑ j, toOB l O (ε j) * X j k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hε, map_add (f := _), map_sum, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show Y i k = _ from toBcris_xiExt t ϖ D.toPhiMod (hWi i) (hWiM i) hxj k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    have hF' : (∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * Y i k) * (l : OB l O) ^ c =
        (l : OB l O) ^ n₁ * ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * toOB l O (y i k) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination toOB l O (ϖ.muDiv a O g' (i + 1)) * hF i k
    have hG' : (∑ j, toOB l O (ε j) * X j k) * (l : OB l O) ^ n₂ =
        ∑ j, toOB l O (ε j) * toOB l O (u j k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination toOB l O (ε j) * hG j k
    have hz : toOB l O (z k) = ∑ i ∈ Finset.range M, toOB l O (ϖ.muDiv a O g' (i + 1)) * toOB l O (y i k) +
        (l : OB l O) ^ c * ∑ j, toOB l O (ε j) * toOB l O (u j k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [z, map_add (f := _), map_sum, map_mul, map_pow, map_natCast]
    rw [hstar, hz]
    linear_combination (l : OB l O) ^ n₂ * hF' + (l : OB l O) ^ (n₁ + n₂) * (l : OB l O) ^ c * hG'
  apply cancel (n₁ + n₂)
  have e1 : (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) =
      (l ^ c) • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) := by
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  rw [e1, smul_smul, show l ^ (n₁ + n₂) * l ^ c = (l ^ n₂ * l ^ c) * l ^ n₁ by ring, ← smul_smul, hgb]
  have eL : (l ^ n₂ * l ^ c) • ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • R.jB (X j) =
      R.jB ((l ^ n₂ * l ^ c) • ∑ j, toOB l O (galOCr O (sQ l g) (β j) - β j) • X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum]
    simp only [LinearEquiv.map_smul]
  have eR : (l ^ (n₁ + n₂)) • R.jB (fun i => toOB l O (z i)) =
      R.jB ((l ^ (n₁ + n₂)) • fun i => toOB l O (z i)) := (map_nsmul _ _ _).symm
  rw [eL, eR]
  congr 1
  ext k
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow] using key k

end GlobalTheory.GalTaylor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImageStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ℕ), (l : K) ^ c • D.conn σ.1 ∈ D.MM → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ z : ι → OCr l O, (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB fun i => toOB l O (z i) := by
  first | exact @GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | exact GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | (intros; apply GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CocycleInt

theorem TWincl_comp_toB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] {T : LocLat (Gl l) ℚ_[l] K O} (z : TW (OA l O) T) :
    TWincl (toOB l O) T (TWincl (toOCr l O) T z) = TWincl (toB l O) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r x => rfl

theorem TWincl_smul' {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

end GlobalTheory.BKGal.CocycleInt


open GlobalTheory.BKGal.CocycleInt in
theorem GlobalTheory.BKGal.potential_cocycle_mem_lpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R hηH hl y hyY c hc b hb g hg hex
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hval, rfl⟩ := hb
  have hl2 : l ≠ 2 := by omega
  obtain ⟨z, hz⟩ := GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image l a e O K t ϖ hl2 ι η H D T R σ c (by rw [hconn]; exact hc) g hg
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower R.jB R.cmp ε hε z
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice l a e O K t ϖ ι η H D T R y hyY hy m₀ b₀ hm₀ hval ε hε
  obtain ⟨z₁, hz₁⟩ := GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl l O K T g ε hε (H + 2 * η) b₀ z₀ hz₀
  obtain ⟨n, x, hx⟩ := hex
  set jσ := R.jB (toBcris t ϖ D.toPhiMod σ)
  refine GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound l O K T hl2 ε hε (H + 2 * η) n c (by omega) _ x
    (toOCr l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) • w₁ - (l : O) ^ c • TWincl (toOCr l O) T z₁) hx ?_
  have hsplit : actB (sQ l) T g (jσ - b₀) - (jσ - b₀) = (actB (sQ l) T g jσ - jσ) - (actB (sQ l) T g b₀ - b₀) := by
    rw [map_sub]; abel
  have hmu : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η) : OA l O) =
      ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ η) := by
    rw [show H + 2 * η = (H + η) + η by ring, pow_add]
  rw [hsplit, map_sub, TWincl_smul', map_smul, TWincl_comp_toB, ← hz₁, smul_sub, hz, ← hw₁]
  rw [smul_sub, hmu, map_mul, mul_smul, hw₁, smul_comm ((l : O) ^ c) (toB l O _ * toB l O _ : OB l O)]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialCocycle_mem_lPow_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.BKGal.potential_cocycle_mem_lpow | exact GlobalTheory.BKGal.potential_cocycle_mem_lpow | (intros; apply GlobalTheory.BKGal.potential_cocycle_mem_lpow <;> assumption)
end
