module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

namespace GlobalTheory.BKGal.HatVal

theorem value_mul_E_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hy b₂ hval c hc Y hY
  obtain ⟨m, c', hu, hmc, hmb⟩ := hval
  set E0 : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hE0
  have hEW : ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) = inclO l O E0 := by
    rw [hE0, ← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  have hYi : ∀ i, inclO l O (ϖ.iTot t K (Y i)) = inclO l O E0 ^ η * toW t ϖ D.toPhiMod ⟨y, hy⟩ i := by
    intro i
    rw [← ϖ.iW_of_mem t K, toW_apply, ← hEW, ← map_pow, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp [hY, EIn]
  set S : ι → OA l O := fun i => ∑ j, ϖ.iTot t K (Y j) * c j i with hSdef
  have hS : inclL t ϖ D.toPhiMod S = inclO l O (E0 ^ (H + η)) • toW t ϖ D.toPhiMod ⟨y, hy⟩ := by
    have h1 : S = ∑ j, fun i => ϖ.iTot t K (Y j) * c j i := by
      funext i; simp [hSdef, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    simp only [inclL_smul_coord, hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hYi i, pow_add]
    simp only [map_mul, map_pow]
    ring
  have hkey : (fun i => m * S i) = fun i => E0 ^ (H + η) * c' i := by
    apply inclL_injective t ϖ D.toPhiMod
    rw [inclL_smul_coord, inclL_smul_coord, hS, ← hmc, smul_smul, smul_smul, mul_comm]
  have h2 := congrArg (fun v : ι → OA l O => R.jB fun i => toB l O (v i)) hkey
  have hL : (fun i => toB l O (m * S i)) = toB l O m • ∑ j, toB l O (ϖ.iTot t K (Y j)) • fun i => toB l O (c j i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hSdef, Finset.sum_apply, Finset.mul_sum, map_sum]
  have hR : (fun i => toB l O (E0 ^ (H + η) * c' i)) = toB l O E0 ^ (H + η) • fun i => toB l O (c' i) := by
    funext i
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, hR, map_smul, map_smul, ← hmb, map_sum] at h2
  simp only [map_smul] at h2
  rw [smul_smul, mul_comm, ← smul_smul] at h2
  exact (hu.smul_left_cancel).1 h2.symm

end GlobalTheory.BKGal.HatVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSumStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  first | exact @GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | exact GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | (intros; apply GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R σ c hc
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  refine ⟨fun j τ => ⟨E K l e ^ η * σ.1 τ j, mem_tot.1 hσM τ j⟩, fun j τ => rfl, ?_⟩
  set ej : ι → Vec K a ι := fun j _ => Pi.single j 1 with hej
  have hejM : ∀ j, ej j ∈ D.M := fun j => mem_tot.2 fun τ => mem_vecs.2 fun i => by
    simp only [hej]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : ∀ j, E K l e ^ H • ej j ∈ D.L := fun j => D.lower _ (hejM j)
  have hcol : ∀ j τ i, (D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ) i = E K l e ^ H * D.mxInv τ i j := by
    intro j τ i
    simp only [hej, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply]
  have hℓ : ∀ j i τ, E K l e ^ H * D.mxInv τ i j ∈ A O K := fun j i τ => by
    rw [← hcol]; exact D.mem_extc_iff.1 (mem_tot.1 (hL j) τ) i
  set ℓ : ι → ι → ZMod a → A O K := fun j i τ => ⟨_, hℓ j i τ⟩ with hℓdef
  have hcj : ∀ j, c j = fun i => ϖ.iTot t K (ℓ j i) := by
    intro j
    apply inclL_injective t ϖ D.toPhiMod
    rw [hc j]
    have hv : E K l e ^ H • ej j ∈ ME D.toPhiMod := mem_ME_of_mem_L (hL j)
    have h1 := toW_of_mx t ϖ D.toPhiMod ⟨_, hv⟩ (ℓ j) (fun τ => by
      have h2 : (fun i => ((ℓ j i τ : A O K) : K⟦X⟧)) = D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ :=
        funext fun i => (hcol j τ i).symm
      change (E K l e ^ H • ej j) τ = D.mx τ *ᵥ fun i => ((ℓ j i τ : A O K) : K⟦X⟧)
      rw [h2, Matrix.mulVec_mulVec, D.mx_mul_mxInv, Matrix.one_mulVec])
    rw [← inclL_apply] at h1
    rw [← h1]
    ext1 i
    rw [toW_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej i) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) =
          fun τ => ⟨(((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ : K⟦X⟧),
            le_away _ _ (((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ).2⟩ :=
        funext fun τ => Subtype.ext (by simp [hej, EIn])
      rw [h3, ϖ.iW_of_mem t K]
      simp only [map_pow, ϖ.iTot_E t K, Pi.single_eq_same, mul_one]
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej j) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) = 0 :=
        funext fun τ => Subtype.ext (by simp [hej, Pi.single_eq_of_ne h])
      rw [h3, map_zero, Pi.single_eq_of_ne h, mul_zero]
  have hB : ∀ f : ZMod a → A O K, toB l O (ϖ.iTot t K f) =
      ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (A_le_S l e (f τ).2)⟩) := fun f => by
    rw [toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
  have hE : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) =
      toB l O (ϖ.iTot t K (fun _ => EIn l e _)) := by rw [ϖ.iTot_E t K]
  rw [← LinearEquiv.map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← LinearEquiv.map_smul, ← map_sum]
  congr 1
  ext i
  simp only [Pi.smul_apply, Finset.sum_apply, hcj, hB, toBcris_apply, hE, smul_eq_mul,
    ← map_pow, ← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
    AddSubmonoidClass.coe_finsetSum, hℓdef]
  change (E K l e) ^ (H + η) * (D.mxInv τ *ᵥ σ.1 τ) i = ∑ j, E K l e ^ η * σ.1 τ j * (E K l e ^ H * D.mxInv τ i j)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  first | exact @GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum | exact GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum | (intros; apply GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

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
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_hat_value_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_hat_mem_filZero | exact GlobalTheory.BKGal.value_hat_mem_filZero | (intros; apply GlobalTheory.BKGal.value_hat_mem_filZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizPole

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem X_pow_eq : (X : K⟦X⟧) ^ e = E K l e - l := by rw [E]; ring

theorem E_ne_zero : E K l e ≠ 0 := (isUnit_E (K := K) l e).ne_zero

theorem pow_mul_EN (j : ℕ) (f : K⟦X⟧) :
    E K l e ^ j * (E K l e * N K f) =
      E K l e * N K (E K l e ^ j * f) - (j : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * (E K l e ^ j * f) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  cases j with
  | zero => simp
  | succ j => simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem N_pow_mul (j : ℕ) (G : K⟦X⟧) :
    N K (E K l e ^ (j + 1) * G) =
      E K l e ^ (j + 1) * N K G + ((j + 1 : ℕ) : K⟦X⟧) * E K l e ^ j * ((e : K⟦X⟧) * X ^ e) * G := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem EN_xiExt (D : BKDat O K l e a ι η H) (w : Vec K a ι) :
    D.EN (D.xiExt w) = D.xiExt (fun τ i => E K l e * N K (w τ i)) := by
  rw [PhiMod.EN_apply, PhiMod.conn_xiExt]
  exact (D.xiExt_smul_tot (fun _ => E K l e) _).symm

theorem N_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : N K f ∈ Rpi O K l e :=
  N_mem (derivative_mem_R l hf)

theorem C_mem_Rpi (c : K) : C c ∈ Rpi O K l e := HasK.C_mem c

theorem cast_ne (j : ℕ) : (((j + 1) * e * l : ℕ) : K) ≠ 0 :=
  natCast_ne_zero' l (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero j) (NeZero.ne e))
    (Fact.out : l.Prime).ne_zero)

theorem C_inv_mul (j : ℕ) : C ((((j + 1) * e * l : ℕ) : K))⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = 1 := by
  have h : (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = C ((((j + 1) * e * l : ℕ) : K)) := by
    rw [map_natCast]; push_cast; ring
  rw [h, ← map_mul, inv_mul_cancel₀ (cast_ne j), map_one]

theorem neg_step (D : BKDat O K l e a ι η H) (p : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, E K l e ^ (p + 1) * D.xiExt.symm v τ i ∈ Rpi O K l e) (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧
      ∀ τ i, E K l e ^ p * D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  set c : K := (((p + 1) * e * l : ℕ) : K) with hc
  refine ⟨v - c⁻¹ • D.EN v, ?_, ?_, fun τ i => ?_⟩
  · rw [sub_sub_cancel]; exact D.Man.smul_mem _ hN
  · rw [map_sub, map_smul]; exact sub_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · obtain ⟨w, rfl⟩ := D.xiExt.surjective v
    have hco : D.xiExt.symm (D.xiExt w - c⁻¹ • D.EN (D.xiExt w)) τ i =
        w τ i - C c⁻¹ * (E K l e * N K (w τ i)) := by
      rw [EN_xiExt, ← map_smul, ← map_sub, LinearEquiv.symm_apply_apply]
      simp [smul_eq_C_mul]
    rw [hco]
    have hF := hv τ i
    rw [LinearEquiv.symm_apply_apply] at hF
    have h2 := pow_mul_EN (l := l) (e := e) (p + 1) (w τ i)
    have h1 := C_inv_mul (K := K) (l := l) (e := e) p
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    have key : E K l e * (E K l e ^ p * (w τ i - C c⁻¹ * (E K l e * N K (w τ i)))) =
        E K l e * (C c⁻¹ * (((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i) -
          N K (E K l e ^ (p + 1) * w τ i))) := by
      rw [← mul_assoc, ← pow_succ']
      linear_combination (-C c⁻¹) * h2 + (C c⁻¹ * ((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i)) * hX + (-(E K l e ^ (p + 1) * w τ i)) * h1
    rw [mul_left_cancel₀ E_ne_zero key]
    exact mul_mem (C_mem_Rpi _) (sub_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hF)
      (N_mem_Rpi hF))

theorem neg_all (D : BKDat O K l e a ι η H) (p : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, E K l e ^ p * D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ ∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  induction p with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, fun τ i => by simpa using hv τ i⟩
  | succ p ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3⟩ := neg_step D p v hv hN
    obtain ⟨v₂, h4, h5, h6⟩ := ih v₁ h3 h2
    refine ⟨v₂, ?_, h5, h6⟩
    have := add_mem h1 h4
    rwa [sub_add_sub_cancel] at this

theorem pos_step (D : BKDat O K l e a ι η H) (j : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e)
    (hG : ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v τ i) = E K l e ^ j * G)
    (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ (j + 1) * G := by
  set c : K := (((j + 1) * e * l : ℕ) : K) with hc
  obtain ⟨w, rfl⟩ := D.xiExt.surjective v
  simp only [LinearEquiv.symm_apply_apply] at hv hG
  have hco : ∀ τ i, D.xiExt.symm (D.xiExt w + c⁻¹ • D.EN (D.xiExt w)) τ i =
      w τ i + c⁻¹ • (E K l e * N K (w τ i)) := fun τ i => by
    rw [EN_xiExt, ← map_smul, ← map_add (f := _), LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨D.xiExt w + c⁻¹ • D.EN (D.xiExt w), ?_, ?_, fun τ i => ?_, fun τ i => ?_⟩
  · rw [sub_add_cancel_left]; exact neg_mem (D.Man.smul_mem _ hN)
  · rw [map_add (f := _), map_smul]; exact add_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · rw [hco, smul_eq_C_mul]
    exact add_mem (hv τ i) (mul_mem (C_mem_Rpi _) (mul_mem (E_mem l e _) (N_mem_Rpi (hv τ i))))
  · obtain ⟨G, hGm, hGe⟩ := hG τ i
    rw [hco]
    refine ⟨C c⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * G + N K G), mul_mem (C_mem_Rpi _)
      (add_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hGm) (N_mem_Rpi hGm)), ?_⟩
    have h3 := N_pow_mul (l := l) (e := e) j G
    have h1 := C_inv_mul (K := K) (l := l) (e := e) j
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    rw [map_add (f := _), Derivation.map_smul, hGe, ← mul_assoc, ← pow_succ', h3, smul_eq_C_mul]
    linear_combination (C c⁻¹ * ((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * E K l e ^ j * G) * hX +
      (-(E K l e ^ j * G)) * h1

theorem pos_all (D : BKDat O K l e a ι η H) (j : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ j * G := by
  induction j with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, hv, fun τ i => ⟨_, N_mem_Rpi (hv τ i), by simp⟩⟩
  | succ j ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3, h4⟩ := ih v hv hN
    obtain ⟨v₂, h5, h6, h7, h8⟩ := pos_step D j v₁ h3 h4 h2
    refine ⟨v₂, ?_, h6, h7, h8⟩
    have := add_mem h1 h5
    rwa [sub_add_sub_cancel] at this

theorem one_div_lt : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact one_div_lt_one_div_of_lt he (by nlinarith)

theorem init (D : BKDat O K l e a ι η H) (n : ℕ) (v : Vec K a ι) (hv : v ∈ divE l e n D.Man) :
    ∀ τ i, E K l e ^ (n + H) * D.xiExt.symm v τ i ∈ Rpi O K l e := by
  have h1 : E K l e ^ (n + H) • v ∈ D.ext (Rpi O K l e) := by
    rw [add_comm, pow_add, mul_smul]
    exact D.smul_mem_ext_of_basis (fun i => D.lower _ (D.bas_mem_M i)) (A_le_Rpi l e) (D.mem_Man.1 hv)
  have h2 := (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt
    (E K l e ^ (n + H) • D.xiExt.symm v)).1 (by
      have := D.xiExt_smul_tot (fun _ => E K l e ^ (n + H)) (D.xiExt.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ h1)
  exact fun τ i => mem_tot.1 h2 τ i

theorem fin (D : BKDat O K l e a ι η H) (r : Vec K a ι) (hr : ∀ τ i, r τ i ∈ Rpi O K l e) :
    E K l e ^ η • D.xiExt r ∈ D.Man :=
  D.mem_Man.2 (D.smul_mem_Mext (A_le_Rpi l e)
    ((GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt r).2 (mem_tot.2 fun τ i => hr τ i)))

theorem taylor (f : K⟦X⟧) (hf : f ∈ Rpi O K l e) (B : ℕ) :
    ∃ g ∈ invL l (A O K), ∃ r ∈ Rpi O K l e, f - g = E K l e ^ B * r := by
  obtain ⟨g, hg⟩ : ∃ g : invL l (A O K),
      Ideal.Quotient.mk _ g = AdicCompletion.evalₐ (idE O K l e) B (toHat O K l e ⟨f, hf⟩) :=
    Ideal.Quotient.mk_surjective _
  obtain ⟨r, hr, h⟩ := (evalₐ_toHat_eq_iff l e B ⟨f, hf⟩ g).1 hg.symm
  exact ⟨g, g.2, r, hr, h⟩

theorem eulerDerivation_eisensteinPow_final_bound {f g r G : K⟦X⟧} (m B : ℕ) (hB : m + 1 ≤ B) (hg : g ∈ invL l (A O K))
    (hr : r ∈ Rpi O K l e) (hG : G ∈ Rpi O K l e) (hf : N K f = E K l e ^ m * G)
    (hfg : f - g = E K l e ^ B * r) :
    ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K g = E K l e ^ m * h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  have hX := X_pow_eq (K := K) (l := l) (e := e)
  set h' := G - (E K l e ^ (d + 1) * N K r +
    ((m + d + 1 : ℕ) : K⟦X⟧) * E K l e ^ d * ((e : K⟦X⟧) * X ^ e) * r) with hh'
  have hgf : g = f - E K l e ^ (m + d + 1) * r := by rw [show m + d + 1 = m + 1 + d by omega, ← hfg]; ring
  have hN : N K g = E K l e ^ m * h' := by
    rw [hgf, map_sub, hf, N_pow_mul, hh']
    ring
  have hh'R : h' ∈ Rpi O K l e := sub_mem hG (add_mem (mul_mem (pow_mem (E_mem l e _) _) (N_mem_Rpi hr))
    (mul_mem (mul_mem (mul_mem (natCast_mem _ _) (pow_mem (E_mem l e _) _))
      (mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _))) hr))
  obtain ⟨k, hk⟩ : N K g ∈ invL l (A O K) := N_mem (derivative_mem_away _ (fun _ => derivative_mem_A) hg)
  have hk' : (l : K⟦X⟧) ^ k * N K g ∈ A O K := by simpa using hk
  refine ⟨(l : K⟦X⟧) ^ k * h', mem_A_of_E_pow_mul_mem l e m
    (mul_mem (pow_mem (natCast_mem _ _) _) hh'R) ?_, k, ?_⟩
  · rw [hN] at hk'; convert hk' using 1; ring
  · rw [hN]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D n v hv hN m
  obtain ⟨v₁, h1, h2, h3⟩ := neg_all D (n + H) v (init D n v hv) hN
  obtain ⟨v₂, h4, -, h6, h7⟩ := pos_all D m v₁ h3 h2
  choose G hGm hGe using h7
  choose g hg r hr hfg using fun (τ : ZMod a) (i : ι) => taylor (D.xiExt.symm v₂ τ i) (h6 τ i) (m + 1 + η)
  refine ⟨g, mem_tot.2 fun τ i => hg τ i, ?_, fun τ i =>
    eulerDerivation_eisensteinPow_final_bound m (m + 1 + η) (by omega) (hg τ i) (hr τ i) (hGm τ i) (hGe τ i) (hfg τ i)⟩
  have e0 : D.xiExt.symm v₂ - g = (fun _ : ZMod a => E K l e ^ (m + 1 + η)) • r :=
    funext fun τ => funext fun i => by simpa using hfg τ i
  have e1 : v₂ - D.xiExt g = E K l e ^ (m + 1) • (E K l e ^ η • D.xiExt r) := by
    rw [smul_smul, ← pow_add]
    have := D.xiExt_smul_tot (fun _ : ZMod a => E K l e ^ (m + 1 + η)) r
    rw [← e0, map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : v - D.xiExt g = (v - v₁) + (v₁ - v₂) + (v₂ - D.xiExt g) := by abel
  rw [e2, e1]
  exact add_mem (add_mem h1 h4) (D.smul_mem_Man (pow_mem (E_mem l e _) _) (fin D r hr))

end GlobalTheory.HorizPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPoleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  exact @GlobalTheory.HorizPole.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

theorem GlobalTheory.BKGal.sub_sub_xi_mem_Man : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ σ : D.MMl, D.conn σ.1 = D.zeta y → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), σ.1 - y - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ ι _ _ η H D y hyY hMon σ hσ m
  have hyM : E K l e ^ η • y ∈ D.M := mem_divE.1 hyY.1
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  have hv : σ.1 - y ∈ divE l e η D.Man := by
    rw [mem_divE, smul_sub]
    exact sub_mem (D.Mext_mono (invL_S_le_Rpi l e) hσM) (D.M_le_Man hyM)
  have hEN : D.EN (σ.1 - y) ∈ D.Man := by
    have h0 : D.EN y - E K l e • D.zeta y ∈ D.Man := by
      rw [← D.cls_eq_zero_iff, ← D.Mon_apply]; exact hMon
    have h1 : D.EN (σ.1 - y) = -(D.EN y - E K l e • D.zeta y) := by
      rw [map_sub, D.EN_apply σ.1, hσ]; abel
    rw [h1]; exact neg_mem h0
  exact GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole O K l e a ι η H D η _ hv hEN m

theorem GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon hy σ hσinv hconn b₂ hb₂ g hg C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  obtain ⟨m₀, hxi⟩ := GlobalTheory.T.xi_value_galois_sub_mem_filZero l a e O K t ϖ hl2 ι η H D T R
  obtain ⟨w, hw, hr, hN⟩ := GlobalTheory.BKGal.sub_sub_xi_mem_Man l a e O K ι η H D y hyY hMon σ hconn m₀
  have hwM : D.xiExt w ∈ D.MMl :=
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 w).2 (D.Mext_mono (away_mono (A_le_S l e) rfl) hw)
  set ξw : D.MMl := ⟨D.xiExt w, hwM⟩ with hξw
  have hr' : (σ - ξw).1 - y ∈ D.Man := by
    have : (σ - ξw).1 - y = σ.1 - y - D.xiExt w := by
      rw [Submodule.coe_sub, hξw]; abel
    rw [this]; exact hr
  have h3 := GlobalTheory.T.breuilKisin_hat_value_mem_filZero l a e O K t ϖ hl2 ι η H D T R (σ - ξw) y hy hr' b₂ hb₂ C
  have h4 := GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable l O K T g C _ h3
  have h2 := hxi w hw hN hwM g hg C
  have key : R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ = R.jB (toBcris t ϖ D.toPhiMod ξw) +
      (R.jB (toBcris t ϖ D.toPhiMod (σ - ξw)) - b₂) := by
    rw [map_sub, map_sub]; abel
  rw [key, map_add (f := _)]
  convert add_mem h2 (sub_mem h4 h3) using 1
  abel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | exact GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | (intros; apply GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionSubMemFiltrationZeroOfMonodromy
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.gb_sub_b_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon b hb g hg
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  refine ⟨C, ?_⟩
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, rfl⟩ := hb
  obtain ⟨b₁, hb₁, hF⟩ := GlobalTheory.T.value_mem_filtration_zero_tame l a e O K t ϖ hl2 ι η H D T R y hyY hy m₀ h1
  have hv : IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) (b₀ - b₁) := by
    rw [← h1]; exact GlobalTheory.BKGal.IsCrisVal.sub t ϖ h4 hb₁
  have h5 := GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero l a e O K t ϖ hl2 ι η H D T R y hyY hMon hy σ h2 h3 (b₀ - b₁) hv g hg C
  have h6 := hF g hg C
  have h7 := Submodule.sub_mem _ h5 h6
  convert h7 using 1
  simp only [map_sub]
  abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionSubMemFiltrationZeroOfMonodromyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gb_sub_b_mem_filZero | exact GlobalTheory.BKGal.gb_sub_b_mem_filZero | (intros; apply GlobalTheory.BKGal.gb_sub_b_mem_filZero <;> assumption)
end
