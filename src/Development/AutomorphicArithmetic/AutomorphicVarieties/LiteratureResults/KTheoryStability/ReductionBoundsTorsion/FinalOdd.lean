module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SEvOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.SBridgeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.SStabOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FiniteIndexCase.SFinOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.SPrimeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.SHeckeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SStokesOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.SHtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.SPUOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SMomOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ActHomApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.SCenOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.SGapOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SLocOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SInvOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SurjectivityCase.SSurjOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.SWtOddOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddSpanRank.SBStarOddOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SeparationCase.SSepOf
noncomputable section

namespace PositivityTheory.KB

open ChainCochainPairing

theorem sSep : SSep := by
  intro G _ k z _ hnb
  classical
  obtain ⟨φ, hφz, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnb inferInstance
  have hφ : ∀ w, φ (bd G (k + 1) w) = 0 := by
    intro w
    have hw : φ (bd G (k + 1) w) ∈ (LinearMap.range (bd G (k + 1))).map φ :=
      Submodule.mem_map_of_mem (LinearMap.mem_range_self _ w)
    rw [hφp] at hw
    exact (Submodule.mem_bot ℝ).mp hw
  refine ⟨fun y => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1), ?_, ?_, ?_⟩
  · intro g y
    simp [smul_eq_mul, mul_assoc]
  · funext y
    have key : dC (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) y
        = φ (bd G (k + 1) (Finsupp.single (fun i : Fin (k + 2) => (y i.castSucc)⁻¹ * y i.succ) 1)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dC, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum, map_smul]
      rw [Fin.sum_univ_succ]
      congr 1
      · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.succ_castSucc]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Fin.val_succ, smul_eq_mul]
        congr 3
        funext l
        rcases lt_trichotomy (l : ℕ) (j : ℕ) with h | h | h
        · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
        · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
          group
        · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
    rw [key, hφ]
    rfl
  · have hev : ev (MonoidHom.id G) (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) 1 z = φ z := by
      unfold ev
      simp only [MonoidHom.id_apply, smul_eq_mul, mul_one]
      conv_rhs => rw [← Finsupp.sum_single z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      have hg : (fun i : Fin (k + 1) => (Fin.partialProd g i.castSucc)⁻¹ * Fin.partialProd g i.succ) = g := by
        funext i
        simp [Fin.partialProd_succ]
      rw [hg, ← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hev]
    exact hφz

theorem sSep_of : SChain → SSep := fun _ => sSep

end PositivityTheory.KB
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MeanLatticeCounts.CountableLatS
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Pointwise

namespace PositivityTheory.KB.MeanLatticeAction

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem countable_latS : Countable (latS L N) := by
  haveI : Countable (𝓞 L) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
    inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) := by
    unfold Matrix.SpecialLinearGroup; infer_instance
  unfold latS
  exact (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO (L := L) w)).rangeRestrict_surjective.countable

theorem mean_shift (d : Dom L N) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Sp L N → E)
    (hf : ∀ (g : latS L N) (x : Sp L N), f ((g : Sp L N) * x) = f x) (s : Sp L N) :
    ∫ y in d.D, f (y * s) ∂d.μ = ∫ y in d.D, f y ∂d.μ := by
  haveI := d.haar
  haveI := d.right
  haveI : Countable (latS L N) := countable_latS
  have hmp : MeasurePreserving (fun y : Sp L N => y * s) d.μ d.μ := measurePreserving_mul_right d.μ s
  have hemb : MeasurableEmbedding (fun y : Sp L N => y * s) := measurableEmbedding_mulRight s
  have hD' : IsFundamentalDomain (latS L N) ((fun y : Sp L N => y * s) ⁻¹' d.D) d.μ :=
    d.fund.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  refine (d.fund.setIntegral_eq hD' (f := fun y => f (y * s)) ?_).trans
    (hmp.setIntegral_preimage_emb hemb f d.D)
  intro g x
  simp [Subgroup.smul_def, mul_assoc, hf]

private theorem fr_eq_of_actL_eq {q : ℕ} (ω : Form (HS L N) q) {x y : Gp L N}
    (h : actL x = actL y) : fr ω x = fr ω y := by
  unfold fr; rw [h]

private theorem fr_mul_eq_comp_actL_of_fixes_one {q : ℕ} (ω : Form (HS L N) q) (x u : Gp L N)
    (hu : actL u (one L N).1 = (one L N).1) :
    fr ω (x * u) = (fr ω x).compContinuousLinearMap (actL u) := by
  have hc : actL (x * u) = (actL x).comp (actL u) := by
    ext h; simp [actL_mul]
  unfold fr
  rw [hc, ContinuousLinearMap.comp_apply, hu]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']
  rfl

private theorem fr_emb_mul_eq_of_fInv {q : ℕ} (ω : Form (HS L N) q) (hγ : ∀ γ, FInv ω (emb L N γ))
    (γ : Gm L N) (x : Gp L N) : fr ω (emb L N γ * x) = fr ω x := by
  have hc : actL (emb L N γ * x) = (actL (emb L N γ)).comp (actL x) := by
    ext h; simp [actL_mul]
  have hp : actL x (one L N).1 ∈ Pos L N := actL_pos x (one L N).2
  unfold fr
  rw [hc, ContinuousLinearMap.comp_apply, ← hγ γ _ hp]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']
  rfl

private theorem exists_emb_eq_ofS_of_mem_latS (g : Sp L N) (hg : g ∈ latS L N) :
    ∃ γ : Gm L N, ofS L N g = emb L N γ := by
  obtain ⟨A, rfl⟩ := hg
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  apply Units.ext
  ext i j
  rfl

private theorem exists_ofS_actL_eq_of_fixes_one (hN : 1 ≤ N) (u : Gp L N) (hu : actL u (one L N).1 = (one L N).1) :
    ∃ k : Sp L N, actL u = actL (ofS L N k) := by
  have hone : ∀ w, mat ((one L N) : HS L N) w = 1 := by
    intro w; unfold one; simp [mat_mkHS]
  have hN0 : N ≠ 0 := by omega
  have hV : ∀ w, ((u w)⁻¹).valᴴ * ((u w)⁻¹).val = 1 := by
    intro w
    have := congrArg (fun h => mat h w) hu
    simp only [mat_actL, hone, Matrix.mul_one] at this
    exact this
  have hdet : ∀ w, ‖(u w).val.det‖ = 1 := by
    intro w
    have h1 := congrArg Matrix.det (hV w)
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
    have h2 : ‖((u w)⁻¹).val.det‖ = 1 := by
      have h3 : ((‖((u w)⁻¹).val.det‖ : ℂ)) ^ 2 = 1 := by
        rw [← Complex.conj_mul']; simpa using h1
      have h4 : ‖((u w)⁻¹).val.det‖ ^ 2 = 1 := by exact_mod_cast h3
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4
    have h5 := congrArg Matrix.det (Units.mul_inv (u w))
    rw [Matrix.det_mul, Matrix.det_one] at h5
    have h6 := congrArg norm h5
    rw [norm_mul, h2, mul_one, norm_one] at h6
    exact h6
  set c : InfinitePlace L → ℂ := fun w => (u w).val.det ^ ((N : ℂ)⁻¹) with hc
  have hcN : ∀ w, c w ^ N = (u w).val.det := fun w => Complex.cpow_nat_inv_pow _ hN0
  have hcn : ∀ w, ‖c w‖ = 1 := by
    intro w
    have h1 := congrArg norm (hcN w)
    rw [norm_pow, hdet] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp h1
  have hc0 : ∀ w, c w ≠ 0 := fun w h => by simpa [h] using hcn w
  have hU0 : ∀ w, (u w).val.det ≠ 0 := fun w h => by simpa [h] using hdet w
  let k : Sp L N := fun w => ⟨(c w)⁻¹ • (u w).val, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hcN, inv_mul_cancel₀ (hU0 w)]⟩
  refine ⟨k, ?_⟩
  ext h : 1
  apply HS_ext
  intro w
  rw [mat_actL, mat_actL]
  have hk : ((ofS L N k w)⁻¹).val = c w • ((u w)⁻¹).val := by
    rw [Matrix.coe_units_inv]
    apply Matrix.inv_eq_left_inv
    have : (ofS L N k w).val = (c w)⁻¹ • (u w).val := rfl
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc0 w), one_smul]
    exact Units.inv_mul (u w)
  have hs : c w * star (c w) = 1 := by
    rw [mul_comm, show star (c w) = (starRingEnd ℂ) (c w) from rfl, Complex.conj_mul', hcn w]; simp
  rw [hk, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hs, one_smul]

theorem mean_inv (hN : 1 ≤ N) (d : Dom L N) {q : ℕ} (ω : Form (HS L N) q)
    (hγ : ∀ γ, FInv ω (emb L N γ)) (hs : ∀ s, FInv ω (scal L N s))
    (hi : IntegrableOn (fun x => fr ω (ofS L N x)) d.D d.μ) {u : Gp L N}
    (hu : actL u (one L N).1 = (one L N).1) :
    (∫ y in d.D, fr ω (ofS L N y) ∂d.μ).compContinuousLinearMap (actL u) =
      ∫ y in d.D, fr ω (ofS L N y) ∂d.μ := by
  obtain ⟨k, hk⟩ := exists_ofS_actL_eq_of_fixes_one hN u hu
  have hinv : ∀ (g : latS L N) (x : Sp L N),
      fr ω (ofS L N ((g : Sp L N) * x)) = fr ω (ofS L N x) := by
    intro g x
    obtain ⟨γ, hγe⟩ := exists_emb_eq_ofS_of_mem_latS (g : Sp L N) g.2
    rw [map_mul, hγe]
    exact fr_emb_mul_eq_of_fInv ω hγ γ _
  have step : ∀ y : Sp L N, (fr ω (ofS L N y)).compContinuousLinearMap (actL u) =
      fr ω (ofS L N (y * k)) := by
    intro y
    rw [← fr_mul_eq_comp_actL_of_fixes_one ω _ u hu]
    apply fr_eq_of_actL_eq
    ext h : 1
    simp [map_mul, actL_mul, hk]
  have hcomm := (ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u)).integral_comp_comm hi
  have happ : ∀ F : HS L N [⋀^Fin q]→L[ℝ] ℝ,
      ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u) F = F.compContinuousLinearMap (actL u) :=
    fun F => rfl
  rw [happ] at hcomm
  simp only [happ, step] at hcomm
  rw [← hcomm]
  exact mean_shift d (fun y => fr ω (ofS L N y)) hinv k

end PositivityTheory.KB.MeanLatticeAction

namespace PositivityTheory.KB

private theorem exists_actL_one_eq_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hh : h ∈ Pos L N) : ∃ x : Gp L N, actL x (one L N).1 = h := by
  have hone : ∀ w, mat ((one L N) : HS L N) w = 1 := by
    intro w; unfold one; simp [mat_mkHS]
  have hB : ∀ w, ∃ B : Matrix (Fin N) (Fin N) ℂ, mat h w = Bᴴ * B ∧ IsUnit B.det := by
    intro w
    open scoped ComplexOrder MatrixOrder in
    exact (by
      have hp : (mat h w).PosDef := by unfold Pos at hh; exact hh w
      obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.posSemidef.nonneg
      refine ⟨B, hB, ?_⟩
      have h1 := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
      rw [hB, Matrix.det_mul] at h1
      exact isUnit_of_mul_isUnit_right h1)
  choose B hB hdet using hB
  refine ⟨fun w => (Matrix.nonsingInvUnit (B w) (hdet w))⁻¹, ?_⟩
  apply HS_ext
  intro w
  rw [mat_actL, hone, hB w, inv_inv, Matrix.mul_one]
  rfl

theorem sMean_of : SMean := by
  intro L _ _ N q hN d ω _hc hγ hs hi
  have hmul : ∀ (a b : Gp L N) (t : HS L N), actL a (actL b t) = actL (a * b) t :=
    fun a b t => (actL_mul a b t).symm
  set I := ∫ y in d.D, fr ω (ofS L N y) ∂d.μ with hI
  set M : HS L N [⋀^Fin q]→L[ℝ] ℝ := (d.μ.real d.D)⁻¹ • I with hM0
  have hM : ∀ u : Gp L N, actL u (one L N).1 = (one L N).1 →
      M.compContinuousLinearMap (actL u) = M := by
    intro u hu
    have h1 := MeanLatticeAction.mean_inv hN d ω hγ hs hi hu
    ext v
    have h2 := congrArg (fun F : HS L N [⋀^Fin q]→L[ℝ] ℝ => F v) h1
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h2
    simp only [M, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply]
    rw [hI, h2]
  classical
  let ωb : Form (HS L N) q := fun h =>
    if hx : ∃ x : Gp L N, actL x (one L N).1 = h then M.compContinuousLinearMap (actL hx.choose⁻¹)
    else 0
  have hωb : ∀ z : Gp L N, ωb (actL z (one L N).1) = M.compContinuousLinearMap (actL z⁻¹) := by
    intro z
    have hx : ∃ x : Gp L N, actL x (one L N).1 = actL z (one L N).1 := ⟨z, rfl⟩
    simp only [ωb, dif_pos hx]
    have hy : actL hx.choose (one L N).1 = actL z (one L N).1 := hx.choose_spec
    generalize hx.choose = y at hy ⊢
    have hs1 : actL (y⁻¹ * z) (one L N).1 = (one L N).1 := by
      rw [← hmul, ← hy, hmul, inv_mul_cancel, actL_one]
    conv_rhs => rw [← hM _ hs1]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [mul_assoc]
  refine ⟨ωb, ?_, ?_⟩
  · intro g h hh
    obtain ⟨x, rfl⟩ := exists_actL_one_eq_of_mem_Pos h hh
    rw [hmul, hωb, hωb]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [mul_assoc]
  · intro x
    unfold fr
    rw [hωb]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [actL_one]

end PositivityTheory.KB
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveSubmatrices.PrimPush
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveSubmatrices.GlobalTheory
noncomputable section

open Matrix

namespace PositivityTheory.KB.PsiBlockMatrix

variable (R : Type) [CommRing R]

def ee (q n : ℕ) : Fin n × Fin q ≃ Fin (q * n) := (Equiv.prodComm _ _).trans finProdFinEquiv

def blkM (q n : ℕ) : (Fin q → Matrix (Fin n) (Fin n) R) →* Matrix (Fin (q * n)) (Fin (q * n)) R where
  toFun a := Matrix.reindex (ee q n) (ee q n) (Matrix.blockDiagonal a)
  map_one' := by simp
  map_mul' a b := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    rfl

def blk (q n : ℕ) : (Fin q → GL (Fin n) R) →* GL (Fin (q * n)) R :=
  (Units.map (blkM R q n)).comp MulEquiv.piUnits.symm.toMonoidHom

end PositivityTheory.KB.PsiBlockMatrix
end
end

noncomputable section

open Matrix UpperTheory.V.KL
open scoped Kronecker

namespace PositivityTheory.KB

namespace PsiBlockMatrix

theorem psi_eq (R : Type) [CommRing R] (q n : ℕ) :
    psi R q n = (blk R q n).comp (MonoidHom.pi fun _ : Fin q => MonoidHom.id (GL (Fin n) R)) := by
  ext A i j
  have hs : ∀ x : Fin (q * n), (ee q n).symm x = (x.modNat, x.divNat) := fun _ => rfl
  simp [psi, blk, blkM, hs, blockDiagonal_apply, Matrix.one_apply]

variable {G H : Type} [Group G] [Group H]

theorem bd_map (hC : SChain) (f : G →* H) {k : ℕ} {w : Chn G (k + 1)} (hw : IsBd w) :
    IsBd (cmap f (k + 1) w) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
  exact LinearMap.mem_range.2 ⟨cmap f (k + 2) x, hC.2.1 G H f (k + 1) x⟩

theorem cyc_map (hC : SChain) (f : G →* H) {k : ℕ} {w : Chn G (k + 1)} (hw : IsCyc w) :
    IsCyc (cmap f (k + 1) w) := by
  unfold IsCyc at *
  rw [hC.2.1 G H f k w, hw, map_zero]

theorem prim_push (hC : SChain) (φ : G × G →* H) {k : ℕ} {z : Chn G (k + 1)} (hz : IsPrim z) :
    IsBd (cmap (φ.comp ((MonoidHom.id G).prod (MonoidHom.id G))) (k + 1) z -
      cmap (φ.comp (MonoidHom.inl G G)) (k + 1) z - cmap (φ.comp (MonoidHom.inr G G)) (k + 1) z) := by
  have e := fun f : G →* G × G => hC.2.2.1 G (G × G) H f φ (k + 1) z
  rw [e, e, e, ← map_sub, ← map_sub]
  exact bd_map hC φ hz

end PsiBlockMatrix

private theorem exists_conj_blk_mulSingle_eq_stab (R : Type) [CommRing R] (q n : ℕ) (h : n ≤ q * n) (i : Fin q) :
    ∃ P : GL (Fin (q * n)) R, (PsiBlockMatrix.blk R q n).comp (MonoidHom.mulSingle (fun _ : Fin q => GL (Fin n) R) i) =
      (MulAut.conj P).toMonoidHom.comp (stab R n (q * n) h) := by
  classical
  haveI : NeZero q := ⟨by rintro rfl; exact i.elim0⟩
  have hs : ∀ x : Fin (q * n), (PsiBlockMatrix.ee q n).symm x = (x.modNat, x.divNat) := fun _ => rfl
  have hE : ∀ (a : Fin n) (b : Fin q),
      (PsiBlockMatrix.ee q n (a, b)).modNat = a ∧ (PsiBlockMatrix.ee q n (a, b)).divNat = b := by
    intro a b
    have e := (PsiBlockMatrix.ee q n).symm_apply_apply (a, b)
    rw [hs] at e
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have hlt : ∀ x : Fin (q * n), (x : ℕ) < n ↔ x.divNat = 0 := by
    intro x
    rw [Fin.ext_iff, Fin.coe_divNat, Fin.val_zero, Nat.div_eq_zero_iff]
    have : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact x.elim0)
    omega
  let σ : Equiv.Perm (Fin (q * n)) := (PsiBlockMatrix.ee q n).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.swap (0 : Fin q) i)).trans (PsiBlockMatrix.ee q n))
  have hσm : ∀ x, (σ x).modNat = x.modNat := fun x => (hE _ _).1
  have hσd : ∀ x, (σ x).divNat = Equiv.swap (0 : Fin q) i x.divNat := fun x => (hE _ _).2
  have hinj : ∀ x y : Fin (q * n), x = y ↔ x.modNat = y.modNat ∧ x.divNat = y.divNat := by
    intro x y
    rw [← Prod.mk.injEq, ← hs, ← hs, (PsiBlockMatrix.ee q n).symm.apply_eq_iff_eq]
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    rw [hinj, hσm, hσm, hσd, hσd, Equiv.swap_apply_self]
    exact ⟨rfl, rfl⟩
  let Pm : Matrix (Fin (q * n)) (Fin (q * n)) R := σ.toPEquiv.toMatrix
  have hPP : Pm * Pm = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext x y
    simp [Pm, Matrix.one_apply, PEquiv.toMatrix_apply, hσσ]
  refine ⟨⟨Pm, Pm, hPP, hPP⟩, MonoidHom.ext fun A => Units.ext ?_⟩
  have hpad : ∀ X Y : Fin (q * n), padMat R (A : Matrix (Fin n) (Fin n) R) X Y =
      if X.divNat = 0 ∧ Y.divNat = 0 then (A : Matrix (Fin n) (Fin n) R) X.modNat Y.modNat
      else if X = Y then 1 else 0 := by
    intro X Y
    have e1 : ∀ (Z : Fin (q * n)) (hZ : (Z : ℕ) < n), (⟨Z, hZ⟩ : Fin n) = Z.modNat :=
      fun Z hZ => Fin.ext (by simp [Fin.coe_modNat, Nat.mod_eq_of_lt hZ])
    simp only [padMat, Matrix.of_apply, e1]
    by_cases hX : X.divNat = 0
    · by_cases hY : Y.divNat = 0
      · rw [dite_eq_left ⟨(hlt X).2 hX, (hlt Y).2 hY⟩, if_pos ⟨hX, hY⟩]
      · rw [dite_eq_right (fun hh => hY ((hlt Y).1 hh.2)),
          if_neg (fun hh : X.divNat = 0 ∧ Y.divNat = 0 => hY hh.2)]
    · rw [dite_eq_right (fun hh => hX ((hlt X).1 hh.1)),
        if_neg (fun hh : X.divNat = 0 ∧ Y.divNat = 0 => hX hh.1)]
  ext x y
  rw [show (((MulAut.conj (⟨Pm, Pm, hPP, hPP⟩ : GL (Fin (q * n)) R)).toMonoidHom.comp
      (stab R n (q * n) h)) A : Matrix _ _ R) = Pm * (stab R n (q * n) h A : Matrix _ _ R) * Pm from rfl]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  have hy : σ.symm y = σ y := by rw [Equiv.symm_apply_eq, hσσ]
  simp only [Matrix.submatrix_apply, id, hy]
  change _ = padMat R (A : Matrix (Fin n) (Fin n) R) (σ x) (σ y)
  simp only [hpad, hσd, hσm, σ.injective.eq_iff, hinj x y]
  simp [PsiBlockMatrix.blk, PsiBlockMatrix.blkM, hs, blockDiagonal_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff]
  by_cases h1 : x.divNat = i <;> by_cases h2 : y.divNat = i <;>
    by_cases h3 : x.divNat = y.divNat <;> simp [h1, h2, h3, Matrix.one_apply]
  all_goals rw [if_neg (fun e => h2 e.symm), if_neg (fun e => h2 e.2.symm)]

private theorem isBd_cmap_pi_sub_sum_cmap_mulSingle_of_isPrim (hC : SChain) {G : Type} [Group G] {k : ℕ} {z : Chn G (k + 1)}
    (hz : IsPrim z) (q : ℕ) :
    IsBd (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z -
      ∑ j, cmap (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) (k + 1) z) := by
  induction q with
  | zero =>
    have e : (MonoidHom.pi fun _ : Fin 1 => MonoidHom.id G) =
        MonoidHom.mulSingle (fun _ : Fin 1 => G) 0 := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      rw [Fin.fin_one_eq_zero j]
      simp
    rw [Fin.sum_univ_one, e, sub_self]
    exact Submodule.zero_mem _
  | succ q ih =>
    let φ : G × G →* (Fin (q + 2) → G) :=
      MonoidHom.pi fun j => Fin.cases (motive := fun _ => G × G →* G) (MonoidHom.fst G G)
        (fun _ => MonoidHom.snd G G) j
    let ψ : (Fin (q + 1) → G) →* (Fin (q + 2) → G) :=
      MonoidHom.pi fun j => Fin.cases (motive := fun _ => (Fin (q + 1) → G) →* G) 1
        (fun l => Pi.evalMonoidHom (fun _ => G) l) j
    have e1 : φ.comp ((MonoidHom.id G).prod (MonoidHom.id G)) = MonoidHom.pi fun _ => MonoidHom.id G := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ]
    have e2 : φ.comp (MonoidHom.inl G G) = MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) 0 := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ, Pi.mulSingle_apply]
    have e3 : φ.comp (MonoidHom.inr G G) = ψ.comp (MonoidHom.pi fun _ => MonoidHom.id G) := by
      refine MonoidHom.ext fun a => funext fun j => ?_
      cases j using Fin.cases <;> simp [φ, ψ]
    have e4 : ∀ j : Fin (q + 1), ψ.comp (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) =
        MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ := by
      intro j
      refine MonoidHom.ext fun a => funext fun l => ?_
      cases l using Fin.cases <;> simp [ψ, Pi.mulSingle_apply]
    have hp := PsiBlockMatrix.prim_push hC φ hz
    rw [e1, e2, e3, hC.2.2.1] at hp
    have hq := PsiBlockMatrix.bd_map hC ψ ih
    have e5 : ∀ j : Fin (q + 1), cmap ψ (k + 1) (cmap (MonoidHom.mulSingle (fun _ : Fin (q + 1) => G) j) (k + 1) z) =
        cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ) (k + 1) z := fun j => by
      rw [← hC.2.2.1, e4]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum] at hq
    simp only [e5] at hq
    have key : cmap (MonoidHom.pi fun _ : Fin (q + 2) => MonoidHom.id G) (k + 1) z -
        ∑ j, cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j) (k + 1) z =
        (cmap (MonoidHom.pi fun _ : Fin (q + 2) => MonoidHom.id G) (k + 1) z -
          cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) 0) (k + 1) z -
          cmap ψ (k + 1) (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z)) +
        (cmap ψ (k + 1) (cmap (MonoidHom.pi fun _ : Fin (q + 1) => MonoidHom.id G) (k + 1) z) -
          ∑ j : Fin (q + 1), cmap (MonoidHom.mulSingle (fun _ : Fin (q + 2) => G) j.succ) (k + 1) z) := by
      rw [Fin.sum_univ_succ]
      abel
    show _ ∈ LinearMap.range _
    rw [key]
    exact Submodule.add_mem _ hp hq

open PsiBlockMatrix in
theorem sPsi_of (hC : SChain) : SPsi := by
  intro R _ d n k h z hzc hzp
  rw [PsiBlockMatrix.psi_eq R (d + 1) n, hC.2.2.1]
  have h1 := PsiBlockMatrix.bd_map hC (PsiBlockMatrix.blk R (d + 1) n) (isBd_cmap_pi_sub_sum_cmap_mulSingle_of_isPrim hC hzp d)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum] at h1
  simp only [← hC.2.2.1] at h1
  rw [hC.2.2.1 _ _ _ (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R))
    (PsiBlockMatrix.blk R (d + 1) n)] at h1
  have h2 : ∀ j : Fin (d + 1), cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
      (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z -
      cmap (stab R n ((d + 1) * n) h) (k + 1) z ∈ LinearMap.range (bd (GL (Fin ((d + 1) * n)) R) (k + 1)) := by
    intro j
    obtain ⟨P, hP⟩ := exists_conj_blk_mulSingle_eq_stab R (d + 1) n h j
    rw [hP, hC.2.2.1]
    exact hC.2.2.2 _ P k _ (PsiBlockMatrix.cyc_map hC _ hzc)
  have h3 := Submodule.sum_mem _ (fun j (_ : j ∈ Finset.univ) => h2 j)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h3
  have key : cmap (PsiBlockMatrix.blk R (d + 1) n) (k + 1)
      (cmap (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R)) (k + 1) z) -
      ((d : ℝ) + 1) • cmap (stab R n ((d + 1) * n) h) (k + 1) z =
      (cmap (PsiBlockMatrix.blk R (d + 1) n) (k + 1)
        (cmap (MonoidHom.pi fun _ : Fin (d + 1) => MonoidHom.id (GL (Fin n) R)) (k + 1) z) -
        ∑ j, cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
          (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z) +
      (∑ j, cmap ((PsiBlockMatrix.blk R (d + 1) n).comp
          (MonoidHom.mulSingle (fun _ : Fin (d + 1) => GL (Fin n) R) j)) (k + 1) z -
        (d + 1) • cmap (stab R n ((d + 1) * n) h) (k + 1) z) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_succ]
    abel
  show _ ∈ LinearMap.range _
  rw [key]
  exact Submodule.add_mem _ h1 h3

end PositivityTheory.KB
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.SChainOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.RatSuccAboveSucc
noncomputable section

namespace PositivityTheory.KB.SimplicialChains

abbrev HC (X : Type) (n : ℕ) : Type := (Fin n → X) →₀ ℝ

def hbd (X : Type) (n : ℕ) : HC X (n + 1) →ₗ[ℝ] HC X n :=
  Finsupp.linearCombination ℝ fun t : Fin (n + 1) → X =>
    ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℝ)

def cone {X : Type} (a : X) (n : ℕ) : HC X n →ₗ[ℝ] HC X (n + 1) :=
  Finsupp.lmapDomain ℝ ℝ fun t : Fin n → X => (Fin.cons a t : Fin (n + 1) → X)

def chMap {X Y : Type} (f : X → Y) (n : ℕ) : HC X n →ₗ[ℝ] HC Y n :=
  Finsupp.lmapDomain ℝ ℝ fun t : Fin n → X => f ∘ t

theorem eq_of_single {α M : Type} [AddCommGroup M] [Module ℝ M] (φ ψ : (α →₀ ℝ) →ₗ[ℝ] M)
    (h : ∀ t, φ (Finsupp.single t 1) = ψ (Finsupp.single t 1)) (c : α →₀ ℝ) : φ c = ψ c := by
  have : φ = ψ := Finsupp.lhom_ext' fun t => LinearMap.ext_ring (by simpa using h t)
  rw [this]

section Tuples

variable {X Y Z : Type}

theorem hbd_single (n : ℕ) (t : Fin (n + 1) → X) :
    hbd X n (Finsupp.single t 1) =
      ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℝ) := by
  rw [hbd, Finsupp.linearCombination_single, one_smul]

theorem cone_single (a : X) (n : ℕ) (t : Fin n → X) (c : ℝ) :
    cone a n (Finsupp.single t c) = Finsupp.single (Fin.cons a t : Fin (n + 1) → X) c := by
  simp [cone]

theorem chMap_single (f : X → Y) (n : ℕ) (t : Fin n → X) (c : ℝ) :
    chMap f n (Finsupp.single t c) = Finsupp.single (f ∘ t) c := by
  simp [chMap]

theorem hbd_chMap (f : X → Y) (n : ℕ) (c : HC X (n + 1)) :
    hbd Y n (chMap f (n + 1) c) = chMap f n (hbd X n c) := by
  refine eq_of_single (hbd Y n ∘ₗ chMap f (n + 1)) (chMap f n ∘ₗ hbd X n) (fun t => ?_) c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, chMap_single, hbd_single, map_sum, map_smul]
  rfl

theorem chMap_chMap (f : X → Y) (g : Y → Z) (n : ℕ) (c : HC X n) :
    chMap g n (chMap f n c) = chMap (g ∘ f) n c := by
  refine eq_of_single (chMap g n ∘ₗ chMap f n) (chMap (g ∘ f) n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single]
  rfl

theorem chMap_cone (f : X → Y) (a : X) (n : ℕ) (c : HC X n) :
    chMap f (n + 1) (cone a n c) = cone (f a) n (chMap f n c) := by
  refine eq_of_single (chMap f (n + 1) ∘ₗ cone a n) (cone (f a) n ∘ₗ chMap f n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single, cone_single, Fin.comp_cons]

theorem hbd_cone_zero (a : X) (c : HC X 0) : hbd X 0 (cone a 0 c) = c := by
  refine eq_of_single (hbd X 0 ∘ₗ cone a 0) LinearMap.id (fun t => ?_) c
  simp only [LinearMap.comp_apply, cone_single, hbd_single, LinearMap.id_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul]
  congr 1

theorem hbd_cone_succ (a : X) (n : ℕ) (c : HC X (n + 1)) :
    hbd X (n + 1) (cone a (n + 1) c) = c - cone a n (hbd X n c) := by
  refine eq_of_single (hbd X (n + 1) ∘ₗ cone a (n + 1)) (LinearMap.id - cone a n ∘ₗ hbd X n)
    (fun t => ?_) c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, cone_single, hbd_single, LinearMap.id_apply,
    LinearMap.sub_apply, map_sum, map_smul]
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : (Fin.cons a t : Fin (n + 2) → X) ∘ (Fin.succ j).succAbove
        = (Fin.cons a (t ∘ j.succAbove) : Fin (n + 1) → X) := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [this, Fin.val_succ, pow_succ]
    simp

theorem hbd_hbd (n : ℕ) (c : HC X (n + 2)) : hbd X n (hbd X (n + 1) c) = 0 := by
  induction n with
  | zero =>
    refine eq_of_single (hbd X 0 ∘ₗ hbd X 1) 0 (fun t => ?_) c
    rw [← Fin.cons_self_tail t, ← cone_single]
    simp only [LinearMap.comp_apply, hbd_cone_succ, map_sub, hbd_cone_zero, sub_self,
      LinearMap.zero_apply]
  | succ n ih =>
    refine eq_of_single (hbd X (n + 1) ∘ₗ hbd X (n + 2)) 0 (fun t => ?_) c
    rw [← Fin.cons_self_tail t, ← cone_single]
    simp only [LinearMap.comp_apply, hbd_cone_succ, map_sub, ih, map_zero, sub_zero, sub_self,
      LinearMap.zero_apply]

end Tuples

section Group

variable {G : Type} [Group G]

def rho (a : G) (n : ℕ) : HC G n →ₗ[ℝ] HC G n := chMap (· * a) n

def hD (a : G) : ∀ n, HC G n →ₗ[ℝ] HC G (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℝ fun t : Fin (n + 1) → G =>
      cone (t 0) (n + 1) (Finsupp.single t 1 - rho a (n + 1) (Finsupp.single t 1)
        - hD a n (hbd G n (Finsupp.single t 1)))

theorem hD_single (a : G) (n : ℕ) (t : Fin (n + 1) → G) :
    hD a (n + 1) (Finsupp.single t 1) =
      cone (t 0) (n + 1) (Finsupp.single t 1 - rho a (n + 1) (Finsupp.single t 1)
        - hD a n (hbd G n (Finsupp.single t 1))) := by
  rw [hD, Finsupp.linearCombination_single, one_smul]

theorem rho_zero (a : G) (c : HC G 0) : rho a 0 c = c := by
  refine eq_of_single (rho a 0) LinearMap.id (fun t => ?_) c
  simp only [rho, chMap_single, LinearMap.id_apply]
  congr 1
  funext i
  exact i.elim0

theorem hbd_rho (a : G) (n : ℕ) (c : HC G (n + 1)) :
    hbd G n (rho a (n + 1) c) = rho a n (hbd G n c) := hbd_chMap _ n c

theorem hD_step (a : G) (n : ℕ)
    (h : ∀ c : HC G (n + 1), hbd G n (hD a n (hbd G n c)) = hbd G n c - rho a n (hbd G n c))
    (c : HC G (n + 1)) :
    hbd G (n + 1) (hD a (n + 1) c) + hD a n (hbd G n c) = c - rho a (n + 1) c := by
  refine eq_of_single (hbd G (n + 1) ∘ₗ hD a (n + 1) + hD a n ∘ₗ hbd G n)
    (LinearMap.id - rho a (n + 1)) (fun t => ?_) c
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hD_single, hbd_cone_succ, map_sub (hbd G n), map_sub (hbd G n), h, hbd_rho, sub_self, map_zero]
  abel

theorem hD_spec (a : G) (n : ℕ) (c : HC G (n + 1)) :
    hbd G (n + 1) (hD a (n + 1) c) + hD a n (hbd G n c) = c - rho a (n + 1) c := by
  induction n with
  | zero =>
    refine hD_step a 0 (fun c => ?_) c
    rw [rho_zero, sub_self, hD, LinearMap.zero_apply, map_zero]
  | succ n ih =>
    refine hD_step a (n + 1) (fun c => ?_) c
    have := ih (hbd G (n + 1) c)
    rwa [hbd_hbd, map_zero, add_zero] at this

theorem chMap_rho (g a : G) (n : ℕ) (c : HC G n) :
    chMap (g * ·) n (rho a n c) = rho a n (chMap (g * ·) n c) := by
  have : ((fun x : G => g * x) ∘ fun x => x * a) = ((fun x => x * a) ∘ fun x => g * x) := by
    funext x
    simp [mul_assoc]
  simp only [rho, chMap_chMap, this]

theorem hD_left (g a : G) (n : ℕ) (c : HC G n) :
    hD a n (chMap (g * ·) n c) = chMap (g * ·) (n + 1) (hD a n c) := by
  induction n with
  | zero => simp [hD]
  | succ n ih =>
    refine eq_of_single (hD a (n + 1) ∘ₗ chMap (g * ·) (n + 1))
      (chMap (g * ·) (n + 2) ∘ₗ hD a (n + 1)) (fun t => ?_) c
    simp only [LinearMap.comp_apply]
    rw [chMap_single, hD_single, hD_single, chMap_cone]
    simp only [map_sub]
    rw [← ih, ← hbd_chMap, chMap_rho, chMap_single]
    rfl

def rat {n : ℕ} (x : Fin (n + 1) → G) : Fin n → G := fun i => (x i.castSucc)⁻¹ * x i.succ

def ph (n : ℕ) : HC G (n + 1) →ₗ[ℝ] HC G n := Finsupp.lmapDomain ℝ ℝ rat

def ps (n : ℕ) : HC G n →ₗ[ℝ] HC G (n + 1) := Finsupp.lmapDomain ℝ ℝ Fin.partialProd

def ibd (G : Type) [Group G] (m : ℕ) : HC G (m + 1) →ₗ[ℝ] HC G m :=
  Finsupp.linearCombination ℝ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

def icmap {H : Type} [Group H] (f : G →* H) (m : ℕ) : HC G m →ₗ[ℝ] HC H m :=
  Finsupp.lmapDomain ℝ ℝ fun g i => f (g i)

theorem ph_single (n : ℕ) (x : Fin (n + 1) → G) (r : ℝ) :
    ph n (Finsupp.single x r) = Finsupp.single (rat x) r := by
  simp [ph]

theorem ps_single (n : ℕ) (x : Fin n → G) (r : ℝ) :
    ps n (Finsupp.single x r) = Finsupp.single (Fin.partialProd x) r := by
  simp [ps]

theorem icmap_single {H : Type} [Group H] (f : G →* H) (m : ℕ) (x : Fin m → G) (r : ℝ) :
    icmap f m (Finsupp.single x r) = Finsupp.single (fun i => f (x i)) r := by
  simp [icmap]

theorem ibd_single (m : ℕ) (g : Fin (m + 1) → G) :
    ibd G m (Finsupp.single g 1) = Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1 := by
  rw [ibd, Finsupp.linearCombination_single, one_smul]

theorem rat_partialProd {n : ℕ} (g : Fin n → G) : rat (Fin.partialProd g) = g := by
  funext i
  simp [rat, Fin.partialProd_succ]

theorem partialProd_rat {n : ℕ} (x : Fin (n + 1) → G) :
    Fin.partialProd (rat x) = fun k => (x 0)⁻¹ * x k := by
  funext k
  induction k using Fin.induction with
  | zero => simp
  | succ k ih => rw [Fin.partialProd_succ, ih, rat, mul_assoc, mul_inv_cancel_left]

theorem ph_ps (n : ℕ) (z : HC G n) : ph n (ps n z) = z := by
  refine eq_of_single (ph n ∘ₗ ps n) LinearMap.id (fun t => ?_) z
  simp only [LinearMap.comp_apply, ps_single, ph_single, rat_partialProd, LinearMap.id_apply]

theorem ph_chMap_left (g : G) (n : ℕ) (c : HC G (n + 1)) :
    ph n (chMap (g * ·) (n + 1) c) = ph n c := by
  refine eq_of_single (ph n ∘ₗ chMap (g * ·) (n + 1)) (ph n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single, ph_single]
  congr 1
  funext i
  simp [rat, mul_assoc]

theorem ph_rho (a : G) (n : ℕ) (c : HC G (n + 1)) :
    ph n (rho a (n + 1) c) = icmap (MulAut.conj a⁻¹).toMonoidHom n (ph n c) := by
  refine eq_of_single (ph n ∘ₗ rho a (n + 1)) (icmap (MulAut.conj a⁻¹).toMonoidHom n ∘ₗ ph n)
    (fun t => ?_) c
  simp only [LinearMap.comp_apply, rho, chMap_single, ph_single, icmap_single]
  congr 1
  funext i
  simp [rat, mul_assoc]

theorem ps_ph_single (n : ℕ) (x : Fin (n + 1) → G) :
    ps n (ph n (Finsupp.single x 1)) = chMap ((x 0)⁻¹ * ·) (n + 1) (Finsupp.single x 1) := by
  rw [ph_single, ps_single, partialProd_rat, chMap_single]
  rfl

theorem rat_succAbove_zero {m : ℕ} (x : Fin (m + 2) → G) :
    rat (x ∘ (0 : Fin (m + 2)).succAbove) = fun i => rat x i.succ := by
  funext i
  simp only [rat, Function.comp_apply, Fin.succAbove_zero, Fin.succ_castSucc]

theorem rat_succAbove_succ {m : ℕ} (x : Fin (m + 2) → G) (j : Fin (m + 1)) :
    rat (x ∘ j.succ.succAbove) = Fin.contractNth j (· * ·) (rat x) := by
  funext i
  simp only [Function.comp_apply, rat, Fin.contractNth]
  by_cases h1 : (i : ℕ) < j
  · rw [if_pos h1, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega),
      Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega)]
    simp only [Fin.succ_castSucc]
  · by_cases h2 : (i : ℕ) = j
    · rw [if_neg h1, if_pos h2, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega),
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega)]
      simp only [Fin.succ_castSucc, mul_assoc, mul_inv_cancel_left]
    · rw [if_neg h1, if_neg h2, Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega),
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega)]
      simp only [Fin.succ_castSucc]

theorem ibd_ph (m : ℕ) (c : HC G (m + 2)) : ibd G m (ph (m + 1) c) = ph m (hbd G (m + 1) c) := by
  refine eq_of_single (ibd G m ∘ₗ ph (m + 1)) (ph m ∘ₗ hbd G (m + 1)) (fun x => ?_) c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, ph_single, ibd_single, hbd_single, map_sum, map_smul]
  conv_rhs => rw [Fin.sum_univ_succ]
  congr 1
  · rw [rat_succAbove_zero]
    simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [rat_succAbove_succ, Fin.val_succ]

def hI (a : G) (m : ℕ) : HC G m →ₗ[ℝ] HC G (m + 1) := ph (m + 1) ∘ₗ hD a (m + 1) ∘ₗ ps m

theorem ph_hD (a : G) (m : ℕ) (c : HC G (m + 1)) : ph (m + 1) (hD a (m + 1) c) = hI a m (ph m c) := by
  refine eq_of_single (ph (m + 1) ∘ₗ hD a (m + 1)) (hI a m ∘ₗ ph m) (fun x => ?_) c
  simp only [LinearMap.comp_apply, hI]
  rw [ps_ph_single, hD_left, ph_chMap_left]

theorem homotopy (a : G) (m : ℕ) (z : HC G (m + 1)) :
    ibd G (m + 1) (hI a (m + 1) z) + hI a m (ibd G m z) =
      z - icmap (MulAut.conj a⁻¹).toMonoidHom (m + 1) z := by
  have hz : z = ph (m + 1) (ps (m + 1) z) := (ph_ps _ z).symm
  rw [hz, ← ph_hD, ibd_ph, ibd_ph, ← ph_hD, ← map_add (f := _), hD_spec, map_sub, ph_rho]

theorem ibd_ibd (m : ℕ) (z : HC G (m + 2)) : ibd G m (ibd G (m + 1) z) = 0 := by
  rw [← ph_ps _ z, ibd_ph, ibd_ph, hbd_hbd, map_zero]

theorem ibd_icmap {H : Type} [Group H] (f : G →* H) (m : ℕ) (z : HC G (m + 1)) :
    ibd H m (icmap f (m + 1) z) = icmap f m (ibd G m z) := by
  refine eq_of_single (ibd H m ∘ₗ icmap f (m + 1)) (icmap f m ∘ₗ ibd G m) (fun x => ?_) z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, icmap_single, ibd_single, map_add (f := _), map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp [map_mul]

theorem icmap_comp {H K : Type} [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ) (z : HC G m) :
    icmap (g.comp f) m z = icmap g m (icmap f m z) := by
  refine eq_of_single (icmap (g.comp f) m) (icmap g m ∘ₗ icmap f m) (fun x => ?_) z
  simp only [LinearMap.comp_apply, icmap_single, MonoidHom.comp_apply]

theorem conj_bd (g : G) (m : ℕ) (z : HC G (m + 1)) (hz : ibd G m z = 0) :
    icmap (MulAut.conj g).toMonoidHom (m + 1) z - z ∈ LinearMap.range (ibd G (m + 1)) := by
  refine ⟨-hI g⁻¹ (m + 1) z, ?_⟩
  have h := homotopy g⁻¹ m z
  rw [hz, map_zero, add_zero, inv_inv] at h
  rw [map_neg, h, neg_sub]

end Group

end PositivityTheory.KB.SimplicialChains
end
end

noncomputable section

namespace PositivityTheory.KB

theorem sChain_of : SChain := by
  have hbd : ∀ (G : Type) [Group G] (m : ℕ), bd G m = SimplicialChains.ibd G m := fun _ _ _ => rfl
  have hcm : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ), cmap f m = SimplicialChains.icmap f m :=
    fun _ _ _ _ _ _ => rfl
  refine ⟨fun G _ m z => ?_, fun G H _ _ f m z => ?_, fun G H K _ _ _ f g m z => ?_,
    fun G _ g m z hz => ?_⟩
  · rw [hbd, hbd]
    exact SimplicialChains.ibd_ibd m z
  · rw [hbd, hbd, hcm, hcm]
    exact SimplicialChains.ibd_icmap f m z
  · rw [hcm, hcm, hcm]
    exact SimplicialChains.icmap_comp f g m z
  · unfold IsBd
    unfold IsCyc at hz
    rw [hbd] at hz ⊢
    rw [hcm]
    exact SimplicialChains.conj_bd g m z hz

end PositivityTheory.KB
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SInv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridge
namespace PositivityTheory.KB

theorem sChain : SChain := sChain_of
theorem sEv : SEv := sEv_of
theorem sSep' : SSep := sSep_of sChain
theorem sBridge : SBridge := sBridge_of
theorem sStab : SStab := sStab_of sChain sBridge
theorem sFin : SFin := sFin_of sBridge
theorem sPsi : SPsi := sPsi_of sChain
theorem sAff : SAff := sAff_of sChain sEv sSep' sBridge
theorem sHecke : SHecke := sHecke_of sChain sEv sSep' sStab sFin sAff
theorem sPU : SPU := sPU_of sHt_of
theorem sMom : SMom := TwSMInt2.sMom_of sHt_of
theorem sWhit : SWhit := sWhit_of sEv sStokes_of
theorem sCen : SCen := sCen_of sEv
theorem sLoc : SLoc := sLoc_of sEv

end PositivityTheory.KB
end

namespace PositivityTheory.KB

theorem sInv : SInv := sInv_of sChain sEv sPsi sStokes_of

end PositivityTheory.KB
end

namespace PositivityTheory.KB

theorem bStarOdd : BStarOdd :=
  sBStarOdd_of sChain sSep' sBridge sStab
    (sSurj_of sPrime_of sHecke sHt_of sPU sMom sWhit sCen sGap_of sLoc sMean_of sInv)
    (sWtOdd_of sChain sEv sPsi sStokes_of)

end PositivityTheory.KB
