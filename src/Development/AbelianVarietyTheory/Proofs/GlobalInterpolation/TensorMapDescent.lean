module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.Proof.TensorMapDescent

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section BaseChange

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem fockB_map {σ : Type} (f g : MvPolynomial σ K) : fockB (map φ f) (map φ g) = φ (fockB f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockB_eq_sum _ _ f.support (support_map_subset _ _), fockB, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem map_ten {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    map φ (ten f) = ten fun τ => map φ (f τ) := by
  unfold ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => fk_map_blockEmb φ τ _

theorem ten_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) : ten f ∈ VV K lam :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem ten_ne_zero {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) (hf : ∀ τ, f τ ≠ 0) :
    ten f ≠ 0 := by
  unfold ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b h => (Prod.mk.inj h).2)
  exact (map_ne_zero_iff _ hinj).mpr (hf τ)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    map φ F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := map_ten φ f
    unfold ten at h
    rw [h]
    exact ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K K' φ n n _ _ (hf τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem ssB_desc {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν, ssB K' ν m = map φ f := by
  obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.2 m).2.2
  refine ⟨Formalism.GradedWeylDivisibility.bideterminant K sz hsz I, ?_, by rw [fk_map_bidet]; exact h⟩
  rw [← hsh]
  exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I

theorem bVVfun_desc {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F ∈ VV K lam, bVVfun K' lam i = map φ F := by
  choose f hf hf' using fun τ => ssB_desc φ (lam τ).natW (i τ)
  refine ⟨ten f, ten_mem lam f hf, ?_⟩
  rw [map_ten]
  exact congrArg ten (funext hf')

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem eq_zero_of_fockB [CharZero K] (sg : ι → DomWeight n) (x : VV K sg)
    (h : ∀ i, fockB (bVVfun K sg i) (x : Pol K ι n) = 0) : x = 0 := by
  refine (pairingBNondegenerate_holds K ι n sg).2 x fun y => ?_
  have : (pairBK sg).flip x = 0 := by
    refine (bVV K sg).ext fun i => ?_
    rw [LinearMap.flip_apply, pairBK_apply, pairB_apply, bVV_coe, h i, mul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun this y

open Classical in
theorem gramB_det_ne_zero [CharZero K] (sg : ι → DomWeight n) : (Br.gramB (K := K) sg).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∑ j, v j • bVV K sg j = 0 := by
    refine eq_zero_of_fockB sg _ fun i => ?_
    have := congrFun hv0 i
    simp only [Matrix.mulVec, dotProduct, Br.gramB, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← fockBL_apply, Submodule.coe_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, map_smul, bVV_coe, fockBL_apply, smul_eq_mul, mul_comm]
  exact hv (funext (Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent v h1))

theorem fockB_projVV_basis [CharZero K] (sg : ι → DomWeight n) (F : Pol K ι n) (k : VVIdx sg) :
    fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) = fockB (bVVfun K sg k) F := by
  classical
  have hG := Matrix.mul_nonsing_inv (Br.gramB (K := K) sg) (Ne.isUnit (gramB_det_ne_zero sg))
  have h1 : fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) =
      ∑ i, ∑ j, Br.gramB (K := K) sg k i * (Br.gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) F := by
    rw [← fockBL_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Br.projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Submodule.coe_sum,
      Submodule.coe_smul, map_sum, map_smul, bVV_coe, fockBL_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Br.gramB (K := K) sg k i = fockB (bVVfun K sg k) (bVVfun K sg i) from rfl]
    ring
  rw [h1, Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Matrix.mul_apply, hG, Matrix.one_apply]
  simp

theorem fockB_projVV [CharZero K] (sg : ι → DomWeight n) (F y : Pol K ι n) (hy : y ∈ VV K sg) :
    fockB y (Br.projVV sg F : Pol K ι n) = fockB y F := by
  rw [← (bVVfun_spec K sg).2] at hy
  simp only [← fockBL_apply]
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact fockB_projVV_basis sg F k
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx]

theorem projVV_map [CharZero K] [CharZero K'] (sg : ι → DomWeight n) (F : Pol K ι n) :
    (Br.projVV sg (map φ F) : Pol K' ι n) = map φ (Br.projVV sg F : Pol K ι n) := by
  have h := eq_zero_of_fockB sg
    (Br.projVV sg (map φ F) - ⟨map φ (Br.projVV sg F : Pol K ι n), map_mem_VV φ sg _ (Br.projVV sg F).2⟩) fun i => by
      rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply, fockB_projVV_basis]
      obtain ⟨Y, hY, hY'⟩ := bVVfun_desc φ sg i
      rw [hY', fockB_map, fockB_map, fockB_projVV sg F Y hY, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp h)

variable {N : ℕ} (hN : N = n + 1)

omit [Fintype ι] in
theorem coefLast_map (b : ι → Fin n → ℕ) (F : Pol K ι N) :
    Br.coefLast hN b (map φ F) = map φ (Br.coefLast hN b F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have h1 : (monomial m a : Pol K ι N) = a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial m (φ a) : Pol K' ι N) = φ a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [map_monomial, h2, h1, map_smul, map_smul, Br.coefLast_monomial, Br.coefLast_monomial]
    split_ifs
    · simp [smul_monomial, map_monomial]
    · simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem xiBr_map (lam : DomWeight N) (sg : DomWeight n) : map φ (Br.xiBr K hN lam sg) = Br.xiBr K' hN lam sg := by
  simp only [Br.xiBr, Br.zMinor, map_prod, map_mul, map_pow, fk_map_initMinor, Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map]

theorem brConst_map (lam : ι → DomWeight N) (sg : ι → DomWeight n) :
    φ (Br.brConst hN K lam sg) = Br.brConst hN K' lam sg := by
  simp only [Br.brConst, Br.kapBr, map_prod, map_mul, map_div₀, map_intCast, ← fockB_map, xiBr_map, extremal,
    Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

theorem branchingProjection_map [CharZero K] [CharZero K'] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Pol K ι N) :
    (Br.brStdP hN lam sg (map φ F) : Pol K' ι n) = map φ (Br.brStdP hN lam sg F : Pol K ι n) := by
  simp only [Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [coefLast_map, projVV_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, brConst_map]

theorem brOne_map [CharZero K] [CharZero K'] (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) :
    GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K' hN lam sg (map φ f) = map φ (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K hN lam sg f) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply]
  rw [← map_rename, branchingProjection_map, map_rename]

end BaseChange

end GlobalTheory.Proof.TensorMapDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchMembers

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem lamTrue_lo (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (j : Fin R.k) (h : i.1 = j.1) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      (W.hc u τ).u j - ((R.k : ℚ) - 1) / 2 + (j.1 : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : i.1 < R.k := h ▸ j.2
  have e : (⟨i.1, hi⟩ : Fin R.k) = j := Fin.ext h
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_left hi, e]
  unfold hcToWeightQ rhoVec
  ring

theorem lamTrue_hi (u : Word) (τ : X.Tau) (i : Fin (R.N R.m)) (B ρ : ℕ) (hρ : ρ < R.t + 1)
    (h : i.1 = R.k + B * (R.t + 1) + ρ) :
    ((W.lamTrue u R.m τ).w i : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hi : ¬ i.1 < R.k := by omega
  have e1 : (i.1 - R.k) / (R.t + 1) = B := by
    have : i.1 - R.k = B * (R.t + 1) + ρ := by omega
    rw [this]
    exact (divmod (R.t + 1) B ρ hρ).1
  have hB : B < R.m := e1 ▸ R.blk_lt le_rfl i hi
  rw [Wts.lamTrue_eq, Wts.lamN_eq W u le_rfl, dite_eq_right hi, RowPar.eAt_of _ hB]
  simp only [e1]
  unfold wG
  push_cast
  ring

theorem sgTrue_entry (hW : W.Ok) (u : Word) (τ : X.Tau) (i : Fin (R.N R.m - 1)) :
    ((W.sgTrue τ).w i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i.1 - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i.1 : ℚ) := by
  unfold Wts.sgTrue
  rw [← hW.hc_row u τ, RowPar.sgTrue_eq]
  unfold rhoVec
  have c1 : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (R.N_pos R.m)]
    unfold Ranks.N
    push_cast
    ring
  rw [c1]
  ring

theorem nonneg_sub_of_lt {a b : ℤ} (h : (b : ℚ) - 1 < a) : 0 ≤ a - b := by
  have : b - 1 < a := by exact_mod_cast h
  omega

theorem interlace (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) := by
  intro i
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hs := sgTrue_entry W hW u τ i
  have hi : i.1 < R.k + R.m * (R.t + 1) - 1 := i.2
  have hS : (Br.iS (N_m_succ R) i).1 = i.1 + 1 := rfl
  have hC : (Br.iC (N_m_succ R) i).1 = i.1 := rfl
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  unfold Br.aBr Br.bBr
  by_cases h1 : i.1 < R.k - 1
  · rw [RowPar.sgHC_lo _ h1, RowPar.vb_lo _ h1] at hs
    have a1 := (W.hc u τ).u_gt_v ⟨i.1, h1⟩
    have a2 := (W.hc u τ).v_gt_u ⟨i.1, h1⟩
    have l1 := lamTrue_lo W u τ _ ⟨i.1 + 1, by omega⟩ hS
    have l2 := lamTrue_lo W u τ _ ⟨i.1, by omega⟩ hC
    simp only at a1 a2 l1 l2
    push_cast at l1
    exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩
  · obtain ⟨B, ρ, hρ, hn⟩ : ∃ B ρ, ρ < R.t + 1 ∧ i.1 = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(i.1 - (R.k - 1)) / (R.t + 1), (i.1 - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (i.1 - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    have l1 := lamTrue_hi W u τ _ B ρ hρ (by rw [hS]; omega : (Br.iS (N_m_succ R) i).1 = _)
    rw [hn] at hs
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
    · rw [Nat.add_zero, RowPar.sgHC_b] at hs
      push_cast [ck] at hs
      have g1 := RowPar.gap_be (W.hc u τ) hBm
      refine ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt ?_⟩
      rcases B with _ | B
      · have l2 := lamTrue_lo W u τ _ ⟨R.k - 1, by omega⟩ (by rw [hC]; simp only; omega : (Br.iC (N_m_succ R) i).1 = _)
        have a1 := (W.hc u τ).u_last_gt (by omega) hBm
        rw [RowPar.bAt_of _ hBm] at hs
        simp only [ck] at l2
        push_cast at hs
        linarith
      · have l2 := lamTrue_hi W u τ _ B R.t (by omega)
          (by rw [hC, hn, Nat.succ_mul]; omega : (Br.iC (N_m_succ R) i).1 = _)
        have g2 := RowPar.gap_eb (W.hc u τ) hBm
        push_cast at hs
        linarith
    · rw [RowPar.sgHC_e _ B ρ hρ0 (by omega)] at hs
      push_cast [ck] at hs
      have l2 := lamTrue_hi W u τ _ B (ρ - 1) (by omega) (by rw [hC]; omega : (Br.iC (N_m_succ R) i).1 = _)
      exact ⟨nonneg_sub_of_lt (by linarith), nonneg_sub_of_lt (by linarith)⟩

theorem members : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Members :=
  fun _ _ _ W hW u τ => ⟨interlace W hW u τ, members_sameShift W hW u τ⟩

end GlobalTheory.BranchMembers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.BranchBasis

theorem mem_sumLat {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 K) (Fin n → K)) (t : K)
    (x : Fin N → K) :
    x ∈ Br.sumLat hN M t ↔ (fun a => x (Br.iC hN a)) ∈ M ∧ ∃ c : 𝓞 K, x (Br.iL hN) = (c : K) * t := Iff.rfl

theorem mem_colLat {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, ∀ a, ∑ j, (c j : K) * (B : Matrix (Fin n) (Fin n) K) a j = x a := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]

theorem colLat_block {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (t : K) (B : GL (Fin n) K)
    (B' : GL (Fin N) K) (h : IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t) :
    colLat B' = Br.sumLat hN (colLat B) t := by
  obtain ⟨h1, h2, h3⟩ := h
  ext x
  rw [mem_sumLat, mem_colLat, mem_colLat]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun j => c (Br.iC hN j), fun a => ?_⟩, c (Br.iL hN), ?_⟩
    · rw [← hc, sum_split hN]
      simp only [h1, (h2 _).1, mul_zero, add_zero]
    · rw [← hc, sum_split hN]
      simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add]
  · rintro ⟨⟨c, hc⟩, d, hd⟩
    refine ⟨fun j => if hj : j.val < n then c ⟨j.val, hj⟩ else d, fun a => ?_⟩
    rw [sum_split hN]
    have e1 : ∀ j : Fin n, (if hj : (Br.iC hN j).val < n then c ⟨(Br.iC hN j).val, hj⟩ else d) = c j :=
      fun j => dif_pos j.2
    have e2 : (if hj : (Br.iL hN).val < n then c ⟨(Br.iL hN).val, hj⟩ else d) = d := dif_neg (lt_irrefl n)
    simp only [e1, e2]
    rcases cases_idx hN a with rfl | ⟨a, rfl⟩
    · simp only [h3, (h2 _).2, mul_zero, Finset.sum_const_zero, zero_add, hd]
    · simp only [h1, (h2 _).1, mul_zero, add_zero]
      exact hc a

theorem localization_sumLat_le {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K))
    (M M₂ : Submodule (𝓞 K) (Fin n → K)) (t : K) (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M₂) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M t) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Br.sumLat hN M₂ t) := by
  rintro x ⟨s, hs, hx1, c, hc⟩
  have h0 : (fun a => (s • x) (Br.iC hN a)) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx1⟩
  obtain ⟨u, hu, hux⟩ := h h0
  refine ⟨u * s, Submonoid.mul_mem _ hu hs, ?_⟩
  rw [mul_smul, mem_sumLat]
  refine ⟨hux, u * c, ?_⟩
  rw [Pi.smul_apply, hc, Algebra.smul_def]
  push_cast
  exact (mul_assoc _ _ _).symm

theorem isBasisAt_block : ∀ (K : Type) [Field K] [NumberField K] (N n : ℕ) (hN : N = n + 1) (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (t : K) (B : GL (Fin n) K) (B' : GL (Fin N) K), IsBlock hN (B' : Matrix (Fin N) (Fin N) K) (B : Matrix (Fin n) (Fin n) K) t → IsBasisAt w M B → IsBasisAt w (Br.sumLat hN M t) B' := by
  intro K _ _ N n hN w M t B B' hB h
  unfold IsBasisAt at h ⊢
  rw [colLat_block hN t B B' hB]
  exact le_antisymm (localization_sumLat_le hN w _ _ t h.le) (localization_sumLat_le hN w _ _ t h.ge)

end GlobalTheory.BranchBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.Proof.IntegralPowerExpansion

variable {E : Type} [Field E] [NumberField E]

theorem intAt_int (P : HeightOneSpectrum (𝓞 E)) (n : ℤ) : IntAt P (n : E) := by
  simpa using IntAt.coe P (n : 𝓞 E)

theorem q_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {n : ℤ}
    (h : IntAt P ((qOf P : E)⁻¹ * n)) : (qOf P : ℤ) ∣ n := by
  by_contra hn
  have hpr : Prime (qOf P : ℤ) := Nat.prime_iff_prime_int.1 hP.1
  obtain ⟨x, y, hxy⟩ := (hpr.coprime_iff_not_dvd).2 hn
  have hq := q_ne_zero hP
  have h1 : IntAt P ((qOf P : E)⁻¹) := by
    have e : (qOf P : E)⁻¹ = x + y * ((qOf P : E)⁻¹ * n) := by
      have := congrArg (Int.cast : ℤ → E) hxy
      push_cast at this
      field_simp
      linear_combination -this
    rw [e]
    exact (intAt_int P x).add ((intAt_int P y).mul h)
  rw [intAt_iff_val, map_inv₀, val_q hP, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem q_pow_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (k : ℕ) {n : ℤ}
    (h : IntAt P (((qOf P : E) ^ k)⁻¹ * n)) : (qOf P : ℤ) ^ k ∣ n := by
  have hq := q_ne_zero hP
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h1 : IntAt P ((qOf P : E)⁻¹ * n) := by
      have e : (qOf P : E)⁻¹ * n = (((qOf P : ℤ) ^ k : ℤ) : E) * (((qOf P : E) ^ (k + 1))⁻¹ * n) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (intAt_int P _).mul h
    obtain ⟨m, rfl⟩ := q_dvd_of_intAt hP h1
    have e : ((qOf P : E) ^ (k + 1))⁻¹ * (((qOf P : ℤ) * m : ℤ) : E) = ((qOf P : E) ^ k)⁻¹ * m := by
      push_cast
      field_simp
      ring
    rw [e] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

theorem valsQ_reps : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ,
    (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B,
      IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧
    ∀ a : E, IntAt P ((qOf P : E) ^ A * a) →
      ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  intro E _ _ P hP A B
  classical
  have hq := q_ne_zero hP
  constructor
  · intro a ha b hb h
    unfold LocE.valsQ at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_range] at hi hj
    have h1 : IntAt P (((qOf P : E) ^ (A + B))⁻¹ * (((i : ℤ) - j : ℤ) : E)) := by
      convert h using 1
      push_cast
      field_simp
      ring
    have h2 := q_pow_dvd_of_intAt hP _ h1
    have hi' : (i : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hi
    have hj' : (j : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hj
    have h3 : (i : ℤ) - j = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    have h4 : i = j := by omega
    rw [h4]
  · intro a ha
    obtain ⟨k, u, hu, e⟩ := exists_int_add_q_pow_mul hP (A + B) ha
    have hpos : (0 : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast pow_pos hP.1.pos (A + B)
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k hpos.ne')
    have hlt : i < qOf P ^ (A + B) := by
      have := Int.emod_lt_of_pos k hpos
      rw [hi] at this
      exact_mod_cast this
    have hk : (k : E) = i + (qOf P : E) ^ (A + B) * ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) := by
      have := Int.emod_add_mul_ediv k ((qOf P : ℤ) ^ (A + B))
      rw [hi] at this
      have h5 := congrArg (Int.cast : ℤ → E) this
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast] at h5
      exact h5.symm
    unfold LocE.valsQ
    refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hlt, rfl⟩, ?_⟩
    have h6 := (intAt_int P (k / (qOf P : ℤ) ^ (A + B))).add hu
    generalize ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) = m at hk h6
    have ea : a = ((qOf P : E) ^ A)⁻¹ * (i + (qOf P : E) ^ (A + B) * (m + u)) := by
      rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hq), e, hk]
      ring
    convert h6 using 1
    rw [ea]
    field_simp
    ring

end GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFractions_represent_primeNormQuotient : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  first | exact @GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | exact GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | (intros; apply GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions

theorem eN_eq_single {F : Type} [Field F] {N i : ℕ} (h : i < N) :
    Loc.eN F N i = Pi.single (⟨i, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {F : Type} [Field F] {N i : ℕ} (h : ¬ i < N) : Loc.eN F N i = 0 := by
  funext l
  have hl : l.1 ≠ i := fun e => h (e ▸ l.2)
  simp only [Loc.eN, hl, if_false, Pi.zero_apply]

theorem inX_single {F : Type} [Field F] {n c : ℕ} (s : Fin (n + c)) (hs : s.1 < n) :
    Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) = Pi.single s 1 := by
  funext l
  rw [inX_apply]
  by_cases hl : l.1 < n
  · simp only [hl, dif_pos, Pi.single_apply, Fin.ext_iff]
  · have hne : l ≠ s := fun e => hl (e ▸ hs)
    simp only [hl, dif_neg, not_false_eq_true, Pi.single_apply, hne, if_false]

theorem unfoldingAffineSpace_mem_iff_intrinsic : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  intro F _ n' c' n c hc hc' xj x
  subst hc'
  have hy : ∀ {a b : ℕ} (y : (Fin a → F) →ₗ[F] (Fin b → F)) (s : Fin a) (l : Fin b),
      y (Pi.single s 1) l = LinearMap.toMatrix' y l s := by
    intro a b y s l
    rw [LinearMap.toMatrix'_apply]
  have hM : ∀ (t : Loc.FC n' (c + 1) n c → F) (l : Fin (n + c)) (s : Fin (n' + (c + 1))),
      LinearMap.toMatrix' (Loc.xx1 xj t) l s =
        if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
        else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
        else if l.1 = n + (s.1 - n') then 1 else 0 := by
    intro t l s
    simp only [Loc.xx1, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨fun v => ?_, ?_, ?_⟩
    · have hcomp : (Loc.xx1 xj t).comp (Loc.inX F n' (c + 1)) = (Loc.inX F n c).comp xj := by
        refine (Pi.basisFun F (Fin n')).ext fun a => ?_
        rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply]
        have hi := inX_single (F := F) (n := n') (c := c + 1) (Fin.castAdd (c + 1) a) a.2
        simp only [Fin.val_castAdd, Fin.eta] at hi
        rw [hi]
        funext l
        rw [hy, hM, inX_apply]
        have hnf : ¬ Loc.IsFree n' n c l.1 (Fin.castAdd (c + 1) a).1 := by
          simp only [Loc.IsFree, Fin.val_castAdd]
          omega
        rw [dif_neg hnf, dif_pos (by simp only [Fin.val_castAdd]; exact a.2)]
        by_cases hl : l.1 < n
        · rw [dif_pos hl, dif_pos hl, hy]
          rfl
        · rw [dif_neg hl, dif_neg hl]
      exact LinearMap.congr_fun hcomp v
    · rw [eN_eq_single (show n' < n' + (c + 1) by omega)]
      funext l
      rw [hy, hM]
      have hnf : ¬ Loc.IsFree n' n c l.1 n' := by
        simp only [Loc.IsFree]
        omega
      rw [dif_neg hnf, dif_neg (lt_irrefl n'), Nat.sub_self, Nat.add_zero]
      simp only [Loc.eN]
    · intro s
      rw [mem_Ufl]
      intro l hl
      rw [Pi.sub_apply]
      by_cases hs : n' + s < n' + (c + 1)
      · rw [eN_eq_single hs, hy, hM]
        have hnf : ¬ Loc.IsFree n' n c l.1 (n' + s) := by
          have := l.2
          simp only [Loc.IsFree]
          omega
        rw [dif_neg hnf, dif_neg (Nat.not_lt.2 (Nat.le_add_right n' s))]
        change (if l.1 = n + (n' + s - n') then (1 : F) else 0) - _ = 0
        rw [Nat.add_sub_cancel_left]
        simp only [Loc.eN, sub_self]
      · rw [eN_eq_zero hs, map_zero]
        have hne : l.1 ≠ n + s := by
          have := l.2
          omega
        simp only [Loc.eN, hne, if_false, Pi.zero_apply, sub_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun p => x (Pi.single p.1.2 1) p.1.1, ?_⟩
    refine (Pi.basisFun F (Fin (n' + (c + 1)))).ext fun s => ?_
    rw [Pi.basisFun_apply]
    funext l
    rw [hy (Loc.xx1 xj _), hM]
    by_cases hf : Loc.IsFree n' n c l.1 s.1
    · rw [dif_pos hf]
    rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, ← inX_single s hs, h1, inX_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, hy]
      · rw [dif_neg hl, dif_neg hl]
    rw [dif_neg hs]
    have hsj : s.1 = n' + (s.1 - n') := by omega
    have hsingle : (Pi.single s 1 : Fin (n' + (c + 1)) → F) = Loc.eN F (n' + (c + 1)) (n' + (s.1 - n')) := by
      rw [eN_eq_single (show n' + (s.1 - n') < n' + (c + 1) by omega)]
      congr 1
      exact Fin.ext hsj
    rw [hsingle]
    by_cases h0 : s.1 - n' = 0
    · rw [h0]
      change x (Loc.eN F (n' + (c + 1)) n') l = if l.1 = n then 1 else 0
      rw [h2]
      simp only [Loc.eN]
    · have hmem := (mem_Ufl).1 (h3 (s.1 - n')) l (by
        simp only [Loc.IsFree] at hf
        omega)
      rw [Pi.sub_apply, sub_eq_zero] at hmem
      rw [hmem]
      simp only [Loc.eN]

end GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsicStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  first | exact @GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | exact GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | (intros; apply GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.LocalComponentChar


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem index_intV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (LocalAdditiveCharacterDual.intV F v).index = 0 := by
  by_contra hn
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (1 : ℤ))
  have hn' : (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := (LocalAdditiveCharacterDual.intV F v).nsmul_index_mem (t / (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v))
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hn'] at h
  have h1 : Valued.v t ≤ 1 := h
  rw [ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_localChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  intro F _ _ ψ hψ v hfin
  refine ⟨⟨psiV F ψ v, LocalAdditiveCharacterDual.psiV_zero F ψ v, LocalAdditiveCharacterDual.psiV_add F ψ v⟩, ⟨?_, fun t => hψ.2.1 _, ?_⟩,
    fun _ => rfl⟩
  · have h2 : Continuous fun x : Fv F v => pairA F 0 (singleV F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV F v)
    exact hψ.1.comp h2
  · by_contra h
    push Not at h
    have htop : LocalAdditiveCharacterDual.psiDual F ψ v = ⊤ := by
      rw [eq_top_iff]
      intro t _ s _
      exact h _
    apply hfin.1
    rw [htop, AddSubgroup.relIndex_top_right]
    exact index_intV F v

end GlobalTheory.LocalComponentChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddCharStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_adelicAddChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  first | exact @GlobalTheory.LocalComponentChar.exists_localChar | exact GlobalTheory.LocalComponentChar.exists_localChar | (intros; apply GlobalTheory.LocalComponentChar.exists_localChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChange
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChange
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange

open GlobalTheory.Proof.NormalFormAtPrime

theorem relIndex_ne_zero_of_cover {V : Type} [AddCommGroup V] (H K : AddSubgroup V) (S : Finset V)
    (h : ∀ k ∈ K, ∃ s ∈ S, k - s ∈ H) : H.relIndex K ≠ 0 := by
  rw [← QuotientAddGroup.ker_mk' H, AddSubgroup.relIndex_ker]
  have hf : ((K.map (QuotientAddGroup.mk' H) : AddSubgroup (V ⧸ H)) : Set (V ⧸ H)).Finite := by
    refine (S.finite_toSet.image (QuotientAddGroup.mk' H)).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨s, hs, e⟩ := h k hk
    exact ⟨s, hs, (QuotientAddGroup.eq_iff_sub_mem.2 e).symm⟩
  have : Finite (K.map (QuotientAddGroup.mk' H)) := hf
  exact Nat.card_pos.ne'

variable {E : Type} [Field E] [NumberField E]

def lat (P : HeightOneSpectrum (𝓞 E)) (ι : Type) (c : E) : AddSubgroup (ι → E) where
  carrier := {u | ∀ i, IntAt P (c * u i)}
  zero_mem' := fun i => by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  add_mem' := fun {a b} ha hb i => by
    have := (ha i).add (hb i)
    rwa [← mul_add] at this
  neg_mem' := fun {a} ha i => by
    have := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (ha i)
    simpa using this

theorem lat_le {P : HeightOneSpectrum (𝓞 E)} {ι : Type} {c c' : E} (k : ℕ) (h : c' = (qOf P : E) ^ k * c) :
    lat P ι c ≤ lat P ι c' := fun u hu i => by
  rw [h, mul_assoc]
  exact intAt_pow_mul k (hu i)

theorem exists_fin {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {κ : Type} [Fintype κ] (x : κ → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ k, IntAt P ((qOf P : E) ^ m' * x k) := by
  choose m hm using h
  refine ⟨Finset.univ.sup fun k => m (x k), fun m' hm' k => intAt_pow_mono (le_trans ?_ hm') (hm (x k))⟩
  exact Finset.le_sup (f := fun k => m (x k)) (Finset.mem_univ k)

theorem exists_bound {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {ι : Type} [Fintype ι] [DecidableEq ι] (T : (ι → E) →ₗ[E] (ι → E)) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ (c : E) (u : ι → E), u ∈ lat P ι c → T u ∈ lat P ι ((qOf P : E) ^ m' * c) := by
  obtain ⟨m, hm⟩ := exists_fin h (fun p : ι × ι => T (Pi.single p.1 1) p.2)
  refine ⟨m, fun m' hm' c u hu l => ?_⟩
  have e : T u = ∑ s, u s • T (Pi.single s 1) := by
    conv_lhs => rw [show u = ∑ s, u s • (Pi.single s (1 : E) : ι → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply, Finset.mul_sum]
  refine intAt_sum _ _ fun s _ => ?_
  have := (hu s).mul (hm m' hm' (s, l))
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem affine : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  classical
  intro h1 h2 h3 E _ _ K _ _ P hP ι _ _ f N hf T b
  have hq := qOf_ne_zero P
  have hs : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x) := fun x => by
    obtain ⟨m, hm⟩ := (h1 E P 1 1).1 (fun _ => x)
    exact ⟨m, hm m le_rfl 0⟩
  have sep : ∀ A B : ℕ, ∀ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      ∀ s' ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      s - s' ∈ lat P ι ((qOf P : E) ^ B)⁻¹ → s = s' := fun A B s hs s' hs' h => by
    funext i
    exact (h3 E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  have cov : ∀ A B : ℕ, ∀ v ∈ lat P ι ((qOf P : E) ^ A),
      ∃ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), v - s ∈ lat P ι ((qOf P : E) ^ B)⁻¹ :=
    fun A B v hv => by
      choose s hs hs' using fun i => (h3 E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩
  have inv : ∀ v, ∀ u ∈ lat P ι ((qOf P : E) ^ N)⁻¹, f (v + u) = f v := fun v u hu => by
    have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  obtain ⟨m1, hm1⟩ := exists_bound hs T.toLinearMap
  obtain ⟨m2, hm2⟩ := exists_bound hs T.symm.toLinearMap
  obtain ⟨m3, hm3⟩ := exists_fin hs b
  obtain ⟨m, a1, a2, a3⟩ : ∃ m, m1 ≤ m ∧ m2 ≤ m ∧ m3 ≤ m := ⟨m1 + m2 + m3, by omega, by omega, by omega⟩
  have hT := hm1 m a1
  have hT' := hm2 m a2
  have hb : b ∈ lat P ι ((qOf P : E) ^ m) := hm3 m a3
  simp only [LinearEquiv.coe_coe] at hT hT'
  refine ⟨N + 2 * m, N + 2 * m, fun A B hA hB => ?_⟩
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le hB
  set A' := N + 2 * m + A with hA'
  set B' := N + 2 * m + B with hB'
  let L : AddSubgroup (ι → E) := lat P ι ((qOf P : E) ^ B')⁻¹
  let L' : AddSubgroup (ι → E) := L.comap T.symm.toLinearMap.toAddMonoidHom
  have mL' : ∀ u, u ∈ L' ↔ T.symm u ∈ L := fun u => Iff.rfl
  have hL'le : L' ≤ lat P ι ((qOf P : E) ^ m * ((qOf P : E) ^ B')⁻¹) := fun u hu => by
    have := hT _ _ ((mL' u).1 hu)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hleL' : lat P ι ((qOf P : E) ^ (B' + m))⁻¹ ≤ L' := fun u hu => by
    have := hT' _ _ hu
    rw [mL']
    convert this using 2
    field_simp
    ring
  have hLN : L ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := lat_le (2 * m + B) (by rw [hB']; field_simp; ring)
  have hL'N : L' ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := hL'le.trans (lat_le (m + B) (by rw [hB']; field_simp; ring))
  have hN0 : lat P ι ((qOf P : E) ^ N)⁻¹ ≤ lat P ι ((qOf P : E) ^ 0) := lat_le N (by field_simp)
  have hinj : Function.Injective fun t => T t + b := fun s t h => T.injective (add_right_cancel h)
  have key := h2 (ι → E) K f L L' (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B')
    ((Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B').image fun t => T t + b)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => by
      obtain ⟨s, hs, e⟩ := cov 0 (B' + m) k (hN0 (hLN hk))
      exact ⟨s, hs, hleL' e⟩)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => cov 0 B' k (hN0 (hL'N hk)))
    (fun v u hu => inv v u (hLN hu)) (fun v u hu => inv v u (hL'N hu)) (sep A' B')
    (fun v hv => cov A' B' v (lat_le (c := (qOf P : E) ^ N) (2 * m + A) (by rw [hA']; ring) (hf.1 v hv)))
    (fun s hs s' hs' h => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
      rw [mL', add_sub_add_right_eq_sub, ← map_sub, LinearEquiv.symm_apply_apply] at h
      rw [sep A' B' t ht t' ht' h])
    (fun v hv => by
      have e1 : v - b ∈ lat P ι ((qOf P : E) ^ (N + m)) :=
        sub_mem (lat_le (c := (qOf P : E) ^ N) m (by ring) (hf.1 v hv)) (lat_le N (by ring) hb)
      obtain ⟨s, hs, e⟩ := cov A' B' _ (lat_le A (by rw [hA']; ring) (hT' _ _ e1))
      refine ⟨T s + b, Finset.mem_image_of_mem _ hs, ?_⟩
      rw [mL']
      convert e using 1
      rw [show v - (T s + b) = (v - b) - T s by abel, map_sub, LinearEquiv.symm_apply_apply])
  rw [Finset.sum_image hinj.injOn] at key
  have hqK : (qOf P : K) ≠ 0 := by
    have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hw : (((qOf P : K) ^ B')⁻¹) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hqK))
  unfold boxSum
  rw [mul_ne_zero_iff_left hw, mul_ne_zero_iff_left hw]
  exact key.symm

end GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChangeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxSum_ne_zero_invariant_affineChange : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  first | exact @GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | exact GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | (intros; apply GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelEqParahoricCategory
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.level_eq_parahoric_category

theorem conj_res {k : Type} [CommRing k] {n c : ℕ} {ρ r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    {γ g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hγ : ∀ x, ρ (Loc.inX k n c x) = Loc.inX k n c (γ x))
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (x : Fin n → k) :
    (ρ⁻¹ * r * ρ) (Loc.inX k n c x) = Loc.inX k n c ((γ⁻¹ * g * γ) x) := by
  show ρ.symm (r (ρ _)) = Loc.inX k n c (γ.symm (g (γ x)))
  rw [hγ, hg, LinearEquiv.symm_apply_eq, hγ, LinearEquiv.apply_symm_apply]

theorem n1Arg_conj_eq {F : Type} [Field F] {n c : ℕ} {ρ r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hρ : ρ ∈ Loc.R1 F n c) (hr : r ∈ Loc.R1 F n c) : Loc.n1Arg (ρ⁻¹ * r * ρ) = Loc.n1Arg r := by
  have h1 := unipotentCharacterArgument_mul_stabilizer hρ.1 (mul_mem (mul_mem (inv_mem hρ) hr) hρ).1
  have h2 := unipotentCharacterArgument_mul_stabilizer hr.1 hρ.1
  have e : ρ * (ρ⁻¹ * r * ρ) = r * ρ := by group
  rw [e, h2] at h1
  linear_combination -h1

end GlobalTheory.Proof.level_eq_parahoric_category
end
