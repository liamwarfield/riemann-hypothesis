module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SinvOfSwt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.BlkConjTranspose
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SmoothCompositionIdentity.MatOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Transport
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker ComplexOrder

namespace PositivityTheory.KB.BlockInvariants

namespace BlockSumPreservesCone

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem mat_one (N : ℕ) (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem mat_padL (n M : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (padL n M h) w = padM (mat h w) := rfl

omit [NumberField L] in
theorem mat_eL (n M : ℕ) (w : InfinitePlace L) :
    mat (eL (L := L) n M) w = padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := rfl

def kr {R : Type} [CommRing R] (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (d * n)) (Fin (d * n)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ A)

theorem mat_blkL (d n : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (blkL d n h) w = kr d (mat h w) := rfl

theorem padMat_eq {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ) = padM A + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n <;> simp [padMat, padM, hij]

theorem padMat_conjTranspose {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ)ᴴ = padMat ℂ Aᴴ := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · have hji : (j : ℕ) < n ∧ (i : ℕ) < n := ⟨hij.2, hij.1⟩
    simp [padMat, hij]
  · have hji : ¬((j : ℕ) < n ∧ (i : ℕ) < n) := fun h => hij ⟨h.2, h.1⟩
    by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, hji, e, Ne.symm e]

theorem padMat_mul {n M : ℕ} (h : n ≤ M) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ (A * B) : Matrix (Fin M) (Fin M) ℂ) = padMat ℂ A * padMat ℂ B :=
  (padHom ℂ h).map_mul A B

theorem padMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n M : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    (padMat R A : Matrix (Fin M) (Fin M) R).map f = padMat S (A.map f) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp [padMat, hij]
  · by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, e]

theorem kr_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (kr d A).map f = kr d (A.map f) := by
  ext i j
  simp only [kr, reindex_apply, map_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  by_cases h : i.divNat = j.divNat <;> simp [Matrix.one_apply, h]

theorem kr_conjTranspose (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : (kr d A)ᴴ = kr d Aᴴ := by
  ext i j
  simp only [kr, reindex_apply, conjTranspose_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  by_cases h : i.divNat = j.divNat <;> simp [Matrix.one_apply, eq_comm, h]

theorem kr_mul (d : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : kr d (A * B) = kr d A * kr d B := by
  simp only [kr, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

omit [NumberField L] in
theorem coe_emb_inv {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem coe_stab {R : Type} [CommRing R] {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) R) :
    ((stab R n N h g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) = padMat R (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem coe_psi {R : Type} [CommRing R] (d n : ℕ) (g : GL (Fin n) R) :
    ((psi R d n g : GL (Fin (d * n)) R) : Matrix (Fin (d * n)) (Fin (d * n)) R) =
      kr d (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem compCLM_comp {V W X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℕ} (f : X [⋀^Fin q]→L[ℝ] ℝ)
    (A : W →L[ℝ] X) (B : V →L[ℝ] W) :
    (f.compContinuousLinearMap A).compContinuousLinearMap B = f.compContinuousLinearMap (A.comp B) := by
  ext v; rfl

theorem fromBlocks_posDef {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (fromBlocks H 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · unfold IsHermitian
    rw [fromBlocks_conjTranspose]
    simp [hH.isHermitian.eq]
  · have hxe : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
    have hst : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
      ext (i | i) <;> rfl
    rw [hst, hxe, fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
    by_cases ha : x ∘ Sum.inl = 0
    · have hb : x ∘ Sum.inr ≠ 0 := by
        intro hb
        apply hx
        rw [hxe, ha, hb]
        ext (i | i) <;> rfl
      rw [ha, Matrix.mulVec_zero, star_zero, dotProduct_zero, zero_add]
      exact dotProduct_star_self_pos_iff.2 hb
    · exact add_pos_of_pos_of_nonneg (hH.dotProduct_mulVec_pos ha) (dotProduct_star_self_nonneg _)

theorem padMat_posDef {n M : ℕ} (h : n ≤ M) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (padMat ℂ H : Matrix (Fin M) (Fin M) ℂ).PosDef := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [padMat_add, reindex_apply]
  exact PosDef.submatrix (fromBlocks_posDef hH) (Equiv.injective _)

theorem kr_posDef (d : ℕ) {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) : (kr d H).PosDef := by
  rw [kr, reindex_apply]
  exact PosDef.submatrix (PosDef.one.kronecker hH) (Equiv.injective _)

end BlockSumPreservesCone

open BlockSumPreservesCone

theorem tStab : TStab := by
  intro L _ _ n N h γ
  apply HS_ext
  intro w
  rw [mat_add]
  show mat (actL (emb L N (stab (𝓞 L) n N h γ)) (one L N).1) w =
    padM (mat (actL (emb L n γ) (one L n).1) w) + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_stab, padMat_map, mat_one, mat_one,
    padMat_conjTranspose]
  simp only [Matrix.mul_one]
  rw [← padMat_mul h, padMat_eq]

theorem tBlk : TBlk := by
  intro L _ _ d n γ
  apply HS_ext
  intro w
  show mat (actL (emb L (d * n) (psi (𝓞 L) d n γ)) (one L (d * n)).1) w =
    kr d (mat (actL (emb L n γ) (one L n).1) w)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_psi, kr_map, mat_one, mat_one,
    kr_conjTranspose]
  simp only [Matrix.mul_one]
  rw [kr_mul]

theorem pStab : PStab := by
  intro L _ _ n N q hnN ω hω g h hh
  let g' : Gp L N := fun w => stab ℂ n N hnN (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((stab ℂ n N hnN (g w))⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = _
    rw [← map_inv, coe_stab]
  have hpadM : ∀ Y : Matrix (Fin n) (Fin n) ℂ, (padM Y : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ Y - padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := fun Y => by
    rw [padMat_eq Y, add_sub_cancel_right]
  have hJ : padL n N (actL g h) + eL n N = actL g' (padL n N h + eL n N) := HS_ext fun w => by
    rw [mat_add, mat_actL, mat_add, mat_padL, mat_padL, mat_eL, mat_actL, hg', ← padMat_eq (mat h w),
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_eq]
  have hP : (padL n N).comp (actL g) = (actL g').comp (padL (L := L) n N) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_padL, mat_actL, mat_actL, mat_padL, hg', hpadM, hpadM, Matrix.mul_sub, Matrix.sub_mul,
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN,
      Matrix.mul_zero, Matrix.zero_mul]
  have hpos : padL n N h + eL n N ∈ Pos L N := fun w => by
    rw [mat_add, mat_padL, mat_eL, ← padMat_eq]
    exact padMat_posDef hnN (hh w)
  show ((ω (padL n N (actL g h) + eL n N)).compContinuousLinearMap (padL n N)).compContinuousLinearMap
      (actL g) = (ω (padL n N h + eL n N)).compContinuousLinearMap (padL n N)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

theorem blockSum_preserves_cone : PBlk := by
  intro L _ _ d n q ω hω g h hh
  let g' : Gp L (d * n) := fun w => psi ℂ d n (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) =
      kr d (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((psi ℂ d n (g w))⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) = _
    rw [← map_inv, coe_psi]
  have hJ : blkL d n (actL g h) + 0 = actL g' (blkL d n h + 0) := HS_ext fun w => by
    rw [add_zero, add_zero, mat_actL, mat_blkL, mat_blkL, mat_actL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hP : (blkL d n).comp (actL g) = (actL g').comp (blkL (L := L) d n) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_blkL, mat_actL, mat_actL, mat_blkL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hpos : blkL d n h + 0 ∈ Pos L (d * n) := fun w => by
    rw [add_zero, mat_blkL]
    exact kr_posDef d (hh w)
  show ((ω (blkL d n (actL g h) + 0)).compContinuousLinearMap (blkL d n)).compContinuousLinearMap
      (actL g) = (ω (blkL d n h + 0)).compContinuousLinearMap (blkL d n)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

end PositivityTheory.KB.BlockInvariants

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PlacePermOperatorCommutantSpan
noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightTwoPolynomials

section Poly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def mt (x : Fin q → Matrix ι ι ℂ) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  Matrix.of fun I J => ∏ i, x i (I i) (J i)

theorem tp_sum {K : Type} [Fintype K] [DecidableEq K] (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    tp q (∑ k, c k • M k) = ∑ f : Fin q → K, (∏ j, c (f j)) • mt (fun j => M (f j)) := by
  ext I J
  simp only [tp, mt, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]


open MvPolynomial in
def polyOf {K : Type} [Fintype K] (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ)
    (M : K → Matrix ι ι ℂ) : MvPolynomial K ℂ :=
  ∑ f : Fin q → K, C (φ (mt fun j => M (f j))) * ∏ j, X (f j)

open MvPolynomial in
theorem eval_polyOf {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    eval c (polyOf φ M) = φ (tp q (∑ k, c k • M k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tp_sum, map_sum, polyOf, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, eval_C, map_prod]
  simp only [eval_X]
  ring

open MvPolynomial in
theorem totalDegree_polyOf {K : Type} [Fintype K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) :
    (polyOf φ M).totalDegree ≤ q := by
  unfold polyOf
  refine totalDegree_finsetSum_le fun f _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  simp [totalDegree_X]

theorem grid {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (S : K → Finset ℂ)
    (hS : ∀ k, q < (S k).card) (h0 : ∀ c : K → ℂ, (∀ k, c k ∈ S k) → φ (tp q (∑ k, c k • M k)) = 0)
    (c : K → ℂ) : φ (tp q (∑ k, c k • M k)) = 0 := by
  have hP : polyOf φ M = 0 := MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ S
    (fun k => lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (totalDegree_polyOf φ M)) (hS k))
    (fun x hx => by rw [eval_polyOf]; exact h0 x hx)
  rw [← eval_polyOf, hP, map_zero]

end Poly

section GlobalTheory

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem blk_apply (d : W → Matrix (Fin m) (Fin m) ℂ) (x y : Ix W m) :
    blk d x y = if x.1 = y.1 then d x.1 x.2 y.2 else 0 := rfl

theorem blk_add (d e : W → Matrix (Fin m) (Fin m) ℂ) : blk (d + e) = blk d + blk e := by
  ext x y; simp only [blk_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem blk_smul (a : ℂ) (d : W → Matrix (Fin m) (Fin m) ℂ) : blk (a • d) = a • blk d := by
  ext x y; simp only [blk_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem blk_sum {K : Type} (s : Finset K) (d : K → W → Matrix (Fin m) (Fin m) ℂ) :
    blk (∑ k ∈ s, d k) = ∑ k ∈ s, blk (d k) := by
  ext x y; simp only [blk_apply, Matrix.sum_apply, Finset.sum_apply]; split_ifs <;> simp

theorem eq_blk (M : Matrix (Ix W m) (Ix W m) ℂ) (hM : ∀ x y : Ix W m, x.1 ≠ y.1 → M x y = 0) :
    M = blk (fun w a b => M (w, a) (w, b)) := by
  ext x y
  change M x y = if x.1 = y.1 then M (x.1, x.2) (x.1, y.2) else 0
  split_ifs with h
  · obtain ⟨w, a⟩ := x; obtain ⟨w', b⟩ := y
    simp only at h; subst h; rfl
  · exact hM x y h

theorem herm_of_unit (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) (hd : ∀ w, (d w).IsHermitian) : φ (tp q (blk d)) = 0 := by
  set v : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hv : ∀ w, v w ∈ unitaryGroup (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary).2
  let M : Ix W m → Matrix (Ix W m) (Ix W m) ℂ := fun k =>
    blk fun w => if w = k.1 then v w * diagonal (Pi.single k.2 1) * star (v w) else 0
  have hsum : ∀ c : Ix W m → ℂ, ∑ k, c k • M k =
      blk fun w => v w * diagonal (fun a => c (w, a)) * star (v w) := by
    intro c
    simp_rw [M, ← blk_smul, ← blk_sum]
    congr 1
    funext w
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single w]
    · simp only [Pi.smul_apply, if_true]
      have hd1 : ∑ x : Fin m, c (w, x) • diagonal (Pi.single x (1 : ℂ)) = diagonal fun a => c (w, a) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
        split_ifs with h
        · subst h; simp [Pi.single_apply]
        · simp
      rw [← hd1, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · intro w' _ hw'
      simp [Ne.symm hw']
    · simp
  have hcirc : ∀ c : Ix W m → ℂ, (∀ k, ‖c k‖ = 1) → φ (tp q (∑ k, c k • M k)) = 0 := by
    intro c hc
    rw [hsum]
    refine hU _ fun w => ?_
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (hv w) ?_) (Unitary.star_mem (hv w))
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, Pi.one_apply]
    rw [Complex.star_def, Complex.mul_conj', hc (w, a)]
    simp
  have hq : 0 < q + 1 := Nat.succ_pos q
  have hζ := Complex.isPrimitiveRoot_exp (q + 1) (Nat.succ_ne_zero q)
  have hall := grid φ M (fun _ => Polynomial.nthRootsFinset (q + 1) (1 : ℂ))
    (fun _ => by rw [hζ.card_nthRootsFinset]; omega)
    (fun c hc => hcirc c fun k => Complex.norm_eq_one_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hq (1 : ℂ)).1 (hc k)) (Nat.succ_ne_zero q))
  have := hall fun k => ((hd k.1).eigenvalues k.2 : ℂ)
  rw [hsum] at this
  have e : d = fun w => v w * diagonal (fun a => ((hd w).eigenvalues a : ℂ)) * star (v w) := by
    funext w
    conv_lhs => rw [(hd w).spectral_theorem]
    rfl
  rw [e]
  exact this

theorem all_of_herm (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hH : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, (d w).IsHermitian) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) : φ (tp q (blk d)) = 0 := by
  set H : W → Matrix (Fin m) (Fin m) ℂ := fun w => (2 : ℂ)⁻¹ • (d w + (d w)ᴴ)
  set K : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((2 : ℂ)⁻¹ * -Complex.I) • (d w - (d w)ᴴ)
  let M : Fin 2 → Matrix (Ix W m) (Ix W m) ℂ := ![blk H, blk K]
  have hM : ∀ c : Fin 2 → ℂ, ∑ k, c k • M k = blk (c 0 • H + c 1 • K) := by
    intro c
    simp [M, Fin.sum_univ_two, blk_add, blk_smul]
  have hall := grid φ M (fun _ => (Finset.range (q + 1)).image (Nat.cast : ℕ → ℂ))
    (fun _ => by rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]; omega)
    (fun c hc => by
      rw [hM]
      refine hH _ fun w => ?_
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hc 0)
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 (hc 1)
      rw [← ha, ← hb]
      simp only [IsHermitian, Pi.add_apply, Pi.smul_apply, H, K, conjTranspose_add,
        conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      simp only [star_natCast, star_mul', star_inv₀, star_ofNat, star_neg, Complex.star_def,
        Complex.conj_I]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring)
  have := hall ![1, Complex.I]
  rw [hM] at this
  have e : d = (![1, Complex.I] : Fin 2 → ℂ) 0 • H + (![1, Complex.I] : Fin 2 → ℂ) 1 • K := by
    funext w
    ext i j
    simp only [Pi.add_apply, Pi.smul_apply, H, K, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (2 : ℂ)⁻¹ * (d w i j - (d w)ᴴ i j) * Complex.I_sq
  rw [e]
  exact this

end GlobalTheory

section Comm

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_apply (σ : Equiv.Perm (Fin q)) (w : Fin q → W) (I J : Fin q → Ix W m) :
    perm' σ w I J = if (∀ i, (I i).1 = w i) ∧ J = I ∘ σ then 1 else 0 := rfl

theorem mul_perm' (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (Z * perm' σ w : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, ((B ∘ σ.symm) i).1 = w i) then Z A (B ∘ σ.symm) else 0 := by
  have hB : (B ∘ σ.symm) ∘ σ = B := by funext i; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (B ∘ σ.symm)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, hB.symm⟩ h1
    · rw [mul_zero]
  · intro K _ hK
    rw [perm'_apply, if_neg, mul_zero]
    rintro ⟨-, rfl⟩
    exact hK (by funext i; simp)
  · simp

theorem perm'_mul (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (perm' σ w * Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, (A i).1 = w i) then Z (A ∘ σ) B else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (A ∘ σ)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, rfl⟩ h1
    · rw [zero_mul]
  · intro K _ hK
    rw [perm'_apply, if_neg, zero_mul]
    rintro ⟨-, rfl⟩
    exact hK rfl
  · simp

theorem compat_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (I J : Fin q → Ix W m) (h : Z I J ≠ 0) : ∀ i, (I i).1 = (J i).1 := by
  have := congrFun (congrFun (hZ 1 fun i => (J i).1) I) J
  rw [mul_perm', perm'_mul] at this
  have e1 : J ∘ (1 : Equiv.Perm (Fin q)).symm = J := by funext i; rfl
  rw [e1] at this
  rw [if_pos (fun _ => rfl)] at this
  by_contra hne
  rw [if_neg hne] at this
  exact h this

theorem sym_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (σ : Equiv.Perm (Fin q)) (I J : Fin q → Ix W m) : Z (I ∘ σ) (J ∘ σ) = Z I J := by
  have := congrFun (congrFun (hZ σ fun i => (I i).1) I) (J ∘ σ)
  rw [mul_perm', perm'_mul] at this
  have hJ : (J ∘ σ) ∘ σ.symm = J := by funext i; simp
  rw [hJ] at this
  rw [if_pos (fun _ => rfl)] at this
  rw [← this]
  by_cases h : Z I J = 0
  · rw [h]; split_ifs <;> rfl
  · rw [if_pos fun i => (compat_of_comm Z hZ I J h i).symm]

end Comm

section Sym

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def symU (I J : Fin q → ι) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  ∑ σ : Equiv.Perm (Fin q), Matrix.single (I ∘ σ) (J ∘ σ) 1

theorem decomp (Z : Matrix (Fin q → ι) (Fin q → ι) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin q)) I J, Z (I ∘ σ) (J ∘ σ) = Z I J) :
    ((Nat.factorial q : ℕ) : ℂ) • Z = ∑ I, ∑ J, Z I J • symU I J := by
  have key : ∀ (σ : Equiv.Perm (Fin q)) (K L : Fin q → ι),
      ∑ I, ∑ J, Z I J * Matrix.single (I ∘ σ) (J ∘ σ) (1 : ℂ) K L = Z K L := by
    intro σ K L
    rw [Finset.sum_eq_single (K ∘ σ.symm)]
    · rw [Finset.sum_eq_single (L ∘ σ.symm)]
      · have h1 : (K ∘ σ.symm) ∘ σ = K := by funext i; simp
        have h2 : (L ∘ σ.symm) ∘ σ = L := by funext i; simp
        rw [h1, h2, Matrix.single_apply_same, mul_one, hsym]
      · intro J _ hJ
        rw [Matrix.single_apply, if_neg, mul_zero]
        rintro ⟨-, h⟩
        exact hJ (by rw [← h]; funext i; simp)
      · simp
    · intro I _ hI
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [Matrix.single_apply, if_neg, mul_zero]
      rintro ⟨h, -⟩
      exact hI (by rw [← h]; funext i; simp)
    · simp
  ext K L
  simp only [Matrix.smul_apply, Matrix.sum_apply, symU, smul_eq_mul, Finset.mul_sum]
  conv_rhs => enter [2, I]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem nu_iff (f : Fin q → Fin q) :
    (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1 ↔ Function.Bijective f := by
  constructor
  · intro h
    have hs : Function.Surjective f := by
      intro k
      by_contra hk
      push_neg at hk
      have := congrArg (fun g : Fin q →₀ ℕ => g k) h
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at this
      simpa [hk] using this
    exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  · intro h
    exact Fintype.sum_bijective f h _ _ fun _ => rfl

theorem sum_perm_mt (x : Fin q → Matrix ι ι ℂ) (I J : Fin q → ι)
    (hx : ∀ j, x j = Matrix.single (I j) (J j) 1) :
    ∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j)) = symU I J := by
  refine Finset.sum_congr rfl fun σ _ => ?_
  ext K L
  simp only [mt, of_apply, hx, Matrix.single_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨congrFun h1 i, congrFun h2 i⟩


open MvPolynomial in
theorem sym_zero (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (x : Fin q → Matrix ι ι ℂ)
    (h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • x j)) = 0) :
    φ (∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j))) = 0 := by
  have hP : polyOf φ x = 0 := MvPolynomial.funext fun t => by rw [eval_polyOf, h0, map_zero]
  have hc := congrArg (fun p => AddMonoidAlgebra.coeff p (∑ j : Fin q, Finsupp.single j 1)) hP
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, polyOf, coeff_sum] at hc
  have hX : ∀ f : Fin q → Fin q, (∏ j, X (f j) : MvPolynomial (Fin q) ℂ) =
      monomial (∑ j, Finsupp.single (f j) 1) 1 := fun f => by
    rw [monomial_sum_one]; rfl
  simp only [hX, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero] at hc
  rw [← Finset.sum_filter] at hc
  have hfil : (Finset.univ.filter fun f : Fin q → Fin q =>
      (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1) =
      Finset.univ.map ⟨fun σ : Equiv.Perm (Fin q) => (σ : Fin q → Fin q), DFunLike.coe_injective⟩ := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk,
      nu_iff]
    exact ⟨fun h => ⟨Equiv.ofBijective f h, rfl⟩, fun ⟨σ, hσ⟩ => hσ ▸ σ.bijective⟩
  rw [hfil, Finset.sum_map] at hc
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, Function.Embedding.coeFn_mk] using hc

end Sym

end WeightTwoPolynomials

open WeightTwoPolynomials in
theorem sw2 : PlacePermOperatorCommutantSpan := by
  intro W _ _ m q Z hZ
  by_contra hZS
  obtain ⟨φ, hφZ, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hZS inferInstance
  have hφ : ∀ y ∈ Submodule.span ℂ {M | ∃ d : W → Matrix (Fin m) (Fin m) ℂ,
      (∀ w, d w ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ M = tp q (blk d)}, φ y = 0 := by
    intro y hy
    have : φ y ∈ (Submodule.span ℂ _).map φ := Submodule.mem_map_of_mem hy
    rw [hφS] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) →
      φ (tp q (blk d)) = 0 := fun d hd => hφ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  have hAll := all_of_herm φ (herm_of_unit φ hU)
  apply hφZ
  have hfac : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
  have hdec := congrArg φ (decomp Z (sym_of_comm Z hZ))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, smul_eq_mul, map_sum] at hdec
  have hterm : ∀ I J, φ (Z I J • symU I J) = 0 := by
    intro I J
    rw [map_smul, smul_eq_mul]
    by_cases h : Z I J = 0
    · rw [h, zero_mul]
    · have hc := compat_of_comm Z hZ I J h
      have h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))) = 0 := by
        intro t
        rw [eq_blk (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))]
        · exact hAll _
        · intro x y hxy
          simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg, mul_zero]
          rintro ⟨rfl, rfl⟩
          exact hxy (hc j)
      have hs := sym_zero φ (fun j => Matrix.single (I j) (J j) (1 : ℂ)) h0
      rw [sum_perm_mt _ I J fun _ => rfl] at hs
      rw [hs, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hterm, Finset.sum_const_zero] at hdec
  exact (mul_eq_zero.1 hdec).resolve_left hfac

end PositivityTheory.KB.BlockInvariants

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PlacePermOperatorBicommutantSpan
noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightOneEmbedding

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Ω × Ω) :=
  (Matrix.ofLinearEquiv ℂ).symm ≪≫ₗ (LinearEquiv.curry ℂ ℂ Ω Ω).symm ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Ω × Ω → ℂ)).symm

theorem inner_embE (x y : Matrix Ω Ω ℂ) :
    inner ℂ (embE x) (embE y) = trace (xᴴ * y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [embE, LinearEquiv.trans_apply, dotProduct, trace, diag, Matrix.mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem comm_left (A : Submodule ℂ (Matrix Ω Ω ℂ)) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T)
    (S : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ) (hS : ∀ a ∈ A, ∀ y, S (a * y) = a * S y)
    (y : Matrix Ω Ω ℂ) : S (T * y) = T * S y := by
  have key : ∀ (a : Matrix Ω Ω ℂ) (c j : Ω), a * single c j 1 = ∑ b, a b c • single b j 1 := by
    intro a c j
    ext x z
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, single, of_apply, smul_eq_mul]
    by_cases h : j = z <;> simp [h, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  let Z : Ω → Ω → Matrix Ω Ω ℂ := fun j k => Matrix.of fun x c => S (single c j 1) x k
  have hZr : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (Z j k * a) x c = S (a * single c j 1) x k := by
    intro a j k x c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, map_sum, Matrix.sum_apply]
    simp only [Z, Matrix.mul_apply, of_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZl : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (a * Z j k) x c = (a * S (single c j 1)) x k := by
    intro a j k x c
    simp only [Z, Matrix.mul_apply, of_apply]
  have hZ : ∀ j k, T * Z j k = Z j k * T := fun j k => hT _ fun a ha => by
    ext x c; rw [hZr, hZl, hS a ha]
  have hsingle : ∀ c j, S (T * single c j 1) = T * S (single c j 1) := by
    intro c j
    ext x k
    rw [← hZr, ← hZl, hZ]
  rw [matrix_eq_sum_single y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have : single c j (y c j) = y c j • single c j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [this, mul_smul_comm, map_smul, hsingle, map_smul, mul_smul_comm]

theorem bic (A : Submodule ℂ (Matrix Ω Ω ℂ)) (h1 : (1 : Matrix Ω Ω ℂ) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hstar : ∀ a ∈ A, aᴴ ∈ A) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T) : T ∈ A := by
  let K : Submodule ℂ (EuclideanSpace ℂ (Ω × Ω)) := A.map (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  let P : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ :=
    (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ K.starProjection.toLinearMap ∘ₗ
      (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  have hPe : ∀ y, embE (P y) = K.starProjection (embE y) := fun y => by
    simp [P]
  have P1 : ∀ y, P y ∈ A := by
    intro y
    obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (embE y))
    have : P y = a := by
      apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
      rw [hPe]; exact e.symm
    rw [this]; exact ha
  have P2 : ∀ a ∈ A, P a = a := by
    intro a ha
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.mem_map_of_mem ha)
  have P3 : ∀ a ∈ A, ∀ y, P (a * y) = a * P y := by
    intro a ha y
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (hmul a ha _ (P1 y))
    · intro w hw
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hw
      have h0 := Submodule.starProjection_inner_eq_zero (K := K) (embE y)
        (embE (aᴴ * b)) (Submodule.mem_map_of_mem (hmul _ (hstar a ha) b hb))
      rw [← hPe, ← map_sub, inner_embE] at h0
      change inner ℂ (embE (a * y) - embE (a * P y)) (embE b) = 0
      rw [← map_sub, inner_embE, ← mul_sub, conjTranspose_mul, Matrix.mul_assoc]
      exact h0
  have := comm_left A T hT P P3 1
  rw [P2 1 h1, Matrix.mul_one] at this
  rw [← this]
  exact P1 T

end WeightOneEmbedding

open WeightOneEmbedding

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_mul (σ τ : Equiv.Perm (Fin q)) (w v : Fin q → W) :
    (perm' (m := m) σ w) * perm' τ v = if v = w ∘ σ then perm' (σ * τ) w else 0 := by
  ext I K
  rw [Matrix.mul_apply, Finset.sum_eq_single (I ∘ σ)]
  · simp only [perm', of_apply, Equiv.Perm.coe_mul]
    by_cases hv : v = w ∘ σ
    · subst hv
      rw [if_pos rfl, of_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · simp [hI, Function.comp_assoc]
      · simp [hI]
    · rw [if_neg hv, Matrix.zero_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · have : ¬ ∀ i, ((I ∘ σ) i).1 = v i := fun h => hv (funext fun i => by
          rw [← h i]; exact hI (σ i))
        simp only [this, false_and, if_false, mul_zero]
      · simp [hI]
  · intro J _ hJ
    simp only [perm', of_apply]
    rw [if_neg (fun h => hJ h.2), zero_mul]
  · simp

theorem perm'_star (σ : Equiv.Perm (Fin q)) (w : Fin q → W) :
    (perm' (m := m) σ w)ᴴ = perm' σ⁻¹ (w ∘ σ) := by
  ext I J
  simp only [perm', conjTranspose_apply, of_apply]
  have e : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ ↔ (∀ i, (I i).1 = (w ∘ σ) i) ∧ J = I ∘ ⇑(σ⁻¹) := by
    constructor
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => h1 (σ i), ?_⟩
      funext i; simp
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := h1 (σ⁻¹ i); simpa using this
      · funext i; simp
  by_cases h : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ
  · rw [if_pos h, if_pos (e.1 h), star_one]
  · rw [if_neg h, if_neg (fun h' => h (e.2 h')), star_zero]

theorem one_eq_sum_perm' : (1 : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) = ∑ w, perm' 1 w := by
  ext I J
  rw [Matrix.sum_apply, Finset.sum_eq_single (fun i => (I i).1)]
  · simp only [perm', of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply]
    by_cases h : I = J
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro w _ hw
    simp only [perm', of_apply]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (funext fun i => (h i).symm)
  · simp

theorem sw1 : PlacePermOperatorBicommutantSpan := by
  intro W _ _ m q T hT
  set S := Set.range fun p : Equiv.Perm (Fin q) × (Fin q → W) => (perm' (m := m) p.1 p.2)
  have hgen : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span ℂ S := by
    rintro _ ⟨⟨σ, w⟩, rfl⟩ _ ⟨⟨τ, v⟩, rfl⟩
    dsimp only
    rw [perm'_mul]
    split_ifs
    · exact Submodule.subset_span ⟨(σ * τ, w), rfl⟩
    · exact Submodule.zero_mem _
  refine bic (Submodule.span ℂ S) ?_ ?_ ?_ T ?_
  · rw [one_eq_sum_perm']
    exact Submodule.sum_mem _ fun w _ => Submodule.subset_span ⟨(1, w), rfl⟩
  · intro a ha b hb
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hgen x hx y hy
  · intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨σ, w⟩, rfl⟩ := hx
      dsimp only
      rw [perm'_star]
      exact Submodule.subset_span ⟨(σ⁻¹, w ∘ σ), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [conjTranspose_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ hx
  · intro Z hZ
    exact hT Z fun σ w => hZ _ (Submodule.subset_span ⟨(σ, w), rfl⟩)

end PositivityTheory.KB.BlockInvariants

end
end

namespace PositivityTheory.KB.BlockInvariants

theorem aGood : AGood := TwAG.aGood

theorem swt_all (hE : SEv) (hS : SStokes) : SWt :=
  swt hE hS (fft_of cplx sw1 sw2) aGood wPad weylTwoBlockMatrix wInv wOne wCyc tStab tBlk pStab blockSum_preserves_cone

end PositivityTheory.KB.BlockInvariants
