module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Psdcone
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.psdcone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsClosed (Psd L N) ∧ (∀ c : ℝ, 0 < c → ∀ k ∈ Psd L N, c • k ∈ Psd L N) ∧
    Pos L N ⊆ Psd L N ∧ (ConeExtensionAcyclic.posDual (Psd L N)).Nonempty := by
  intro L _ _ N
  have hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j) := by
    intro w i j
    exact (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))
  have htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace := by
    intro k hk w
    exact Finset.sum_nonneg fun i _ => (hk w).diag_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ,
        {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj} := by
      ext h
      simp only [Psd, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh w x
        exact (hh w).2 x
      · intro hh w
        exact ⟨mat_herm h w, hh w⟩
    rw [hP]
    refine isClosed_iInter fun w => isClosed_iInter fun x => ?_
    refine isClosed_le continuous_const ?_
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hc w i j)).mul continuous_const
  · intro c hc k hk w
    show (mat (c • k) w).PosSemidef
    rw [mat_smul]
    exact (hk w).smul hc.le
  · intro k hk w
    exact (hk w).posSemidef
  · let f : HS L N →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∑ w, ((mat h w).trace).re
        map_add' := by
          intro h k
          simp only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]
          rfl
        map_smul' := by
          intro c h
          simp only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp }
    have hf : Continuous f := by
      show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)
      exact continuous_finsetSum _ fun w _ =>
        Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => hc w i i)
    refine ⟨⟨f, hf⟩, ?_⟩
    intro k hk hk0
    have hw : ∃ w, mat k w ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hk0 (HS_ext fun w => by rw [hne w, mat_zero])
    obtain ⟨w, hw⟩ := hw
    show 0 < ∑ w, ((mat k w).trace).re
    have hpos : 0 < ((mat k w).trace).re := by
      have h1 : 0 ≤ (mat k w).trace := htr k hk w
      have h2 : (mat k w).trace ≠ 0 := fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)
      exact (Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1
    refine lt_of_lt_of_le hpos ?_
    refine Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)
    exact (Complex.le_def.mp (htr k hk v)).1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RynePlace
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem ryne_place (L : Type) [Field L] [NumberField L] (x : 𝓞 L) (hx : x ≠ 0) :
    ∃ w : InfinitePlace L, 1 ≤ w (x : L) := by
  classical
  by_contra hc
  push_neg at hc
  have hprod := InfinitePlace.prod_eq_abs_norm (x : L)
  rw [← Algebra.coe_norm_int] at hprod
  have hn : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  have h1 : (1 : ℝ) ≤ ((|((Algebra.norm ℤ x : ℤ) : ℚ)| : ℚ) : ℝ) := by
    have := Int.one_le_abs hn
    rw [← Int.cast_abs]
    exact_mod_cast this
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have hf : ∀ w : InfinitePlace L, 0 ≤ w (x : L) ^ w.mult := fun w => by positivity
  have hlt : ∀ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := fun w =>
    pow_lt_one₀ (by positivity) (hc w) InfinitePlace.mult_pos.ne'
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => hf w) (fun w _ => (hlt w).le)
  have : ∏ w : InfinitePlace L, w (x : L) ^ w.mult < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]
    calc w0 (x : L) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult
        ≤ w0 (x : L) ^ w0.mult * 1 := mul_le_mul_of_nonneg_left hle (hf w0)
      _ < 1 := by rw [mul_one]; exact hlt w0
  linarith

theorem UpperTheory.V.KT.ryne :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), (Ry L N).Nonempty := by
  intro L _ _ N
  refine ⟨mkHS (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => isHermitian_one), ?_⟩
  intro y hy
  have hterm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  obtain ⟨w, hw⟩ := ryne_place L (y a) ha
  have hw' : ‖embO w (y a)‖ = w ((y a : 𝓞 L) : L) := by
    simp only [embO, RingHom.comp_apply]
    exact InfinitePlace.norm_embedding_eq w _
  simp only [q, qR, mat_mkHS, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, hterm, toR]
  calc (1 : ℝ) ≤ ‖embO w (y a)‖ ^ 2 := by rw [hw']; nlinarith
    _ ≤ ∑ a', ‖embO w (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun a' => ‖embO w (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    _ ≤ ∑ w', ∑ a', ‖embO w' (y a')‖ ^ 2 :=
      Finset.single_le_sum (f := fun w' => ∑ a', ‖embO w' (y a')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ w)
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.good :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), ConeExtensionAcyclic.Good (qc L N) (Psd L N) := by
  intro L _ _ _ N
  obtain ⟨hc, hs, hp, hd⟩ := psdcone L N
  refine ⟨fun h hh => ?_, ?_, hc, hs, ?_, hd⟩
  · rw [poly_qc] at hh
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hh) 1
    refine ⟨Subtype.val ⁻¹' S, hS.preimage Subtype.val_injective.injOn, ?_⟩
    filter_upwards [hev] with k hk y hy
    exact hk y.1 hy
  · rw [poly_qc]; exact ryne L N
  · rw [poly_qc]; exact (rypos L N).trans hp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Detlow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Gramdet
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Blockdet
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.blockdet :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (E : Matrix ι ι ℂ) (A : ι → Matrix (Fin N) (Fin N) ℂ),
    (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2).det =
      (star E.det * E.det) ^ N * ∏ φ, (A φ).det := by
  intro ι _ _ N E A
  have key : (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2) =
      (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E)ᴴ * Matrix.blockDiagonal A *
        Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.blockDiagonal_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.kronecker,
    Matrix.det_kronecker, Matrix.det_blockDiagonal]
  simp [star_pow, mul_pow]
  ring
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

@[to_additive]
private theorem UpperTheory.V.KT.prod_emb (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    {M : Type} [CommMonoid M] (f : (L →+* ℂ) → M) :
    ∏ φ, f φ = ∏ w : InfinitePlace L, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk f]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e.symm)
  rw [← Finset.prod_pair hne]
  congr 1
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rw [← InfinitePlace.mk_embedding w, eq_comm, InfinitePlace.mk_eq_iff] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem UpperTheory.V.KT.det_emb (L : Type) [Field L] [NumberField L] :
    star (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det *
      (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det =
      (absD L : ℂ) := by
  classical
  have hE : (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) =
      ((basisMatrix L).submatrix (equivReindex L).symm (equivReindex L).symm)ᵀ := by
    ext k i
    simp [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rw [hE, det_transpose, det_submatrix_equiv_self]
  have h := congrArg norm (discr_eq_basisMatrix_det_sq L)
  rw [norm_pow, Complex.norm_intCast] at h
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← h, absD, ← Int.cast_abs,
    ← Int.natCast_natAbs]
  rw [Int.cast_natCast, Complex.ofReal_natCast]

theorem UpperTheory.V.KT.gramdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (h : HS L N),
    2 ^ dd L N * (gram h).det = (absD L : ℝ) ^ N * (∏ w, (mat h w).det.re) ^ 2 := by
  intro L _ _ _ N h
  classical
  let A : (L →+* ℂ) → Matrix (Fin N) (Fin N) ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then mat h (InfinitePlace.mk φ)
    else (mat h (InfinitePlace.mk φ))ᵀ
  have hne : ∀ w : InfinitePlace L, ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
    intro w e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e)
  have hA1 : ∀ w : InfinitePlace L, A w.embedding = mat h w := by
    intro w; simp [A, InfinitePlace.mk_embedding]
  have hA2 : ∀ w : InfinitePlace L, A (ComplexEmbedding.conjugate w.embedding) = (mat h w)ᵀ := by
    intro w; simp only [A, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (hne w)]
  have key := UpperTheory.V.KT.blockdet (BI L) N
    (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L))
    (fun k => A ((equivReindex L).symm k))
  rw [UpperTheory.V.KT.det_emb, Equiv.prod_comp (equivReindex L).symm (fun φ => (A φ).det),
    UpperTheory.V.KT.prod_emb L] at key
  have hM : (Matrix.of fun s t : Fin N × BI L => ∑ k,
      star ((Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k s.2) *
        A ((equivReindex L).symm k) s.1 t.1 *
        (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k t.2) =
      Complex.ofRealHom.mapMatrix ((2 : ℝ) • gram h) := by
    ext s t
    simp only [of_apply]
    rw [Equiv.sum_comp (equivReindex L).symm (fun φ => star (φ (RingOfIntegers.basis L s.2 : L)) *
      A φ s.1 t.1 * φ (RingOfIntegers.basis L t.2 : L)), UpperTheory.V.KT.sum_emb L]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA1, hA2, RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, gram, of_apply,
      smul_eq_mul, Finset.mul_sum, map_sum, Complex.ofRealHom_eq_coe]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Complex.add_conj]
    have hh : mat h w t.1 s.1 = star (mat h w s.1 t.1) := ((mat_herm h w).apply t.1 s.1).symm
    simp [embO, hh, ComplexEmbedding.conjugate_coe_eq]
  rw [hM, ← RingHom.map_det, det_smul] at key
  have hc : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  have hd : ∀ w, (mat h w).det = ((mat h w).det.re : ℂ) := by
    intro w
    have : star (mat h w).det = (mat h w).det := by
      rw [← det_conjTranspose, (mat_herm h w).eq]
    exact (Complex.conj_eq_iff_re.mp this).symm
  simp only [hA1, hA2, det_transpose, hc] at key
  rw [Finset.prod_congr rfl fun w _ => by rw [hd w]] at key
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, key, Finset.prod_mul_distrib]
  push_cast
  ring
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.detlow_num (d : ℕ) (hd : d = 0 ∨ 2 ≤ d) (E P g : ℝ) (hE : 1 ≤ E)
    (hP : 0 ≤ P) (h1 : 1 ≤ (4 * (d : ℝ)) ^ d * g) (h2 : 2 ^ d * g = E * P ^ 2) :
    1 ≤ E * (d : ℝ) ^ d * P := by
  have hq : (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d := by
    rcases hd with rfl | hd2
    · simp
    · apply one_le_pow₀
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hprod : 1 ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
    calc (1 : ℝ) ≤ ((d : ℝ) / 2) ^ d * ((4 * (d : ℝ)) ^ d * g) :=
          one_le_mul_of_one_le_of_one_le hq h1
      _ = E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := by
        rw [← mul_assoc, ← mul_pow, show (d : ℝ) / 2 * (4 * d) = 2 * d * d by ring, mul_pow,
          mul_pow, ← h2]
        ring
  have hE0 : 0 ≤ E := by linarith
  have hX : 0 ≤ E * (d : ℝ) ^ d * P := mul_nonneg (mul_nonneg hE0 (by positivity)) hP
  have hsq : 1 ≤ (E * (d : ℝ) ^ d * P) ^ 2 := by
    calc (1 : ℝ) ≤ E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d := hprod
      _ ≤ E * (E * P ^ 2 * (d : ℝ) ^ d * (d : ℝ) ^ d) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hE) (le_trans zero_le_one hprod)]
      _ = (E * (d : ℝ) ^ d * P) ^ 2 := by ring
  nlinarith

theorem UpperTheory.V.KT.detlow :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (h : HS L N), h ∈ Ry L N →
    1 ≤ (I0 L N : ℝ) * ∏ w, (mat h w).det.re := by
  intro L _ _ _ N h hh
  classical
  obtain ⟨hherm, hquad, hreal, hbij⟩ := gramq L N h
  have hint0 : (intVec (0 : Fin N × BI L → ℤ) : KT.Lat L N) = 0 := by
    funext a
    simp [intVec]
  have hpos : ∀ c : Fin N × BI L → ℤ, c ≠ 0 →
      1 ≤ (fun i => (c i : ℝ)) ⬝ᵥ KT.gram h *ᵥ (fun i => (c i : ℝ)) := by
    intro c hc
    rw [hquad, hreal]
    have hne : intVec c ≠ 0 := fun h0 => hc (hbij.1 (h0.trans hint0.symm))
    exact hh (intVec c) hne
  obtain ⟨_, hdet⟩ := grampd (Fin N × BI L) (KT.gram h) hherm hpos
  have hcard : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  rw [hcard] at hdet
  have hgd := gramdet L N h
  have hPpos : 0 ≤ ∏ w, (mat h w).det.re := by
    apply Finset.prod_nonneg
    intro w _
    exact (Complex.pos_iff.1 ((rypos L N hh w).det_pos)).1.le
  have hE : (1 : ℝ) ≤ (absD L : ℝ) ^ N := by
    apply one_le_pow₀
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero L))
  have hd : dd L N = 0 ∨ 2 ≤ dd L N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · left
      simp [dd, hN]
    · right
      have hr := Module.finrank_pos (R := ℚ) (M := L)
      have h2 : 2 ≤ Module.finrank ℚ L := by
        rw [IsTotallyComplex.finrank] at hr ⊢
        omega
      show 2 ≤ Module.finrank ℚ L * N
      nlinarith
  have key := UpperTheory.V.KT.detlow_num (dd L N) hd ((absD L : ℝ) ^ N) (∏ w, (mat h w).det.re)
    (KT.gram h).det hE hPpos hdet hgd
  have e : ((I0 L N : ℕ) : ℝ) = (absD L : ℝ) ^ N * (dd L N : ℝ) ^ (dd L N) := by
    unfold I0
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [e]
  exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.stabfin :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    Finite (MulAction.stabilizer (Gm L N) v) := by
  intro L _ _ _ N v
  classical
  have hpoly : v.1 ∈ Ry L N := by
    rw [← poly_qc]
    exact v.2.1
  obtain ⟨S, hSfin, hev⟩ := locfin L N v.1 (rypos L N hpoly) 1
  have hS : ∀ y, q v.1 y = 1 → y ∈ S := by
    intro y hy
    by_contra hyS
    have := hev.self_of_nhds y hyS
    linarith
  have hspan : Spans (minVec v.1) :=
    spanpsd L N _ (fun k _ hk => v.2.2 k (fun y hy => hk y.1 hy))
  obtain ⟨A, hA, hAcol⟩ := exbasis L N _ hspan
  have hinv : ∀ g ∈ MulAction.stabilizer (Gm L N) v, ∀ y, q v.1 y = 1 → q v.1 (g • y) = 1 := by
    intro g hg y hy
    have hgh : g • v.1 = v.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg)
    have hgh' : g⁻¹ • v.1 = v.1 := inv_smul_eq_iff.2 hgh.symm
    calc q v.1 (g • y) = q v.1 (g⁻¹⁻¹ • y) := by rw [inv_inv]
      _ = q (g⁻¹ • v.1) y := (q_smul g⁻¹ v.1 y).symm
      _ = q v.1 y := by rw [hgh']
      _ = 1 := hy
  haveI : Finite S := hSfin.to_subtype
  let φ : MulAction.stabilizer (Gm L N) v → (Fin N → S) := fun g a =>
    ⟨(g : Gm L N) • (fun i => A i a), hS _ (hinv g.1 g.2 _ (hAcol a))⟩
  refine Finite.of_injective φ ?_
  intro g g' hgg
  have hcol : ∀ a, (g : Gm L N) • (fun i => A i a) = (g' : Gm L N) • (fun i => A i a) :=
    fun a => congrArg Subtype.val (congrFun hgg a)
  have hM : ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A :=
    Matrix.ext fun i a => congrFun (hcol a) i
  have hM2 : A.det • ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) =
      A.det • ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) := by
    have h2 := congrArg (· * A.adjugate) hM
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  exact Subtype.ext (Units.ext (smul_right_injective _ hA hM2))
end
