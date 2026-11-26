module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_eq_sum_set {S : Type} [AddCommMonoid S] (s : Set ι) [Fintype s] (f : ι → S)
    (h : ∀ m, m ∉ s → f m = 0) : ∑ m, f m = ∑ m : s, f m := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ s)) (by simp) f]
  exact (Finset.sum_filter_of_ne fun m _ hm => by_contra fun hs => hm (h m hs)).symm

theorem blk_mul {S : Type} [CommRing S] (s : Set ι) [Fintype s] (x y : Matrix ι ι S)
    (hy : ∀ r, r ∉ s → ∀ c ∈ s, y r c = 0) :
    (x * y).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      x.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) *
        y.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact sum_eq_sum_set s _ fun m hm => by rw [hy m hm c c.2, mul_zero]

open Classical in
theorem det_blk_mul (s : Set ι) (p : GL ι R) {q : GL ι R} (hq : q ∈ stab R s) :
    (((p * q : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
        ((q : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [Units.val_mul, blk_mul s _ _ fun r hr c hc => (hq r hr c hc).1, Matrix.det_mul]

open Classical in
theorem det_blk_mul_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
      (((p⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det = 1 := by
  rw [← det_blk_mul s p (inv_mem hp), mul_inv_cancel, Units.val_one,
    Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

open Classical in
theorem isUnit_det_blk (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    IsUnit ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det :=
  IsUnit.of_mul_eq_one _ (det_blk_mul_inv s hp)

open Classical in
theorem bdet_val (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((bdet s p : Rˣ) : R) = ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [bdet, dite_eq_left (isUnit_det_blk s hp), IsUnit.unit_spec]

theorem bdet_mul (s : Set ι) {p q : GL ι R} (hp : p ∈ stab R s) (hq : q ∈ stab R s) :
    bdet s (p * q) = bdet s p * bdet s q := by
  classical
  apply Units.ext
  rw [Units.val_mul, bdet_val s (mul_mem hp hq), bdet_val s hp, bdet_val s hq]
  exact det_blk_mul s p hq

theorem bdet_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) : (bdet s p)⁻¹ = bdet s p⁻¹ := by
  classical
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  apply Units.ext
  rw [Units.val_mul, bdet_val s hp, bdet_val s (inv_mem hp), Units.val_one]
  exact det_blk_mul_inv s hp

theorem bdet_univ (g : GL ι R) : bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g := by
  classical
  have hs : g ∈ stab R (Set.univ : Set ι) := fun r hr => absurd (Set.mem_univ r) hr
  apply Units.ext
  rw [bdet_val _ hs]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  convert Matrix.det_submatrix_equiv_self (Equiv.Set.univ ι) (g : Matrix ι ι R)
  all_goals (funext x; rfl)

section Top

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isClosed_stab [T2Space R] (s : Set ι) : IsClosed (stab R s : Set (GL ι R)) := by
  have e : (stab R s : Set (GL ι R)) = ⋂ (r : ι) (_ : r ∉ s) (c : ι) (_ : c ∈ s),
      ({g : GL ι R | (g : Matrix ι ι R) r c = 0} ∩
        {g : GL ι R | ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun c =>
    isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_eq (Units.continuous_val.matrix_elem r c) continuous_const
  · exact isClosed_eq ((Units.continuous_val.comp continuous_inv).matrix_elem r c) continuous_const

theorem continuousOn_bdet (s : Set ι) :
    ContinuousOn (bdet s) (stab R s : Set (GL ι R)) := by
  classical
  have hm (p : (stab R s : Set (GL ι R))) : (p : GL ι R) ∈ stab R s := p.2
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  constructor
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      (((p : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => (bdet_val s (hm p)).symm
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      ((((p : GL ι R)⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      (((Units.continuous_val.comp continuous_inv).comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => ?_
    show _ = (((bdet s (p : GL ι R))⁻¹ : Rˣ) : R)
    rw [bdet_inv s (hm p), bdet_val s (inv_mem (hm p))]

end Top

section Places

variable {E : Type} [Field E]


open Classical in
theorem bdet_rat (A : Ad E R) (hi : Function.Injective A.i) (s : Set ι) {p : GL ι R}
    (hp : p ∈ stab R s) (hr : p ∈ A.ratGL ι) : ∃ x, bdet s p = Units.map A.i.toMonoidHom x := by
  classical
  obtain ⟨g, rfl⟩ := hr
  set d : E := ((g : Matrix ι ι E).submatrix (Subtype.val : s → ι) Subtype.val).det with hd
  have hval : ((bdet s (Matrix.GeneralLinearGroup.map A.i g) : Rˣ) : R) = A.i d := by
    rw [bdet_val s hp, hd, RingHom.map_det]
    congr 1
  have hd0 : d ≠ 0 := by
    intro h0
    have hu := (bdet s (Matrix.GeneralLinearGroup.map A.i g)).isUnit
    rw [hval, h0, map_zero] at hu
    have h10 : (0 : R) = 1 := by
      have := isUnit_zero_iff.1 hu
      exact this
    exact zero_ne_one (hi (by rw [map_zero, map_one, h10]) : (0 : E) = 1)
  refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
  rw [hval]
  rfl


open Classical in
theorem norm_det_blk (M : Matrix ι ι ℂ) (hM : M ∈ Matrix.unitaryGroup ι ℂ) (s : Set ι)
    (h0 : ∀ r, r ∉ s → ∀ c ∈ s, M r c = 0) :
    ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ = 1 := by
  have h1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hM
  have h2 : ((star M * M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det = 1 := by
    rw [h1, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
  rw [blk_mul s _ _ h0, Matrix.det_mul, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_submatrix,
    Matrix.det_conjTranspose] at h2
  have h3 : ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ^ 2 = 1 := by
    have := congrArg norm h2
    rw [norm_mul, norm_star, norm_one] at this
    rw [sq]; exact this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem det_mem_subring {κ : Type} [Fintype κ] [DecidableEq κ] (O : Subring R) (m : Matrix κ κ R)
    (h : ∀ r c, m r c ∈ O) : m.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem lg_eq_zero (A : Ad E R) (hA : A.GoodL) (u : Rˣ) (h1 : (u : R) ∈ A.O)
    (h2 : ((u⁻¹ : Rˣ) : R) ∈ A.O) (hw : ∀ w, ‖A.φ w (u : R)‖ = 1) : A.lg u = 0 := by
  let j : Rˣ →* GL Unit R := Units.map (Matrix.scalar Unit : R →+* Matrix Unit Unit R).toMonoidHom
  have hj : j u ∈ A.kGL Unit := by
    refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
    · simpa [j] using h1
    · have : ((j u)⁻¹ : GL Unit R) = j u⁻¹ := (map_inv j u).symm
      rw [this]
      simpa [j] using h2
    · rw [Matrix.mem_unitaryGroup_iff]
      ext r c
      simp [j, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw w]
  have hdet : Continuous fun g : GL Unit R => (Matrix.GeneralLinearGroup.det g : Rˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact Units.continuous_val.matrix_det
    · have : (fun g : GL Unit R => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R)) =
          fun g => ((g⁻¹ : GL Unit R) : Matrix Unit Unit R).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [this]
      exact (Units.continuous_val.comp continuous_inv).matrix_det
  have hc : Continuous fun g : GL Unit R => A.lg (Matrix.GeneralLinearGroup.det g) :=
    hA.lgcont.comp hdet
  obtain ⟨C, hC⟩ := (hA.kcpt Unit).exists_bound_of_continuousOn hc.continuousOn
  have hone : A.lg 1 = 0 := by
    have := hA.lgmul 1 1
    rw [mul_one] at this
    linarith
  have hpow : ∀ n : ℕ, A.lg (u ^ n) = n * A.lg u := by
    intro n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hA.lgmul, ih]; push_cast; ring
  have hdj : Matrix.GeneralLinearGroup.det (j u) = u := by
    apply Units.ext
    simp [j, Matrix.GeneralLinearGroup.val_det_apply]
  have hb : ∀ n : ℕ, (n : ℝ) * |A.lg u| ≤ C := by
    intro n
    have := hC (j u ^ n) (pow_mem hj n)
    rw [map_pow, hdj, hpow, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
    exact this
  by_contra hne
  have hpos : 0 < |A.lg u| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |A.lg u|)
  have := hb n
  rw [div_lt_iff₀ hpos] at hn
  linarith


open Classical in
theorem lg_bdet (A : Ad E R) (hA : A.GoodL) (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s)
    (hk : p ∈ A.kGL ι) : A.lg (bdet s p) = 0 := by
  classical
  refine lg_eq_zero A hA _ ?_ ?_ fun w => ?_
  · rw [bdet_val s hp]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).1
  · rw [bdet_inv s hp, bdet_val s (inv_mem hp)]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).2
  · rw [bdet_val s hp, RingHom.map_det]
    refine (congrArg norm (congrArg Matrix.det ?_)).trans
      (norm_det_blk _ (hk.2 w) s fun r hr c hc => ?_)
    · ext r c; rfl
    · simp [(hp r hr c hc).1]

end Places

theorem bdetLaw : BdetLaw := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ s
  exact ⟨isClosed_stab s, fun p hp q hq => bdet_mul s hp hq, continuousOn_bdet s,
    fun p hp hr => bdet_rat A hA.iinj s hp hr, fun p hp hk => lg_bdet A hA s hp hk, bdet_univ⟩

end GlobalTheory.CompanionTheory.RgEis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLawStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_determinant_law : PositivityTheory.RgEis.BdetLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.bdetLaw | exact GlobalTheory.CompanionTheory.RgEis.bdetLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.bdetLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CancelLTensor
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovComp

theorem cancel_lTensor (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (w : B₁ ⊗[B] (B ⊗[A] K₁)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀ ((d.baseChange B).lTensor B₁ w) =
      d.lTensor B₁ (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁ w) := by
  induction w with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t =>
    induction t with
    | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, hx, hy]
    | tmul c k => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul']

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := by
  intro p _ A _ B _ _ B₁ _ _ _ _ r hA hB hr h1 h2
  unfold Cov at h1 h2 ⊢
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  have e1 : Pf p (B ⊗[A] K₁) := PerfectRing.pf_tensor p A B K₁ hA hB hK₁
  have e0 : Pf p (B ⊗[A] K₀) := PerfectRing.pf_tensor p A B K₀ hA hB hK₀
  have e2 : Good p (fun k => algebraMap A B (r k)) (d.baseChange B) :=
    GoodBaseChange.good_baseChange p A B r K₁ K₀ d hd
  have hz' : (1 : B₁) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] z) ∈ (LinearMap.lTensor B₁ (d.baseChange B)).range := by
    obtain ⟨w, hw⟩ := hz
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁).symm w, ?_⟩
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀).injective
    rw [cancel_lTensor, LinearEquiv.apply_symm_apply, hw]
    simp
  have hB' := h2 _ _ e1 e0 (d.baseChange B) e2 _ hz' (k + 1)
  have h3 : (1 : B) ⊗ₜ[A] (r (k + 1) • z) ∈ (LinearMap.lTensor B d).range := by
    obtain ⟨v, hv⟩ := hB'
    refine ⟨v, ?_⟩
    change (d.baseChange B) v = _
    rw [hv, algebraMap_smul, ← TensorProduct.tmul_smul]
  have h4 := h1 K₁ K₀ hK₁ hK₀ d hd (r (k + 1) • z) h3 (k + 1)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    rw [← hr k, ← sq, ← pow_add, Nat.sub_add_cancel hp]
  rw [hrk, mul_smul, mul_smul]
  exact Submodule.smul_mem _ _ h4

end GlobalTheory.CompanionTheory.CovComp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRetraction
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovRoot

theorem exists_retraction {A : Type} [CommRing A] (P : Polynomial A) (hP : P.Monic)
    (hd : 0 < P.natDegree) : ∃ ρ : AdjoinRoot P →ₗ[A] A, ρ 1 = 1 := by
  let b := AdjoinRoot.powerBasis' hP
  have h0 : 0 < b.dim := by simpa [b] using hd
  refine ⟨b.basis.coord ⟨0, h0⟩, ?_⟩
  have h1 : b.basis ⟨0, h0⟩ = 1 := by simp
  change b.basis.repr 1 ⟨0, h0⟩ = 1
  rw [← h1, b.basis.repr_self]
  simp

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A)
    (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ x : B, Polynomial.aeval x P = 0 := by
  intro p _ A _ r P hA hP hd
  have hpS : (p : AdjoinRoot P) = 0 := by
    have := congrArg (algebraMap A (AdjoinRoot P)) hA.char
    simpa using this
  obtain ⟨T, _, i, hq⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (AdjoinRoot P) ⊥ hpS
  letI : Algebra A T := (i.comp (algebraMap A (AdjoinRoot P))).toAlgebra
  let i' : AdjoinRoot P →ₐ[A] T := { i with commutes' := fun _ => rfl }
  have hq' : PQ p (i' : AdjoinRoot P →+* T) ⊥ := hq
  refine ⟨T, inferInstance, inferInstance, hq.pf, ?_, i' (AdjoinRoot.root P), ?_⟩
  · refine GlobalTheory.CompanionTheory.CovCmp.cov_of_solv p A T r fun m n a c hs => ?_
    refine ⟨A, inferInstance, inferInstance, GlobalTheory.CompanionTheory.CovMono.cov_self p A r, ?_⟩
    obtain ⟨k, s, hs'⟩ := GlobalTheory.T.frobenius_power_solution_lift p A (AdjoinRoot P) T i' ⊥ m n a c hA.char hq' hs
    refine GlobalTheory.T.perfect_frobenius_root_solution p A A m n k a c hA ?_
    obtain ⟨ρ, hρ⟩ := exists_retraction P hP hd
    have hρa : ∀ x : A, ρ (algebraMap A (AdjoinRoot P) x) = x := fun x => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]
    refine ⟨fun j => ρ (s j), fun t => ?_⟩
    have h := sub_eq_zero.mp ((Ideal.mem_bot).mp (hs' t))
    have h2 := congrArg ρ h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hρa] at h2
    simpa using h2
  · rw [Polynomial.aeval_algHom_apply]
    have : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
      simp [AdjoinRoot.aeval_eq]
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.CovRoot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPowSmulTopIff
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Completion

theorem mem_pow_smul_top_iff {T : Type} [CommRing T] (t y : T) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule T T) ↔ y ∈ Ideal.span {t ^ n} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem aic_of_isCompl : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := by
  intro B _ T _ π g hc hπ hA hV P hP hd
  have step := GlobalTheory.T.hensel_polynomial_refinement B T π g hc hπ hA hV P hP hd
  set d := P.natDegree with hdd
  set t := g π with ht

  let S : ℕ → Type := fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}
  have s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)} := by simp
  let seq : (M : ℕ) → S M := fun M =>
    Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M
  have hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M} := fun M =>
    (step M (seq M).1 (seq M).2).choose_spec.1
  let a : ℕ → T := fun M => g (seq M).1
  have hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M} := by
    intro M
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (hstep M)
    refine Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩
    simp only [a, ht, ← map_pow, ← map_mul, hc', map_sub]
  have hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} := by
    intro m n hmn
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn
  have hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := Ideal.add_mem _ ih (hpow hmn (hg n))
      simpa using this
  have hpre := hc.compl.toIsPrecomplete
  obtain ⟨x, hx⟩ := hpre.prec' a (fun {m n} hmn => by
    rw [SModEq.sub_mem, mem_pow_smul_top_iff]
    have := Ideal.neg_mem_iff _ |>.2 (hcau hmn)
    simpa using this)
  refine ⟨x, ?_⟩
  have hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n} := by
    intro n
    have h1 : a n - x ∈ Ideal.span {t ^ n} := by
      have := hx n
      rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    have h2 : P.eval (a n) ∈ Ideal.span {t ^ n} :=
      hpow (Nat.le_mul_of_pos_left n hd) (seq n).2
    have h3 : a n - x ∣ P.eval (a n) - P.eval x := Polynomial.sub_dvd_eval_sub _ _ _
    have h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n} := Ideal.mem_of_dvd _ h3 h1
    have := Ideal.sub_mem _ h2 h4
    simpa using this
  have := hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by
    rw [SModEq.zero, mem_pow_smul_top_iff]
    exact hz n)
  exact this

end GlobalTheory.CompanionTheory.Completion
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisExt

variable {G : Type} [Group G]

theorem ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by
  have hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [PositivityTheory.RgEis.ext, dite_eq_left hex]
  have hcP : p * k * (hex.choose : G)⁻¹ ∈ P := hex.choose_spec
  have hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) hcP
  have hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K := by
    have he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹ := by group
    rw [he]
    exact K.mul_mem hk (K.inv_mem hex.choose.2)
  have h0 := hfK _ hq hqK
  have hsplit := hadd p hp _ hq
  rw [mul_inv_cancel_left] at hsplit
  rw [hsplit, h0, add_zero]

theorem extLaw : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK

end GlobalTheory.CompanionTheory.RgEisExt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLawStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_law : PositivityTheory.RgEis.ExtLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisExt.extLaw | exact GlobalTheory.CompanionTheory.RgEisExt.extLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisExt.extLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
open Matrix Topology

namespace GlobalTheory.CompanionTheory.RgEisTop

section Units

variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]

theorem isClosedEmbedding_embedProduct : IsClosedEmbedding (Units.embedProduct M) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hr : Set.range (Units.embedProduct M) =
      {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} ∩
        {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, hu⟩
      have h1 : (u : M) = x := congrArg Prod.fst hu
      have h2 : MulOpposite.op ((u⁻¹ : Mˣ) : M) = y := congrArg Prod.snd hu
      subst h1 h2
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, MulOpposite.unop y, h1, h2⟩, rfl⟩
  rw [hr]
  have hu : Continuous fun p : M × Mᵐᵒᵖ => MulOpposite.unop p.2 :=
    MulOpposite.continuous_unop.comp continuous_snd
  exact (isClosed_eq (continuous_fst.mul hu) continuous_const).inter
    (isClosed_eq (hu.mul continuous_fst) continuous_const)

end Units

section Mat

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem generalLinear_t2Space [T2Space R] : T2Space (GL ι R) :=
  (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.t2Space

theorem gl_locallyCompact [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL ι R) := by
  have : LocallyCompactSpace (Matrix ι ι R) := inferInstanceAs (LocallyCompactSpace (ι → ι → R))
  have : LocallyCompactSpace (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isClosedEmbedding.locallyCompactSpace
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).locallyCompactSpace

theorem gl_secondCountable [T2Space R] [SecondCountableTopology R] :
    SecondCountableTopology (GL ι R) := by
  have : SecondCountableTopology (Matrix ι ι R) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → R))
  have : SecondCountableTopology (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isEmbedding.secondCountableTopology
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.secondCountableTopology

end Mat

open PositivityTheory.RgEis

theorem isClosed_uSub {E R : Type} [Field E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Ad E R) (hσ : Continuous A.σ) (ε : ℤˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsClosed (A.uSub ε ι : Set (GL (ι ⊕ ι) R)) := by
  have hv : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ :=
    hv.matrix_map hσ
  exact isClosed_eq ((hv.matrix_transpose.mul continuous_const).mul hm) continuous_const

theorem grpTop : PositivityTheory.RgEis.GrpTop := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ ε
  have hc := isClosed_uSub A hA.σcont ε ι
  have hce : IsClosedEmbedding (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) :=
    hc.isClosedEmbedding_subtypeVal
  have := generalLinear_t2Space R (ι ⊕ ι)
  have := gl_locallyCompact R (ι ⊕ ι)
  have := gl_secondCountable R (ι ⊕ ι)
  refine ⟨generalLinear_t2Space R ι, gl_locallyCompact R ι, gl_secondCountable R ι, hce.isEmbedding.t2Space,
    hce.locallyCompactSpace, hce.isEmbedding.secondCountableTopology, ?_⟩
  exact hce.isCompact_preimage (hA.toGoodL.kcpt (ι ⊕ ι))

end GlobalTheory.CompanionTheory.RgEisTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroupStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_topological_group : PositivityTheory.RgEis.GrpTop := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop | exact GlobalTheory.CompanionTheory.RgEisTop.grpTop | (intros; apply GlobalTheory.CompanionTheory.RgEisTop.grpTop <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPunitEqZero
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiExact

theorem pf_punit (p : ℕ) : Pf p PUnit :=
  ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨b, Subsingleton.elim _ _⟩⟩⟩

theorem tensor_punit_eq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    (w : C ⊗[A] PUnit) : w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => rfl
  | tmul c u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem almost_injective {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K₀ : Type) [CommRing K₀] [Algebra A K₀] (hK : Pf p K₀)
    (z : K₀) (hz : (1 : B) ⊗ₜ[A] z = 0) (k : ℕ) : r k • z = 0 := by
  have good : Good p r (0 : PUnit →ₗ[A] K₀) := by
    intro C _ _ _ w _ k
    exact ⟨0, (tensor_punit_eq_zero _).trans (tensor_punit_eq_zero _).symm⟩
  have h := hCov PUnit K₀ (pf_punit p) hK 0 good z
    ⟨0, by rw [map_zero, hz]⟩ k
  simpa using h

theorem ker_zero {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n)) (h0 : ∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z)
    (z : K 0) (hz : d 0 z = 0) (k : ℕ) : r k • z = 0 :=
  almost_injective hCov (K 0) (hK 0) z (by rw [← h0, hz, map_zero]) k

theorem exact_of_good {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n))
    (hS : ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z)
    (n : ℕ) (hG : Good p r (d n)) (z : K (n + 1)) (hz : d (n + 1) z = 0) (k : ℕ) :
    r k • z ∈ LinearMap.range (d n) :=
  hCov (K n) (K (n + 1)) (hK n) (hK (n + 1)) (d n) hG z
    ⟨H n z, by simpa [hz] using hS n z⟩ k

theorem lTensor_sq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    {K : ℕ → Type} [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (dd : ∀ n z, d (n + 1) (d n z) = 0)
    (n : ℕ) (z : C ⊗[A] K n) : (d (n + 1)).lTensor C ((d n).lTensor C z) = 0 := by
  have h : d (n + 1) ∘ₗ d n = 0 := LinearMap.ext (dd n)
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

theorem exact_succ {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {B : Type} [CommRing B]
    [Algebra A B] {r : ℕ → A} (hA : Pf p A) (hCov : Cov p r B) (n : ℕ) :
    ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
      (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n),
      (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) →
      ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧
        ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) →
      ∀ z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  induction n with
  | zero =>
    intro K _ _ d H hK _ hH
    refine exact_of_good hCov K d H hK hH.2 0 ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', _⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    have hz : r k • w = 0 :=
      ker_zero hCov (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
        (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n)) h0' w hw k
    rw [hz]
    exact zero_mem _
  | succ n ih =>
    intro K _ _ d H hK dd hH
    refine exact_of_good hCov K d H hK hH.2 (n + 1) ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', hS'⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    obtain ⟨v, hv⟩ := ih (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
      (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n))
      (fun n z => lTensor_sq_zero d dd n z) ⟨h0', hS'⟩ w hw k
    refine ⟨((d n).codRestrict (LinearMap.ker (d (n + 1))) (fun z => dd n z)).lTensor C v, ?_⟩
    rw [← hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl

theorem exact_of_contraction :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  intro p _ A _ B _ _ r hA hCov K _ _ d H hK dd hH
  exact ⟨fun z hz k => ker_zero hCov K d H hK hH.1 z hz k,
    fun n z hz k => exact_succ hA hCov n K d H hK dd hH z hz k⟩

end GlobalTheory.CompanionTheory.Dblock.AmiExact
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKill
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BigStep

def gens {A : Type} [CommRing A] (𝓔 : Set (Set (MvPolynomial (Fin 3) A))) :
    Set (MvPolynomial (𝓔 × Fin 3) A) :=
  {f | ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
    f = MvPolynomial.rename (fun t => (E, t)) q}

theorem exists_kill (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A)
    {𝓔 : Set (Set (MvPolynomial (Fin 3) A))}
    (hfin : ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 →
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
        ∀ E ∈ J, Pt (algebraMap A B) E)
    (F : Finset (MvPolynomial (𝓔 × Fin 3) A)) (hF : (F : Set _) ⊆ gens 𝓔) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ τ : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B, ∀ g ∈ F, τ g = 0 := by
  classical
  have hg : ∀ g : {g // g ∈ F}, ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
      g.1 = MvPolynomial.rename (fun t => (E, t)) q := fun g => hF g.2
  choose Eg qg hq hgq using hg
  obtain ⟨B₁, i1, i2, hP, hC, hpt⟩ := hfin (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact (Eg g).2)
  have hpt' : ∀ E : 𝓔, ∃ y : Fin 3 → B₁, E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1) →
      ∀ q ∈ E.1, MvPolynomial.eval₂ (algebraMap A B₁) y q = 0 := by
    intro E
    by_cases h : E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    · obtain ⟨y, hy⟩ := hpt _ h
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hpt'
  refine ⟨B₁, i1, i2, hP, hC, MvPolynomial.aeval (fun v => y v.1 v.2), ?_⟩
  intro g hg
  have e := hgq ⟨g, hg⟩
  simp only at e
  rw [e, MvPolynomial.aeval_rename, MvPolynomial.aeval_def]
  exact hy _ ⟨⟨g, hg⟩, rfl⟩ _ (hq ⟨g, hg⟩)

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := by
  classical
  intro p _ A _ r 𝓔 hA hfin
  have hpS : (p : MvPolynomial (𝓔 × Fin 3) A) = 0 := by
    have := congrArg (algebraMap A (MvPolynomial (𝓔 × Fin 3) A)) hA.char
    simpa using this
  obtain ⟨B, instB, i, hQ⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (MvPolynomial (𝓔 × Fin 3) A)
    (Ideal.span (gens 𝓔)) hpS
  letI instAB : Algebra A B := (i.comp MvPolynomial.C).toAlgebra
  let iA : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B := { i with commutes' := fun _ => rfl }
  refine ⟨B, instB, instAB, hQ.pf, ?_, ?_, ?_⟩
  · apply GlobalTheory.CompanionTheory.CovCmp.cov_of_solv
    intro m n a c hS
    obtain ⟨k, s, hs⟩ := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow p A (MvPolynomial (𝓔 × Fin 3) A) B iA
      (Ideal.span (gens 𝓔)) m n a c hA.char hQ hS
    have hT := fun t => Submodule.mem_span_finite_of_mem_span (hs t)
    choose G hGs hGm using hT
    obtain ⟨B₁, i1, i2, hP, hC, τ, hτ⟩ := exists_kill p r hfin (Finset.univ.biUnion G) (by
      intro g hg
      obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hg)
      exact hGs t ht)
    refine ⟨B₁, i1, i2, hC,
      GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow p A B₁ m n k a c hP ⟨fun j => τ (s j), fun t => ?_⟩⟩
    have hle : Ideal.span (G t : Set (MvPolynomial (𝓔 × Fin 3) A)) ≤ RingHom.ker τ :=
      Ideal.span_le.2 fun g hg =>
        hτ g (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, Finset.mem_coe.1 hg⟩)
    have h0 := hle (hGm t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sum, AlgHom.commutes, sub_eq_zero] at h0
    simpa only [map_smul] using h0
  · intro E hE
    refine ⟨fun t => i (MvPolynomial.X ((⟨E, hE⟩ : 𝓔), t)), fun q hq => ?_⟩
    have hz : i (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 :=
      (hQ.ker _).2 ⟨0, by
        have h : MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q ∈ Ideal.span (gens 𝓔) :=
          Ideal.subset_span ⟨⟨E, hE⟩, q, hq, rfl⟩
        simpa using h⟩
    have hi : i = MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v)) :=
      MvPolynomial.ringHom_ext (by simp) (by simp)
    have hz' : MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v))
        (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 := by
      rw [← hi]; exact hz
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename] at hz'
    exact hz'
  · intro T _ x hT hpts
    have hpts' : ∀ E : 𝓔, ∃ y : Fin 3 → T, ∀ q ∈ E.1, MvPolynomial.eval₂ x y q = 0 :=
      fun E => hpts E.1 E.2
    choose y hy using hpts'
    have hle : Ideal.span (gens 𝓔) ≤
        RingHom.ker (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨E, q, hq, rfl⟩
      show MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2) _ = 0
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
      exact hy E q hq
    obtain ⟨ψ, hψ, -⟩ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift p _ B T i _
      (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) hQ hT (fun g hg => hle hg)
    refine ⟨ψ, RingHom.ext fun a => ?_⟩
    have := RingHom.congr_fun hψ (MvPolynomial.C a)
    show ψ (i (MvPolynomial.C a)) = x a
    simpa using this

end GlobalTheory.CompanionTheory.BigStep
end
