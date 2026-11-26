module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransform

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumns
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Classical Kronecker

namespace GlobalTheory.ColumnSymplectic

variable {n g : ℕ}

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) :
    blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  change (if p.1 = q.1 then τ p.2 q.2 else 0) =
    (1 : Matrix (Fin n) (Fin n) ℂ) p.1 q.1 * τ p.2 q.2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem blk_mul (A B : Matrix (Fin g) (Fin g) ℂ) : blk n A * blk n B = blk n (A * B) := by
  rw [blk_eq, blk_eq, blk_eq, ← mul_kronecker_mul, one_mul]

theorem blk_one : blk n (1 : Matrix (Fin g) (Fin g) ℂ) = 1 := by
  rw [blk_eq, one_kronecker_one]

theorem blk_mulVec (A : Matrix (Fin g) (Fin g) ℂ) (w : Fin n × Fin g → ℂ) :
    blk n A *ᵥ w = fun p => (A *ᵥ fun i => w (p.1, i)) p.2 := by
  funext p
  simp only [mulVec, dotProduct, blk, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem blk_mem_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · show (blk n τ)ᵀ = blk n τ
    ext p q
    simp only [transpose_apply, blk, of_apply]
    by_cases e : p.1 = q.1
    · rw [if_pos e.symm, if_pos e]
      exact congrFun (congrFun h.1 p.2) q.2
    · rw [if_neg (Ne.symm e), if_neg e]
  · have e : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ τ.map Complex.im := by
      ext p q
      change Complex.im (if p.1 = q.1 then τ p.2 q.2 else 0) =
        (1 : Matrix (Fin n) (Fin n) ℝ) p.1 q.1 * Complex.im (τ p.2 q.2)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [e]
    exact PosDef.one.kronecker h.2

private theorem sum_herm_eq_trace_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G (y k) (y' k) = (y * G * ccT y').trace := by
  simp only [herm, trace, diag, Matrix.mul_apply, ccT, transpose_apply, map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem sum_herm_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (G : Matrix (Fin r) (Fin r) E)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G ((h * y) k) ((h * y') k) = ∑ k, herm G (y k) (y' k) := by
  rw [sum_herm_eq_trace_mul_ccT, sum_herm_eq_trace_mul_ccT, Base.ccT_mul]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, hu, Matrix.mul_one]

theorem sum_EF_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X ((h * y) k) ((h * y') k) = ∑ k, EF X (y k) (y' k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [EF_def, ← map_sum, ← Finset.mul_sum]
  rw [sum_herm_mul hu]

private theorem crd_dotProduct_sub_eq_neg_sum_EF (hs : IsSympl X bas) (Z Z' : Matrix (Fin n) (Fin r) E) :
    (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inl p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inr p.2)) -
      (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inr p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inl p.2)) =
      -∑ k, EF X (Z k) (Z' k) := by
  simp only [EF_crd hs, dotProduct, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_neg,
    ← Finset.sum_sub_distrib]


variable (bas) in
noncomputable def famOf (u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) : Matrix (Fin n) (Fin r) E :=
  Matrix.of fun k => vecQ X bas (Sum.elim (fun i => u.1 (k, i)) fun i => u.2 (k, i))

noncomputable def colMap (hs : IsSympl X bas) (h : Matrix (Fin n) (Fin n) E) :
    ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) →ₗ[ℚ] ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) where
  toFun u := (fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inl p.2),
    fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inr p.2))
  map_add' u v := by
    have : famOf bas (u + v) = famOf bas u + famOf bas v := by
      refine funext fun k => ?_
      change vecQ X bas _ = vecQ X bas _ + vecQ X bas _
      rw [← vecQ_add]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (u + v)) k = (h * famOf bas u) k + (h * famOf bas v) k := fun k => by
      rw [this, Matrix.mul_add]; rfl
    simp only [e, crd_add hs]
    rfl
  map_smul' q u := by
    have : famOf bas (q • u) = q • famOf bas u := by
      refine funext fun k => ?_
      change vecQ X bas _ = q • vecQ X bas _
      rw [← vecQ_smul]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (q • u)) k = q • (h * famOf bas u) k := fun k => by
      rw [this, Matrix.mul_smul]; rfl
    simp only [e, crd_smul hs]
    rfl

theorem colMap_form (hs : IsSympl X bas) {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (u v : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) :
    (colMap hs h u).1 ⬝ᵥ (colMap hs h v).2 - (colMap hs h u).2 ⬝ᵥ (colMap hs h v).1 =
      u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 := by
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  have e1 := crd_dotProduct_sub_eq_neg_sum_EF hs (h * famOf bas u) (h * famOf bas v)
  have e2 := crd_dotProduct_sub_eq_neg_sum_EF hs (famOf bas u) (famOf bas v)
  rw [sum_EF_mul hu, ← e2] at e1
  simp only [hcrd, Sum.elim_inl, Sum.elim_inr] at e1
  exact e1

noncomputable def actM (h : Matrix (Fin n) (Fin n) E) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  blockDiagonal fun i => (rowType X (idx i)).mapMatrix h

theorem actM_mulVec (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    (actM idx h *ᵥ fun p => z p.1 p.2) = fun p => Dict.hAct X idx h z p.1 p.2 := by
  funext p
  simp only [actM, Dict.hAct, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, RingHom.mapMatrix_apply, map_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_actM (h : Matrix (Fin n) (Fin n) E) :
    (actM idx h).det = ∏ i, rowType X (idx i) h.det := by
  rw [actM, det_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ => (RingHom.map_det _ _).symm

theorem per_mul (x : Frame X.Ψ r) (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E)
    (k : Fin n) : per X x ((h * y) k) ∘ idx = Dict.hAct X idx h (fun k => per X x (y k) ∘ idx) k := by
  have e : (h * y) k = ∑ k', h k k' • y k' := by
    ext a
    simp [Matrix.mul_apply, Finset.sum_apply]
  funext i
  rw [e, per_sum]
  simp only [Function.comp_apply, Finset.sum_apply, per_smul, Dict.hAct]

theorem conj_mulVec (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    ((blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) =
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  have hH : (hMat X bas idx x)⁻¹ * hMat X bas idx x = 1 :=
    nonsing_inv_mul _ (isUnit_det_hMat (idx := idx) hs hx)
  have e3 : (blk n (hMat X bas idx x)⁻¹ *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = fun p => z p.1 p.2 := by
    rw [blk_mulVec]
    funext p
    simp only [mulVec_mulVec, hH, one_mulVec]
  rw [← mulVec_mulVec, e3, ← mulVec_mulVec, actM_mulVec, blk_mulVec]

theorem exists_symplectic_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  intro E _ _ _ r X g bas idx n hs _ h hu
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  obtain ⟨s, hsS, hact⟩ := GlobalTheory.SymplecticPeriods.exists_symplectic_action (Fin n × Fin g)
    (colMap hs h) (colMap_form hs hu)
  refine ⟨s, hsS, fun x hx => ?_⟩
  have hT : tauMat X bas idx x ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩
  have hB := blk_mem_siegel (n := n) hT
  have hUnit := isUnit_det_hMat (idx := idx) hs hx
  have key : ∀ u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ),
      (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
          (qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2) =
        qv (colMap hs h u).1 + blk n (tauMat X bas idx x) *ᵥ qv (colMap hs h u).2 := by
    intro u
    have ea : qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2 =
        fun p : Fin n × Fin g =>
          (hMat X bas idx x *ᵥ (fun k => per X x (famOf bas u k) ∘ idx) p.1) p.2 := by
      funext p
      rw [hMat_mulVec_per_crd idx hs hx, Pi.add_apply, blk_mulVec]
      simp only [Pi.add_apply, hcrd, Sum.elim_inl, Sum.elim_inr]
      rfl
    rw [ea, conj_mulVec idx hs hx h (fun k => per X x (famOf bas u k) ∘ idx)]
    funext p
    rw [← per_mul idx x h (famOf bas u) p.1, hMat_mulVec_per_crd idx hs hx, Pi.add_apply,
      Pi.add_apply, blk_mulVec]
    rfl
  obtain ⟨e1, e2⟩ := hact _ hB _ _ hB.1 key
  have hdetM : (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹).det =
      ∏ i, rowType X (idx i) h.det := by
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, blk_mul, mul_nonsing_inv _ hUnit, blk_one,
      det_one, one_mul, det_actM]
  have hdeth : h.det ≠ 0 := by
    have := congrArg Matrix.det hu
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have hP : ∏ i, rowType X (idx i) h.det ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hdeth
  rw [e2, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv'] at hdetM
  have hD : (spDen s (blk n (tauMat X bas idx x))).det ≠ 0 := by
    intro hz
    rw [hz, _root_.inv_zero] at hdetM
    exact hP hdetM.symm
  refine ⟨hT, e1.symm, ?_, fun z => ?_⟩
  · rw [← hdetM, mul_inv_cancel₀ hD]
  · rw [← mulVec_transpose, ← e2]
    exact conj_mulVec idx hs hx h z

end GlobalTheory.ColumnSymplectic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumnsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplectic_unitary_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  first | exact @GlobalTheory.ColumnSymplectic.exists_symplectic_columns | exact GlobalTheory.ColumnSymplectic.exists_symplectic_columns | (intros; apply GlobalTheory.ColumnSymplectic.exists_symplectic_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionProperties
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker

namespace GlobalTheory.Phase.Doubling

noncomputable section

variable {n g : ℕ}

def rowM (j : Fin 2) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : Matrix (Fin n) (Fin g) ℚ :=
  Matrix.of fun k i => x j (k, i)

def glue (a b : Matrix (Fin n) (Fin g) ℚ) : Matrix (Fin 2) (Fin n × Fin g) ℚ :=
  Matrix.of fun j p => if j = 0 then a p.1 p.2 else b p.1 p.2

theorem rowM_glue_zero (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 0 (glue a b) = a := by
  ext k i; simp [rowM, glue]

theorem rowM_glue_one (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 1 (glue a b) = b := by
  ext k i; simp [rowM, glue]

theorem glue_rowM (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : glue (rowM 0 x) (rowM 1 x) = x := by
  ext j p; fin_cases j <;> simp [rowM, glue]

theorem dup_apply (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    dup φ x = φ (rowM 0 x) * φ (rowM 1 x) := rfl

theorem rowM_add (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x + y) = rowM j x + rowM j y := rfl

theorem rowM_sub (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x - y) = rowM j x - rowM j y := rfl

theorem rowM_smul (j : Fin 2) (c : ℚ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (c • x) = c • rowM j x := rfl

def rowEquiv (n g : ℕ) : Matrix (Fin 2) (Fin n × Fin g) ℚ ≃
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun x := (rowM 0 x, rowM 1 x)
  invFun p := glue p.1 p.2
  left_inv x := glue_rowM x
  right_inv p := by simp [rowM_glue_zero, rowM_glue_one]

theorem dot_row (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    x j ⬝ᵥ y j = ∑ k, rowM j x k ⬝ᵥ rowM j y k := by
  simp [dotProduct, rowM, Fintype.sum_prod_type]

def comp (j : Fin 2) : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ →+
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun y := (rowM j y.1, rowM j y.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def glueP : (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) ×
    (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) →+
    Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ where
  toFun z := (glue z.1.1 z.2.1, glue z.1.2 z.2.2)
  map_zero' := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> simp [glue]
  map_add' a b := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> fin_cases j <;> simp [glue]

theorem comp_glueP_zero (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 0 (glueP (a, b)) = a := by
  show (rowM 0 (glue a.1 b.1), rowM 0 (glue a.2 b.2)) = a
  simp [rowM_glue_zero]

theorem comp_glueP_one (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 1 (glueP (a, b)) = b := by
  show (rowM 1 (glue a.1 b.1), rowM 1 (glue a.2 b.2)) = b
  simp [rowM_glue_one]

theorem glueP_comp (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    glueP (comp 0 y, comp 1 y) = y := by
  show (glue (rowM 0 y.1) (rowM 1 y.1), glue (rowM 0 y.2) (rowM 1 y.2)) = y
  simp [glue_rowM]

theorem om_eq (y y' : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    om y y' = om (comp 0 y) (comp 0 y') + om (comp 1 y) (comp 1 y') := by
  simp only [om, Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib]
  exact add_sub_add_comm _ _ _ _

theorem om_zero_right (y : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) : om y 0 = 0 := by
  simp [om, dotProduct]

theorem heisS_dup (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ)
    (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    heisS y.1 y.2 (dup φ) x = heisS (comp 0 y).1 (comp 0 y).2 φ (rowM 0 x) *
      heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x) := by
  have h : (∑ k, (2 * (x k ⬝ᵥ y.1 k) - y.1 k ⬝ᵥ y.2 k) : ℚ) =
      (∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) +
      (∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) := by
    simp only [Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib, Finset.mul_sum]
    exact add_sub_add_comm _ _ _ _
  unfold heisS
  rw [h, Rat.cast_add, mul_add, Complex.exp_add, dup_apply, rowM_sub, rowM_sub]
  show _ = (φ (rowM 0 x - rowM 0 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) : ℂ))) *
    (φ (rowM 1 x - rowM 1 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) : ℂ)))
  ring

theorem isSB_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) : IsSB (dup φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx j p => ?_, fun x y hy => ?_⟩
  · rw [dup_apply] at hx
    fin_cases j
    · exact h1 _ (left_ne_zero_of_mul hx) p.1 p.2
    · exact h1 _ (right_ne_zero_of_mul hx) p.1 p.2
  · rw [dup_apply, dup_apply, rowM_add, rowM_add, rowM_smul, rowM_smul,
      h2 _ (rowM 0 y) (fun k i => hy 0 (k, i)), h2 _ (rowM 1 y) (fun k i => hy 1 (k, i))]

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨k, hk, hb⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m k,
    pow_mul b, hb, ← pow_mul]

theorem pv_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : PV φ) : PV (dup φ) := by
  obtain ⟨⟨A, ε, hV⟩, hP⟩ := h
  refine ⟨⟨(A.prod A).map glueP, fun y => ε (comp 0 y) * ε (comp 1 y), ?_⟩,
    fun x => ph_mul (hP _) (hP _)⟩
  have mem : ∀ y, y ∈ (A.prod A).map glueP ↔ comp 0 y ∈ A ∧ comp 1 y ∈ A := by
    intro y
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [comp_glueP_zero, comp_glueP_one]
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(comp 0 y, comp 1 y), ⟨ha, hb⟩, glueP_comp y⟩
  refine ⟨?_, fun y => ?_, fun y hy => ?_, fun y hy y' hy' => ?_, ?_, isSB_dup hV.sb, fun y hy => ?_⟩
  · have := (hV.fg.prod hV.fg)
    rw [AddSubgroup.fg_iff] at this ⊢
    obtain ⟨S, hS, hf⟩ := this
    exact ⟨glueP '' S, by rw [← hS, AddMonoidHom.map_closure], hf.image _⟩
  · constructor
    · intro hy y' hy'
      rw [mem] at hy hy'
      obtain ⟨m, hm⟩ := (hV.dual _).1 hy.1 _ hy'.1
      obtain ⟨k, hk⟩ := (hV.dual _).1 hy.2 _ hy'.2
      exact ⟨m + k, by rw [om_eq, hm, hk, Int.cast_add]⟩
    · intro hy
      rw [mem]
      constructor
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (a, 0)) ⟨(a, 0), ⟨ha, A.zero_mem⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, add_zero] at this
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (0, a)) ⟨(0, a), ⟨A.zero_mem, ha⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, zero_add] at this
  · rw [mem] at hy
    rw [norm_mul, hV.norm _ hy.1, hV.norm _ hy.2, one_mul]
  · rw [mem] at hy hy'
    rw [map_add (f := _), map_add (f := _), hV.semi _ hy.1 _ hy'.1, hV.semi _ hy.2 _ hy'.2, om_eq y y',
      Rat.cast_add, mul_add, Complex.exp_add]
    ring
  · obtain ⟨m, hm, h⟩ := hV.ord
    refine ⟨m, hm, fun y hy => ?_⟩
    rw [mem] at hy
    rw [map_nsmul, map_nsmul, h _ hy.1, h _ hy.2, one_mul]
  · rw [mem] at hy
    funext x
    have h0 := congrFun (hV.fix _ hy.1) (rowM 0 x)
    have h1 := congrFun (hV.fix _ hy.2) (rowM 1 x)
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    rw [heisS_dup, dup_apply, ← h0, ← h1]
    rw [h0, h1]
    linear_combination (ε (comp 1 y) * heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x)) * h0 +
      φ (rowM 0 x) * h1

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) : blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]

theorem blk_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · ext p q
    have := h.1.apply p.2 q.2
    by_cases hpq : p.1 = q.1
    · simp [blk, hpq, this]
    · simp [blk, hpq, Ne.symm hpq]
  · have : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (τ.map Complex.im) := by
      ext p q
      by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [this]
    exact Matrix.PosDef.one.kronecker h.2

theorem blk_inv (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  have : ((blk n τ).map fun z => (z.im : ℂ)) = blk n (τ.map fun z => (z.im : ℂ)) := by
    ext p q
    by_cases h : p.1 = q.1 <;> simp [blk, h]
  rw [this, blk_eq, blk_eq, Matrix.inv_kronecker, inv_one]

theorem expo_row (τ : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin 2 → Fin n × Fin g → ℂ) (j : Fin 2)
    (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    qv (x j) ⬝ᵥ blk n τ *ᵥ qv (x j) + 2 * (qv (x j) ⬝ᵥ ζ j) =
      ∑ k, (qv (rowM j x k) ⬝ᵥ τ *ᵥ qv (rowM j x k) +
        2 * (qv (rowM j x k) ⬝ᵥ (fun k i => ζ j (k, i)) k)) := by
  simp [dotProduct, mulVec, qv, rowM, blk, Fintype.sum_prod_type, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem thS_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin 2 → Fin n × Fin g → ℂ) :
    thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i)) := by
  have s0 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 0 (k, i))
  have s1 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 1 (k, i))
  unfold thS
  rw [tsum_mul_tsum_of_summable_norm s0 s1, ← (rowEquiv n g).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Fin.sum_univ_two, expo_row, expo_row, mul_add, Complex.exp_add, dup_apply]
  simp only [rowEquiv, Equiv.coe_fn_mk]
  ring

theorem doubling : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  intro n g φ
  refine ⟨pv_dup, fun h h' => h ?_, isSB_dup, fun u => ?_, fun τ hτ =>
    ⟨blk_siegel hτ, fun h ζ => thS_dup h hτ ζ, blk_inv τ⟩⟩
  · funext a
    have := congrFun h' (glue a a)
    rw [dup_apply, rowM_glue_zero, rowM_glue_one] at this
    exact mul_self_eq_zero.1 this
  · funext x
    simp only [dup_apply, Pi.smul_apply, smul_eq_mul]
    ring

end

end GlobalTheory.Phase.Doubling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionPropertiesStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledRowTestFunction_properties : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  first | exact @GlobalTheory.Phase.Doubling.doubling | exact GlobalTheory.Phase.Doubling.doubling | (intros; apply GlobalTheory.Phase.Doubling.doubling <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
section Siegel

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Mult

theorem thS_smul' {κ ι : Type} [Fintype κ] [Fintype ι] (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ)
    (ζ : κ → ι → ℂ) : thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  congr 1
  funext x
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem isSB_smul' {κ ι : Type} [Fintype κ] [Fintype ι] (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) :
    IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x ?_, fun x y hy => ?_⟩
  · intro h0
    apply hx
    simp [h0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2 x y hy]

theorem quad_blk {n g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin n × Fin g → ℂ) :
    ζ ⬝ᵥ blk n M *ᵥ ζ = ∑ k, (fun i => ζ (k, i)) ⬝ᵥ M *ᵥ fun i => ζ (k, i) := by
  simp only [dotProduct, mulVec, blk, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem isMu_of_fixed {n g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g))
    {s : Matrix ((Fin n × Fin g) ⊕ (Fin n × Fin g)) ((Fin n × Fin g) ⊕ (Fin n × Fin g)) ℚ}
    (hs : s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ) (hfix : spAct s (blk n τ) = blk n τ)
    {d t : ℂ} (hd : (spDen s (blk n τ)).det * d = 1) (hd1 : ‖d‖ = 1) (ht : ‖t‖ = 1)
    {φ φ' : Matrix (Fin n) (Fin g) ℚ → ℂ} (hφ : PV φ) (hφ' : PV φ') (h0 : φ' ≠ 0)
    (H : ∀ ζ ζ' : Fin n × Fin g → ℂ, ζ' = ζ ᵥ* (spDen s (blk n τ))⁻¹ →
      cexp (π / 2 * ∑ k, (fun i => ζ' (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ fun i => ζ' (k, i)) *
        thS φ' τ (fun k i => ζ' (k, i)) =
      t * (cexp (π / 2 * ∑ k, (fun i => ζ (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ fun i => ζ (k, i)) *
        thS φ τ (fun k i => ζ (k, i)))) : IsMu (t ^ 2 * d) := by
  classical
  set B := blk n τ with hB
  set D := spDen s B with hD
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hd)
  have hsb : IsSB φ := by
    obtain ⟨A, ε, hv⟩ := hφ.1
    exact hv.sb
  have hsb' : IsSB φ' := by
    obtain ⟨A, ε, hv⟩ := hφ'.1
    exact hv.sb
  obtain ⟨hpvd, -, hsbd, -, hτB⟩ := GlobalTheory.T.doubledRowTestFunction_properties n g φ
  obtain ⟨hpvd', hned', hsbd', -, hτB'⟩ := GlobalTheory.T.doubledRowTestFunction_properties n g φ'
  obtain ⟨hBs, hthS, hImB⟩ := hτB τ hτ
  obtain ⟨-, hthS', -⟩ := hτB' τ hτ

  have hrel : ∀ ζ : Fin n × Fin g → ℂ, thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i)) =
      t * cexp (π * I * (ζ ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ ζ)) * thS φ τ (fun k i => ζ (k, i)) := by
    intro ζ
    have h1 := H ζ (ζ ᵥ* D⁻¹) rfl
    have hq : ∀ v : Fin n × Fin g → ℂ,
        ∑ k, (fun i => v (k, i)) ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ (fun i => v (k, i)) =
          v ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ v := by
      intro v
      rw [hImB, quad_blk]
    rw [hq ζ, hq (ζ ᵥ* D⁻¹)] at h1
    have hc := canon_exponent_invariant (Fin n × Fin g) s hs B hBs ζ
    rw [hfix] at hc
    set a := ζ ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ
    set a' := (ζ ᵥ* D⁻¹) ⬝ᵥ (B.map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* D⁻¹)
    set e := ζ ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ ζ
    have ha' : a' = a - 2 * I * e := by rw [← hc]; ring
    have hexp : cexp (π / 2 * a') = cexp (π / 2 * a) * cexp (-(π * I * e)) := by
      rw [← Complex.exp_add, ha']
      congr 1
      ring
    rw [hexp] at h1
    have hne : cexp (π / 2 * a) ≠ 0 := Complex.exp_ne_zero _
    have h2 : cexp (-(π * I * e)) * thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i)) =
        t * thS φ τ (fun k i => ζ (k, i)) := by
      apply mul_left_cancel₀ hne
      rw [← mul_assoc, h1]
      ring
    calc thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i))
        = cexp (π * I * e) * (cexp (-(π * I * e)) * thS φ' τ (fun k i => (ζ ᵥ* D⁻¹) (k, i))) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = t * cexp (π * I * e) * thS φ τ (fun k i => ζ (k, i)) := by
          rw [h2]
          ring

  have hdup : ∀ Z : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ') B (fun k => Z k ᵥ* D⁻¹) =
      t ^ 2 * cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z := by
    intro Z
    rw [hthS' hsb', hthS hsb, hrel (Z 0), hrel (Z 1), Fin.sum_univ_two, mul_add, Complex.exp_add]
    ring
  have heven : Even (Fintype.card (Fin 2)) := by
    rw [Fintype.card_fin]
    exact even_two
  obtain ⟨ω, hω⟩ := exists_weil_of_symplectic (Fin 2) (Fin n × Fin g) s heven hs
  obtain ⟨hsbω, hTω, -⟩ := hω (dup φ) (hsbd hsb)
  have hT : ∀ Z : Fin 2 → Fin n × Fin g → ℂ,
      cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z =
        d * thS (ω (dup φ)) B (fun k => Z k ᵥ* D⁻¹) := by
    intro Z
    have h1 := hTω B hBs Z
    rw [hfix, Fintype.card_fin] at h1
    rw [h1]
    calc cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) * thS (dup φ) B Z
        = (D.det * d) * (cexp (π * I * ∑ k, Z k ⬝ᵥ (D⁻¹ * qm s.toBlocks₂₁) *ᵥ Z k) *
            thS (dup φ) B Z) := by rw [hd, one_mul]
      _ = _ := by ring
  have hall : ∀ W : Fin 2 → Fin n × Fin g → ℂ,
      thS (dup φ') B W = thS ((t ^ 2 * d) • ω (dup φ)) B W := by
    intro W
    have hW : W = fun k => (W k ᵥ* D) ᵥ* D⁻¹ := by
      funext k
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hDu, Matrix.vecMul_one]
    rw [thS_smul', hW, hdup, mul_assoc, hT, ← hW]
    ring
  have heq := eq_of_thS_eq (Fin 2) (Fin n × Fin g) (dup φ') ((t ^ 2 * d) • ω (dup φ))
    (hsbd' hsb') (isSB_smul' _ hsbω) B hBs hall
  have hpvω : PV (ω (dup φ)) :=
    GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform (Fin 2) (Fin n × Fin g) heven s hs (dup φ) (ω (dup φ)) hsbω hTω (hpvd hφ)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp (hned' h0)
  have hxe : dup φ' x = (t ^ 2 * d) * ω (dup φ) x := by
    rw [heq]
    rfl
  have hb0 : ω (dup φ) x ≠ 0 := by
    intro hz
    apply hx
    rw [hxe, hz, mul_zero]
    rfl
  have hph : Ph (t ^ 2 * d) :=
    GlobalTheory.Phase.Calc.ph_cancel hb0 (hpvω.2 x) (hxe ▸ (hpvd' hφ').2 x)
  refine GlobalTheory.Phase.Calc.isMu_of_ph hph ?_
  rw [norm_mul, norm_pow, ht, hd1]
  norm_num

end GlobalTheory.Phase.Mult

end Siegel

section Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Mult

theorem isUnit_hMat_of_siegel {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (h : tauMat X bas idx x ∈ Siegel (Fin g)) : IsUnit (ThFr.hMat X bas idx x).det := by
  by_cases hP : IsUnit (perMat X bas idx Sum.inl x).det
  · exact Matrix.isUnit_nonsing_inv_det _ hP
  · have h0 : ThFr.hMat X bas idx x = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hP
    have ht : tauMat X bas idx x = 0 := by
      rw [ThFr.tauMat, h0, Matrix.zero_mul]
    rw [ht] at h
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · rw [Matrix.det_fin_zero]
      exact isUnit_one
    · exfalso
      have hx : Finsupp.single (⟨0, hg⟩ : Fin g) (1 : ℝ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
      have := h.2.2 hx
      simp at this

theorem norm_det_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (σ : E →+* ℂ) : ‖σ h.det‖ = 1 := by
  have h1 : cc h.det * h.det = 1 := by
    have := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one, ccT, Matrix.det_transpose] at this
    have hm : (h.map cc).det = cc h.det := by
      have := (IsCMField.complexConj E).toRingHom.map_det h
      rw [RingHom.mapMatrix_apply] at this
      exact this.symm
    rwa [hm] at this
  have h2 : conj (σ h.det) * σ h.det = 1 := by
    rw [← IsCMField.complexEmbedding_complexConj, ← map_mul]
    have : IsCMField.complexConj E h.det * h.det = 1 := h1
    rw [this, map_one]
  have h3 := congrArg (‖·‖) h2
  simp only [norm_mul, Complex.norm_conj, norm_one] at h3
  nlinarith [norm_nonneg (σ h.det)]

theorem isMu_multiplier_sq_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ t : ℂ, ‖t‖ = 1 → (∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (Dict.hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z) → IsMu (t ^ 2 * ∏ i : Fin g, rowType X (idx i) h.det) := by
  intro E _ _ _ r X g bas idx n hS hn w hw hwc h hu Λ hΛ Λ' hΛ' L hL v hv x hx t ht H
  obtain ⟨u, hu1, hU⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hS hn w hw hwc L hL v hv
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.T.exists_rational_symplectic_unitary_columns E r X g bas idx n hS hn h hu
  obtain ⟨hτ, hfix, hdet, hvec⟩ := hsx x hx
  obtain ⟨-, hpv, -⟩ := hU Λ hΛ
  obtain ⟨hvac', hpv', -⟩ := hU Λ' hΛ'
  have hMu : IsUnit (hMat X bas idx x).det := isUnit_hMat_of_siegel X bas idx x hτ
  have hd1 : ‖∏ i : Fin g, rowType X (idx i) h.det‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => norm_det_unitary hu _
  have hψ'0 : u • unitv (projA X bas w (tens Λ' L) v) ≠ 0 := by
    intro h0
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu1
      exact zero_ne_one hu1
    have hz : unitv (projA X bas w (tens Λ' L) v) = 0 := by
      funext y
      have := congrFun h0 y
      simpa [hu0] using this
    have h1 : ip (unitv (projA X bas w (tens Λ' L) v)) (unitv (projA X bas w (tens Λ' L) v)) = 1 :=
      hvac'.2.1
    rw [hz] at h1
    simp [GlobalTheory.SW.ip, GlobalTheory.SW.haar, GlobalTheory.SW.haarAt] at h1
  refine isMu_of_fixed hτ hs hfix hdet hd1 ht hpv hpv' hψ'0 ?_
  intro ζ ζ' hζ'
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Fin g → ℂ, ∀ k, hMat X bas idx x *ᵥ z k = fun i => ζ (k, i) :=
    ⟨fun k => (hMat X bas idx x)⁻¹ *ᵥ fun i => ζ (k, i), fun k => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]⟩
  have hζ : (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = ζ := by
    funext p
    rw [hz p.1]
  have hz' : ∀ k, hMat X bas idx x *ᵥ Dict.hAct X idx h z k = fun i => ζ' (k, i) := by
    intro k
    funext i
    have := congrFun (hvec z) (k, i)
    rw [hζ, ← hζ'] at this
    exact this.symm
  have H1 := H z
  simp only [GlobalTheory.SW.thA, hz, hz', imInv_eq] at H1
  rw [thS_smul', thS_smul']
  have hne := pow_ne_zero (n / 2) hMu.ne_zero
  have H2 := mul_left_cancel₀ hne (by rw [← _root_.mul_assoc, H1]; ring :
    (hMat X bas idx x).det ^ (n / 2) *
      (cexp (Real.pi / 2 * ∑ k, (fun i => ζ' (k, i)) ⬝ᵥ ((tauMat X bas idx x).map fun z => (z.im : ℂ))⁻¹ *ᵥ
          (fun i => ζ' (k, i))) * thS (unitv (projA X bas w (tens Λ' L) v)) (tauMat X bas idx x)
          (fun k i => ζ' (k, i))) =
    (hMat X bas idx x).det ^ (n / 2) *
      (t * (cexp (Real.pi / 2 * ∑ k, (fun i => ζ (k, i)) ⬝ᵥ ((tauMat X bas idx x).map fun z => (z.im : ℂ))⁻¹ *ᵥ
          (fun i => ζ (k, i))) * thS (unitv (projA X bas w (tens Λ L) v)) (tauMat X bas idx x)
          (fun k i => ζ (k, i)))))
  linear_combination u * H2

end GlobalTheory.Phase.Mult

end Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ t : ℂ, ‖t‖ = 1 → (∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (Dict.hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z) → IsMu (t ^ 2 * ∏ i : Fin g, rowType X (idx i) h.det) := by
  first | exact @GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | exact GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | (intros; apply GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det <;> assumption)
end
