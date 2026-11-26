module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusCoords
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem real_smul_vec (c : ℝ) (z : ι → ℂ) : c • z = (c : ℂ) • z := by
  ext i
  simp [Complex.real_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem map_conj_transpose (M : Matrix ι ι ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := rfl

theorem hyperbolic_at_place (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨(GramAtData.proof h v w).1, (GramAtData.proof h v w).2, ?_, ?_, ?_⟩
  · rw [hForm, ← HermAtPlace.proof h v w, h1, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h2, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h3, map_one]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem archUnitary_at_place {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (w : InfinitePlace E) :
    (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w := by
  rw [← map_conj_transpose]
  exact mem_archUnitary.1 g.2 w

def heisY (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Submodule ℝ (InfinitePlace E → ι → ℂ) where
  carrier := {y | ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0}
  add_mem' {y z} hy hz w := by
    simp only [Pi.add_apply, hForm_add_right, (hy w).1, (hz w).1, (hy w).2, (hz w).2, add_zero,
      and_self]
  zero_mem' w := ⟨hForm_zero_right _ _, hForm_zero_right _ _⟩
  smul_mem' c y hy w := by
    simp only [Pi.smul_apply, real_smul_vec, hForm_smul_right, (hy w).1, (hy w).2, mul_zero,
      and_self]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem mem_heisY {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
    {y : InfinitePlace E → ι → ℂ} : y ∈ heisY h v x₀ w₀ ↔
      ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
        hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0 := Iff.rfl

abbrev HeisCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :=
  heisY h v x₀ w₀ × (InfinitePlace E → ℝ)

def heisMatAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (y : InfinitePlace E → ι → ℂ) (t : InfinitePlace E → ℝ) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  heisMat (gramAt h v w) (vecAt v x₀ w) (y w) (heisS (gramAt h v w) (y w) (t w))

omit [DecidableEq ι] in
theorem heisS_add {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (y₁ y₂ : ι → ℂ) (t₁ t₂ : ℝ) :
    heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂ =
      heisS H (y₁ + y₂) (t₁ + t₂ - (hForm H y₁ y₂).im) := by
  have hs : (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      starRingEnd ℂ (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      hForm H (y₁ + y₂) (y₁ + y₂) = 0 := by
    have e1 := heisS_spec hH y₁ t₁
    have e2 := heisS_spec hH y₂ t₂
    have e3 := hForm_conj hH y₁ y₂
    simp only [map_add (f := _), map_sub, hForm_add_left, hForm_add_right]
    linear_combination e1 + e2 - e3
  rw [eq_heisS hs]
  congr 1

section Coords

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem heisMatAt_mul (hp : IsHyperbolicPair h x₀ w₀) {y₁ y₂ : InfinitePlace E → ι → ℂ}
    (hy₁ : y₁ ∈ heisY h v x₀ w₀) (hy₂ : y₂ ∈ heisY h v x₀ w₀) (t₁ t₂ : InfinitePlace E → ℝ)
    (w : InfinitePlace E) :
    heisMatAt h v x₀ y₁ t₁ w * heisMatAt h v x₀ y₂ t₂ w = heisMatAt h v x₀ (y₁ + y₂)
      (t₁ + t₂ - fun w => (hForm (gramAt h v w) (y₁ w) (y₂ w)).im) w := by
  obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
  rw [heisMatAt, heisMatAt, heisMat_mul hH ha (hy₁ w).1 (hy₂ w).1, heisS_add hH, heisMatAt]
  rfl

def heisUnit (hp : IsHyperbolicPair h x₀ w₀) (y : heisY h v x₀ w₀) (t : InfinitePlace E → ℝ)
    (w : InfinitePlace E) : GL ι ℂ where
  val := heisMatAt h v x₀ y t w
  inv := heisMatAt h v x₀ (-(y : InfinitePlace E → ι → ℂ)) (-t) w
  val_inv := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp y.2 (neg_mem y.2), heisMatAt]
    simp only [add_neg_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_right, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero
  inv_val := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp (neg_mem y.2) y.2, heisMatAt]
    simp only [neg_add_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_left, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero

def heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) : unipRadical h v x₀ :=
  ⟨⟨fun w => heisUnit hp p.1 p.2 w, mem_archUnitary.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      rw [map_conj_transpose]
      exact heisMat_unitary hH ha (p.1.2 w).1 (heisS_spec hH _ _)⟩,
    mem_unipRadical.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      refine ⟨heisMat_mulVec_self hH ha (p.1.2 w).1 _, fun z hz => ⟨-hForm (gramAt h v w)
        ((p.1 : InfinitePlace E → ι → ℂ) w) z, ?_⟩⟩
      change heisMat _ _ _ _ *ᵥ z = _
      rw [heisMat_mulVec, show hForm (gramAt h v w) (vecAt v x₀ w) z = 0 from hz]
      simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]⟩

theorem heisPoint_val (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    ((((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) = heisMatAt h v x₀ p.1 p.2 w := rfl


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem unipRadical_at_place (n : unipRadical h v x₀) (w : InfinitePlace E) :
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)ᴴ * gramAt h v w *
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      vecAt v x₀ w ∧
    ∀ z, hForm (gramAt h v w) (vecAt v x₀ w) z = 0 → ∃ c : ℂ,
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        z + c • vecAt v x₀ w :=
  ⟨archUnitary_at_place _ w, (mem_unipRadical.1 n.2 w).1, (mem_unipRadical.1 n.2 w).2⟩

def heisU (n : unipRadical h v x₀) (w : InfinitePlace E) : ι → ℂ :=
  (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

def heisYOf (n : unipRadical h v x₀) : InfinitePlace E → ι → ℂ := fun w =>
  heisU (w₀ := w₀) n w - hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) • vecAt v x₀ w

theorem heisYOf_spec (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) +
      starRingEnd ℂ (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) +
      hForm (gramAt h v w) (heisYOf (w₀ := w₀) n w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w)
        (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  obtain ⟨hn, hna, hn'⟩ := unipRadical_at_place n w
  exact eq_heisMat hH ha hb hab hn hna hn'

def heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) : HeisCoord h v x₀ w₀ :=
  (⟨heisYOf n, fun w => ⟨(heisYOf_spec hp n w).1, (heisYOf_spec hp n w).2.1⟩⟩,
    fun w => (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)).im)

end Coords

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem continuous_hForm_self (H : Matrix ι ι ℂ) {X : Type*} [TopologicalSpace X] {y : X → ι → ℂ}
    (hy : Continuous y) : Continuous fun x => hForm H (y x) (y x) :=
  (continuous_star.comp hy).dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem continuous_hForm_right (H : Matrix ι ι ℂ) (u : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} (hy : Continuous y) : Continuous fun x => hForm H u (y x) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem heisS_eq (H : Matrix ι ι ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H y t = ((-(hForm H y y).re / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [heisS]

theorem continuous_heisMat_heisS (H : Matrix ι ι ℂ) (a : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} {t : X → ℝ} (hy : Continuous y) (ht : Continuous t) :
    Continuous fun x => heisMat H a (y x) (heisS H (y x) (t x)) := by
  have hs : Continuous fun x => heisS H (y x) (t x) := by
    simp only [heisS_eq]
    exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.comp (continuous_hForm_self H hy)).neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp ht).mul continuous_const)
  unfold heisMat
  exact (continuous_const.add ((hy.add (hs.smul continuous_const)).matrix_vecMulVec
    continuous_const)).sub (continuous_const.matrix_vecMulVec
      ((continuous_star.comp hy).matrix_vecMul continuous_const))

section Homeo

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_unipRadical_at (w : InfinitePlace E) :
    Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
  Units.continuous_val.comp ((continuous_apply w).comp
    (continuous_subtype_val.comp continuous_subtype_val))

theorem heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    heisU (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w +
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) • vecAt v x₀ w := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hyb : hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
    rw [← hForm_conj hH, (p.1.2 w).2, map_zero]
  rw [heisU, heisPoint_val, heisMatAt, heisMat_mulVec, hab, hyb]
  simp only [one_smul, zero_smul, sub_zero, add_sub_cancel_left]

theorem hForm_heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w) =
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hab, map_one]
  rw [heisU_heisPoint, hForm_add_right, hForm_smul_right, (p.1.2 w).2, hba]
  ring

theorem heisCoordOf_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisCoordOf hp (heisPoint hp p) = p := by
  refine Prod.ext (Subtype.ext (funext fun w => ?_)) (funext fun w => ?_)
  · change heisYOf (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w
    rw [heisYOf, hForm_heisU_heisPoint, heisU_heisPoint, add_sub_cancel_right]
  · change (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w)).im = p.2 w
    rw [hForm_heisU_heisPoint, heisS_im]

theorem heisPoint_heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) :
    heisPoint hp (heisCoordOf hp n) = n := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  obtain ⟨-, -, h3, h4⟩ := heisYOf_spec hp n w
  rw [heisPoint_val]
  conv_rhs => rw [h4]
  exact congrArg (heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w))
    (eq_heisS h3).symm

def heisHomeo (hp : IsHyperbolicPair h x₀ w₀) : HeisCoord h v x₀ w₀ ≃ₜ unipRadical h v x₀ where
  toFun := heisPoint hp
  invFun := heisCoordOf hp
  left_inv := heisCoordOf_heisPoint hp
  right_inv := heisPoint_heisCoordOf hp
  continuous_toFun := by
    have hy : Continuous fun p : HeisCoord h v x₀ w₀ => (p.1 : InfinitePlace E → ι → ℂ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : HeisCoord h v x₀ w₀ => p.2 := continuous_snd
    refine continuous_induced_rng.2 (continuous_induced_rng.2 (continuous_pi fun w => ?_))
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy)
        ((continuous_apply w).comp ht)
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy.neg)
        ((continuous_apply w).comp ht.neg)
  continuous_invFun := by
    have hu : ∀ w, Continuous fun n : unipRadical h v x₀ => heisU (w₀ := w₀) n w := fun w =>
      ((continuous_unipRadical_at w).matrix_mulVec continuous_const).sub continuous_const
    have hs : ∀ w, Continuous fun n : unipRadical h v x₀ =>
        hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) := fun w =>
      continuous_hForm_right _ _ (hu w)
    refine Continuous.prodMk (f := fun n => (heisCoordOf hp n).1)
      (g := fun n => (heisCoordOf hp n).2) ?_ ?_
    · refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
      exact (hu w).sub ((hs w).smul continuous_const)
    · exact continuous_pi fun w => Complex.continuous_im.comp (hs w)

theorem heisHomeo_apply (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisHomeo hp p = heisPoint hp p := rfl

theorem heisPoint_mul (hp : IsHyperbolicPair h x₀ w₀) (p q : HeisCoord h v x₀ w₀) :
    heisPoint hp p * heisPoint hp q = heisPoint hp (p.1 + q.1, p.2 + q.2 - fun w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((q.1 : InfinitePlace E → ι → ℂ) w)).im) := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisPoint_val, heisMatAt_mul hp p.1.2 q.1.2]
  rfl

def heisConjLin (g : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      (y : InfinitePlace E → ι → ℂ) w, fun w => by
    have ha := (Subgroup.mem_inf.1 hg).1 w
    have hb := (Subgroup.mem_inf.1 hg).2 w
    constructor
    · conv_lhs => rw [← ha]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).1]
    · conv_lhs => rw [← hb]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).2]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [mulVec_add]
  map_smul' c y := by
    apply Subtype.ext
    funext w
    change _ *ᵥ (c • (y : InfinitePlace E → ι → ℂ) w) =
      c • (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w)
    rw [real_smul_vec, real_smul_vec, mulVec_smul]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem heisConjLin_apply (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y : heisY h v x₀ w₀) (w : InfinitePlace E) :
    ((heisConjLin g hg y : heisY h v x₀ w₀) : InfinitePlace E → ι → ℂ) w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w := rfl

theorem heisPoint_conj (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisConjLin g hg p.1, p.2) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have ha := (Subgroup.mem_inf.1 hg).1 w
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt, heisMat_conj hu ha, mul_assoc,
    Units.mul_inv, mul_one, heisConjLin_apply]
  congr 1
  simp only [heisS, hForm_mulVec_of_unitary _ hu]

end Homeo

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
