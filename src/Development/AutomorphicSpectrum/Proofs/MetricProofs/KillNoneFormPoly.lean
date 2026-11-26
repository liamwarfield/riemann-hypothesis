module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

theorem killNone_formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) :
    aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) (formPoly n a)
      = formPoly n fun w => a fun j => some (w j) := by
  classical
  unfold formPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  symm
  refine Finset.sum_of_injOn (fun (w : Fin n → σ) j => some (w j)) ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext j
    exact Option.some_injective _ (congrFun h j)
  · intro w _
    exact Finset.mem_univ _
  · intro w _ hw
    have : ∃ j, w j = none := by
      by_contra hc
      apply hw
      have hc' : ∀ j, (w j).isSome := fun j => by
        cases h : w j with
        | none => exact absurd ⟨j, h⟩ hc
        | some _ => rfl
      exact ⟨fun j => (w j).get (hc' j), Finset.mem_coe.2 (Finset.mem_univ _), by funext j; simp⟩
    obtain ⟨j, hj⟩ := this
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w _
    simp [map_prod]

theorem killNone_toWtS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) :
    aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) (toWtS Q)
      = toWt (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) Q) := by
  have h : (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)).comp toWtS
      = toWt.comp (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)) := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o with
    | none => simp [toWtS, toWt]
    | some p =>
      simp only [toWtS, toWt, AlgHom.comp_apply, aeval_X, Option.elim_some, aeval_rename]
      have : ((fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) ∘ some) = X := rfl
      rw [this, aeval_X_left_apply]
  exact DFunLike.congr_fun h Q

theorem eval_toWt_gap {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ) :
    eval lam (toWt Q) = eval (gap lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWt]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [toWt, gap]

theorem eval_toWtS_gapS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ)
    (s : ℝ) : eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWtS]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | none => simp [toWtS, gapS]
    | some q =>
      simp only [toWtS, gapS, gap, aeval_X, eval_X, Option.elim_some, eval_rename]
      rfl

theorem poly_s_zero : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ),
    (∀ (a : (Fin n → Option (Ψ × Fin N)) → ℝ),
      aeval (fun o : Option (Ψ × Fin N) => o.elim 0 X) (toWtS (formPoly n a))
        = toWt (formPoly n fun w => a fun j => some (w j))) ∧
    (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ), eval lam (toWt Q) = eval (gap lam) Q) ∧
    ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ) (s : ℝ),
      eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  intro Ψ _ N n
  refine ⟨fun a => ?_, eval_toWt_gap, eval_toWtS_gapS⟩
  rw [killNone_toWtS, killNone_formPoly]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem formPoly_isHomogeneous_and_eval (σ : Type) [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) :
    (formPoly n a).IsHomogeneous n ∧
      ∀ c : σ → ℝ, eval c (formPoly n a) = ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
  classical
  refine ⟨?_, fun c => ?_⟩
  · unfold formPoly
    refine IsHomogeneous.sum _ _ _ fun w _ => ?_
    have h : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous (∑ _j : Fin n, 1) :=
      IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _
    have h' : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous n := by simpa using h
    exact h'.C_mul _
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [formPoly, map_sum, map_prod]

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBound
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

private theorem sum_eq_sum_comp_of_eq_zero_of_forall_ne {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommMonoid M] (v : κ → ι) (hv : Function.Injective v) (f : ι → M)
    (hf : ∀ i, (∀ a, i ≠ v a) → f i = 0) :
    ∑ i, f i = ∑ a, f (v a) := by
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := v) (fun a _ b _ h => hv h)]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i (fun a hia =>
    hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hia.symm⟩)))).symm

theorem gramOf_mul {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ) :
    gramOf hd (u * g) = gᴴ * gramOf hd u * g := by
  simp only [GlobalTheory.CompanionTheory.Ar.PB.gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem head_conj_mul {N : ℕ} {P : Type*} [Fintype P] (v : P → Fin N)
    (hv : Function.Injective v) (hdown : ∀ (i : Fin N) (c : P), (∀ a, i ≠ v a) → v c < i)
    (G b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) :
    (bᴴ * G * b).submatrix v v = (b.submatrix v v)ᴴ * G.submatrix v v * b.submatrix v v := by
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
    intro i hi
    rw [hb (hdown i p hi), star_zero, zero_mul]
  · intro j hj
    rw [hb (hdown j q hj), mul_zero]

theorem gramLog_inv (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧
    (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 →
      gramLog hd k (g * b) = gramLog hd k g +
        ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  constructor
  · intro h
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog, GlobalTheory.CompanionTheory.Ar.PB.gramHead]
    rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul, h, GlobalTheory.CompanionTheory.Ar.PB.gramOf]
  · intro hb hdet hM
    have hdown : ∀ (i : Fin N) (c : {a : Fin N // (a : ℕ) < k}),
        (∀ a : {a : Fin N // (a : ℕ) < k}, i ≠ a.val) → c.val < i := by
      intro i c hi
      have hik : ¬ (i : ℕ) < k := fun h => hi ⟨i, h⟩ rfl
      rw [Fin.lt_def]
      exact lt_of_lt_of_le c.2 (not_lt.mp hik)
    have hbk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).IsUpperTriangular :=
      fun i j hij => hb (Subtype.coe_lt_coe.mpr hij)
    have hdiag : ∀ i, b i i ≠ 0 := by
      intro i hi
      have h0 : b.det = 0 := by
        rw [Matrix.det_of_upperTriangular hb]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [h0] at hdet
      exact not_isUnit_zero hdet
    have hdetk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).det = ∏ a : {a : Fin N // (a : ℕ) < k}, b a a :=
      Matrix.det_of_upperTriangular hbk
    have hminor : GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b) =
        (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val)ᴴ *
          GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g *
            b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val := by
      simp only [GlobalTheory.CompanionTheory.Ar.PB.gramHead]
      rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul]
      exact GlobalTheory.CompanionTheory.Ar.PB.head_conj_mul Subtype.val
        Subtype.val_injective hdown _ b hb
    have hB0 : ∏ a : {a : Fin N // (a : ℕ) < k}, b a a ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun a _ => hdiag a)
    have hnorm : ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b)).det‖ =
        ‖∏ a : {a : Fin N // (a : ℕ) < k}, b a a‖ ^ 2 *
          ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g).det‖ := by
      rw [hminor, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetk, norm_mul,
        norm_mul, norm_star]
      ring
    have hsum : (∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) =
        ∑ a : {a : Fin N // (a : ℕ) < k}, Real.log ‖b a a‖ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun a => by simp) _
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog]
    rw [hnorm, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hB0)) (norm_ne_zero_iff.mpr hM),
      Real.log_pow, norm_prod, Real.log_prod (s := Finset.univ)
        (f := fun a : {a : Fin N // (a : ℕ) < k} => ‖b a a‖) (fun a _ => norm_ne_zero_iff.mpr (hdiag a)),
      hsum]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_log_unitary_triangular_invariance : ∀ (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ), (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧ (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 → gramLog hd k (g * b) = gramLog hd k g + ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | exact GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorus
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorus
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem dense_forall_coord_ne_zero : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  intro n
  have h : {z : Fin n → ℂ | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ)) := by
    ext z
    simp
  rw [h]
  exact dense_pi Set.univ (fun _ _ => dense_compl_singleton 0)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AbsCoeffProdXLeOne
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem abs_coeff_prod_X_le_one {σ : Type} {n : ℕ} (w : Fin n → σ) (m : σ →₀ ℕ) :
    |(∏ j, X (w j) : MvPolynomial σ ℝ).coeff m| ≤ 1 := by
  classical
  have h : (∏ j, X (w j) : MvPolynomial σ ℝ) = monomial (∑ j, Finsupp.single (w j) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h, coeff_monomial]
  split_ifs <;> simp

theorem formPoly_sub_bound : ∀ (σ : Type) [Fintype σ] (n : ℕ) (a b : (Fin n → σ) → ℝ) (M : ℝ),
    (∀ w, |a w - b w| ≤ M) →
    (∀ m, |(formPoly n a).coeff m - (formPoly n b).coeff m| ≤ (Fintype.card σ : ℝ) ^ n * M) ∧
    ∀ c : σ → ℝ, |eval c (formPoly n a) - eval c (formPoly n b)| ≤ (∑ x, |c x|) ^ n * M := by
  intro σ _ n a b M h
  constructor
  · intro m
    simp only [formPoly, coeff_sum, coeff_C_mul]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m
            - b w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m|
        ≤ ∑ _w : Fin n → σ, M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul]
          calc _ ≤ |a w - b w| * 1 :=
                mul_le_mul_of_nonneg_left (abs_coeff_prod_X_le_one w m) (abs_nonneg _)
            _ ≤ M := by rw [mul_one]; exact h w
      _ = (Fintype.card σ : ℝ) ^ n * M := by
          simp
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * ∏ j, c (w j) - b w * ∏ j, c (w j)|
        ≤ ∑ w : Fin n → σ, (∏ j, |c (w j)|) * M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul, Finset.abs_prod, mul_comm]
          exact mul_le_mul_of_nonneg_left (h w) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = (∑ x, |c x|) ^ n * M := by
          rw [← Finset.sum_mul, Fintype.sum_pow]

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
open Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

def den (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g 0 0 + g 0 1 * a

def mob (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := (g 1 0 + g 1 1 * a) / den g a

def mobD (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g.det / den g a ^ 2

def mob1 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cons (mob (g (Fin.tail z)) (z 0)) (Fin.tail z)

def mob2 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 2) → ℂ) : Fin (d + 2) → ℂ :=
  Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 0))
    (Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 1)) (Fin.tail (Fin.tail z)))

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry {d : ℕ} (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (p q : Fin 2) :
    ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y := by
  have hg' : ∀ i j, ContDiffAt ℝ 2 (fun y' => g y' i j) y := fun i j =>
    ((ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg i j).differentiableOn y (Set.mem_univ _)).contDiffAt).restrict_scalars ℝ
  have hs : ∀ i j, ContDiffAt ℝ 2 (fun y' => star (g y' i j)) y := fun i j => by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp y (hg' i j)
    simpa [Function.comp_def] using h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  exact ((((hs 0 p).mul (hC 0 0)).add ((hs 1 p).mul (hC 1 0))).mul (hg' 0 q)).add
    ((((hs 0 p).mul (hC 0 1)).add ((hs 1 p).mul (hC 1 1))).mul (hg' 1 q))

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_xiPot {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → Matrix (Fin 2) (Fin 2) ℂ) (b : E → ℂ) (w₀ : E) (hpd : (H w₀).PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun w => H w p q) w₀) (hb : ContDiffAt ℝ 2 b w₀) :
    ContDiffAt ℝ 2 (fun w => xiPot (H w) (b w)) w₀ := by
  have hb' : ContDiffAt ℝ 2 (fun w => star (b w)) w₀ := by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp w₀ hb
    simpa [Function.comp_def] using h
  have h00 := hC 0 0
  have h01 := hC 0 1
  have h10 := hC 1 0
  have h11 := hC 1 1
  have hq : ContDiffAt ℝ 2 (fun w => herm2 (H w) ![1, b w] ![1, b w]) w₀ := by
    simp only [herm2, dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_one, one_mul, mul_one]
    fun_prop
  have hd : ContDiffAt ℝ 2 (fun w => (H w).det) w₀ := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hqr : ContDiffAt ℝ 2 (fun w => (herm2 (H w) ![1, b w] ![1, b w]).re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hq
  have hdr : ContDiffAt ℝ 2 (fun w => (H w).det.re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hd
  have hv : (![1, b w₀] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hp1 : 0 < herm2 (H w₀) ![1, b w₀] ![1, b w₀] := by
    exact hpd.dotProduct_mulVec_pos hv
  have hp2 : 0 < (H w₀).det := hpd.det_pos
  simp only [xiPot]
  exact (hqr.log (Complex.pos_iff.1 hp1).1.ne').neg.add (contDiffAt_const.mul (hdr.log (Complex.pos_iff.1 hp2).1.ne'))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBound
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcNorm_norm_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hz
  have h3 : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [← h2]
  rw [h3, Complex.norm_real]
  simp only [Complex.ofReal_re, Real.norm_eq_abs]
  exact abs_of_pos (by simpa using h1)

theorem fcNorm_arith {ne nw ns h₁ h₂ t u : ℝ} (hh₂ : 0 < h₂) (ht : 0 < t)
    (hnw : nw * h₂ = t) (hmain : ne * ne * h₂ * h₁ = t * u * ns) :
    (ne / nw) ^ 2 * h₁ = u * t⁻¹ * ns * h₂ := by
  have hnw' : nw = t / h₂ := by field_simp; exact hnw
  have e : (ne / (t / h₂)) ^ 2 * h₁ = (ne * ne * h₂ * h₁) * h₂ / t ^ 2 := by
    field_simp
  rw [hnw', e, hmain]
  field_simp

theorem fcNorm : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  intro p q A A' S H₁ H₂ hH₁ hH₂ hS h
  have hd₁ : 0 < H₁.det := hH₁.det_pos
  have hd₂ : 0 < H₂.det := hH₂.det_pos
  have hn₁ := fcNorm_norm_of_pos hd₁
  have hn₂ := fcNorm_norm_of_pos hd₂
  have hr₂ : 0 < H₂.det.re := (Complex.lt_def.mp hd₂).1
  have hc : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hnc : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  have hAstar : (A.map star)ᵀ = Aᴴ := by ext i j; simp [conjTranspose_apply]
  have hB'H : (A'.map star)ᴴ = A'ᵀ := by ext i j; simp [conjTranspose_apply]
  have hT : Aᴴ * H₁ᵀ * A - A'ᵀ * H₂ * A'.map star = (2 * Complex.I) • Sᵀ := by
    have := congrArg Matrix.transpose h
    rw [transpose_sub, transpose_transpose, transpose_smul, transpose_mul, transpose_mul,
      transpose_transpose, hAstar, ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨B', hB'⟩ : ∃ B', B' = A'.map star := ⟨_, rfl⟩
  rw [← hB'] at hT hB'H
  obtain ⟨E, hE⟩ : ∃ E, E = fromRows B' A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = fromCols (-(A'ᵀ * H₂)) (Aᴴ * H₁ᵀ) := ⟨_, rfl⟩
  have hME : M * E = (2 * Complex.I) • Sᵀ := by
    rw [hM, hE, fromCols_mul_fromRows, ← hT, Matrix.neg_mul]
    abel
  have hMD : M = Eᴴ * fromBlocks (-H₂) 0 0 H₁ᵀ := by
    rw [hM, hE, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, hB'H]
    simp
  have hdetME : M.det * E.det = (2 * Complex.I) ^ (q + p) * S.det := by
    rw [← det_mul, hME, det_smul, det_transpose]
    simp
  have hne : (2 * Complex.I) ^ (q + p) * S.det ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hS
  have hMu : IsUnit M := (isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (hdetME ▸ hne)))
  have hEdet : E.det ≠ 0 := right_ne_zero_of_mul (hdetME ▸ hne)
  have hEu : IsUnit E := (isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEdet)
  have hmain : ‖E.det‖ * ‖E.det‖ * H₂.det.re * H₁.det.re
      = (2 : ℝ) ^ q * 2 ^ p * ‖S.det‖ := by
    have h1 := congrArg norm hdetME
    rw [hMD, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_neg, det_transpose] at h1
    simp only [norm_mul, norm_pow, hnc, norm_star, norm_neg, norm_one, one_pow, one_mul, hn₁, hn₂,
      Fintype.card_fin] at h1
    rw [pow_add] at h1
    linarith
  have hSu : IsUnit (Sᵀ).det := by
    rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hS
  have hSinv : Sᵀ * (Sᵀ)⁻¹ = 1 := mul_nonsing_inv _ hSu
  have hH₂u : IsUnit H₂.det := isUnit_iff_ne_zero.mpr hd₂.ne'
  have hH₂inv : H₂ * H₂⁻¹ = 1 := mul_nonsing_inv _ hH₂u
  have hH₂inv' : H₂⁻¹ * H₂ = 1 := nonsing_inv_mul _ hH₂u
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (Sᵀ)⁻¹ * A'ᵀ := ⟨_, rfl⟩
  rw [← hΦ]
  have hEΦ : E * Φ = fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have hMi : M⁻¹ * M = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hMu)
    have hkey : M * (E * Φ)
        = M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
      rw [← Matrix.mul_assoc, hME, hΦ, Matrix.smul_mul, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]
      rw [hM, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.mul_smul, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hH₂inv, Matrix.mul_one]
    calc E * Φ = M⁻¹ * (M * (E * Φ)) := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
      _ = M⁻¹ * (M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)) := by
        rw [hkey]
      _ = _ := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
  rw [hE, fromRows_mul] at hEΦ
  obtain ⟨hBΦ, hAΦ⟩ := fromRows_inj hEΦ
  have hrA : A.rank = p := by
    obtain ⟨X, hXd⟩ : ∃ X, X = E⁻¹ * fromRows (0 : Matrix (Fin q) (Fin p) ℂ)
        (1 : Matrix (Fin p) (Fin p) ℂ) := ⟨_, rfl⟩
    have hX : E * X = fromRows 0 1 := by
      rw [hXd, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hEdet), Matrix.one_mul]
    rw [hE, fromRows_mul] at hX
    obtain ⟨-, hX2⟩ := fromRows_inj hX
    have h1 := rank_mul_le_left A X
    rw [hX2, rank_one, Fintype.card_fin] at h1
    have h2 := rank_le_card_height A
    rw [Fintype.card_fin] at h2
    omega
  have hw : (B' * Φ).det * H₂.det = (-(2 * Complex.I)) ^ q := by
    have e : (2 * Complex.I) • (-1 : Matrix (Fin q) (Fin q) ℂ) = (-(2 * Complex.I)) • 1 := by simp
    rw [← det_mul, hBΦ, Matrix.smul_mul, Matrix.neg_mul, hH₂inv', e, det_smul, det_one,
      Fintype.card_fin, mul_one]
  have hwne : (B' * Φ).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact pow_ne_zero _ (neg_ne_zero.mpr hc) hw.symm
  have hrΦ : Φ.rank = q := by
    have h1 := rank_mul_le_right B' Φ
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hwne)),
      Fintype.card_fin] at h1
    have h2 := rank_le_card_width Φ
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨hy, -, hN⟩ := fcIndep p q A Φ hAΦ hrA hrΦ
  have hN' := hN B'
  rw [← hE] at hN'
  refine ⟨hAΦ, hrA, hrΦ, ?_⟩
  have hq : (fromRows Φᴴ A).det / (Φᴴ * Φ).det = E.det / (B' * Φ).det := by
    field_simp
    linear_combination -hN'
  have hnw : ‖(B' * Φ).det‖ * H₂.det.re = (2 : ℝ) ^ q := by
    have := congrArg norm hw
    simpa [hn₂, hnc] using this
  rw [hq, norm_div, inv_pow]
  have hfin := fcNorm_arith (ne := ‖E.det‖) (ns := ‖S.det‖) (h₁ := H₁.det.re) (u := (2:ℝ)^p) hr₂
    (by positivity) hnw hmain
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBoundStatement
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_period_determinant : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.fcNorm | exact GlobalTheory.CompanionTheory.Ar.Flat.fcNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.fcNorm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SubframeDetLogGrowth
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

section SlopeTestRemainingChoices

open scoped ComplexOrder MatrixOrder

variable {g k : ℕ}

theorem subframe_map_posSemidef {A : Matrix (Fin g) (Fin g) ℝ} (h : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hH : (A.map Complex.ofReal).IsHermitian :=
    h.isHermitian.map _ (fun x => by simp [Complex.conj_ofReal])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)
  have hu := h.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hv := h.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial] at hu hv
  have key : (star x ⬝ᵥ (A.map Complex.ofReal) *ᵥ x).re =
      ∑ i, ((x i).re * ∑ j, A i j * (x j).re + (x i).im * ∑ j, A i j * (x j).im) := by
    simp only [dotProduct, mulVec, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.re_sum, Complex.im_sum,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [RCLike.im_to_complex] at him
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  rw [key, Finset.sum_add_distrib]
  exact add_nonneg hu hv

theorem subframe_inv_bounds (Y : Matrix (Fin g) (Fin g) ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (h1 : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (h2 : (D • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) :
    D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ (Y⁻¹).map Complex.ofReal ∧
      (Y⁻¹).map Complex.ofReal ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  have hmap : ∀ {P Q : Matrix (Fin g) (Fin g) ℝ}, P ≤ Q →
      P.map Complex.ofReal ≤ Q.map Complex.ofReal := by
    intro P Q hPQ
    rw [Matrix.le_iff] at hPQ ⊢
    have := subframe_map_posSemidef hPQ
    rwa [Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b)] at this
  have hone : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℝ)).map Complex.ofReal =
      t • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t; ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Complex.real_smul]
  have hc1 : (c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hle1 : c • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y := Matrix.le_iff.mpr h1
  have hle2 : Y ≤ D • (1 : Matrix (Fin g) (Fin g) ℝ) := Matrix.le_iff.mpr h2
  have hY : Y.PosDef := GlobalTheory.posDef_of_le hc1 hle1
  have hlo : D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y⁻¹ :=
    GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hY hD hle2
  have hhi : Y⁻¹ ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) := by
    have := GlobalTheory.inv_le_inv_of_posDef_of_le hc1 hle1
    rwa [GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one hc.ne', inv_one] at this
  refine ⟨?_, ?_⟩
  · have := hmap hlo
    rwa [hone] at this
  · have := hmap hhi
    rwa [hone] at this

theorem subframe_det_bounds (P : Matrix (Fin g) (Fin k) ℂ) (A : Matrix (Fin g) (Fin g) ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (h1 : a • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ A)
    (h2 : A ≤ b • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    a ^ k * (Pᴴ * P).det.re ≤ (Pᴴ * A * P).det.re ∧
      (Pᴴ * A * P).det.re ≤ b ^ k * (Pᴴ * P).det.re := by
  have hA : A.PosSemidef := GlobalTheory.posSemidef_of_le (Matrix.PosSemidef.one.smul ha) h1
  have hPP : (Pᴴ * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
  have hsm : ∀ t : ℝ, Pᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * P = t • (Pᴴ * P) := by
    intro t; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hlo : a • (Pᴴ * P) ≤ Pᴴ * A * P := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h1 P
    rwa [hsm] at this
  have hhi : Pᴴ * A * P ≤ b • (Pᴴ * P) := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h2 P
    rwa [hsm] at this
  have hdetsm : ∀ t : ℝ, ((t • (Pᴴ * P)).det).re = t ^ k * ((Pᴴ * P).det).re := by
    intro t
    have he : t • (Pᴴ * P) = (t : ℂ) • (Pᴴ * P) := by
      ext i j; simp [Complex.real_smul]
    rw [he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  refine ⟨?_, ?_⟩
  · have := GlobalTheory.pow_mul_re_det_le_of_smul_le hPP ha hlo
    simpa [Fintype.card_fin] using this
  · have := GlobalTheory.re_det_le_re_det_of_posSemidef_of_le (hA.conjTranspose_mul_mul_same P) hhi
    rw [RCLike.re_to_complex, RCLike.re_to_complex, hdetsm] at this
    exact this

theorem subframe_gram_posDef (F : Matrix (Fin g) (Fin k) ℂ) (h : F.rank = k) :
    ((F.map star)ᴴ * F.map star).PosDef := by
  have hr : (F.map star).rank = k := by
    have he : F.map star = (Fᴴ)ᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he, Matrix.rank_transpose, Matrix.rank_conjTranspose, h]
  have hr' : Module.finrank ℂ (LinearMap.range (F.map star).mulVecLin) = k := hr
  have hsum := LinearMap.finrank_range_add_finrank_ker (F.map star).mulVecLin
  rw [Module.finrank_fin_fun, hr'] at hsum
  have hker0 : Module.finrank ℂ (LinearMap.ker (F.map star).mulVecLin) = 0 := by omega
  have hbot : LinearMap.ker (F.map star).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective (F.map star).mulVec := by
    intro v w hvw
    have h0 : (F.map star).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have := (Matrix.ker_mulVecLin_eq_bot_iff.mp hbot) (v - w) h0
    exact sub_eq_zero.mp this
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

theorem subframe_continuous_det :
    Continuous fun M : Matrix (Fin g) (Fin k) ℂ => ((Mᵀ * M.map star).det).re := by
  exact Complex.continuous_re.comp
    ((continuous_id.matrix_transpose.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_det)

end SlopeTestRemainingChoices

theorem subframe_det_log_growth : ∀ (g k : ℕ) (X : Type) [TopologicalSpace X] (K : Set X), IsCompact K → ∀ (F : X → Matrix (Fin g) (Fin k) ℂ), ContinuousOn F K → (∀ x ∈ K, (F x).rank = k) → ∀ c C : ℝ, 0 < c → ∃ C' : ℝ, 0 < C' ∧ ∀ x ∈ K, ∀ (Y : Matrix (Fin g) (Fin g) ℝ) (r : ℝ), 1 ≤ r → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ((C * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → (let d := (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re; d ≤ C' ∧ 1 ≤ C' * r ^ k * d) := by
  intro g k X _ K hK F hF hrank c C hc
  by_cases hne : K.Nonempty
  swap
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hT : ∀ x, ((F x).map star)ᴴ = (F x)ᵀ := by
    intro x; ext i j; simp [Matrix.conjTranspose_apply]
  have hGc : ContinuousOn (fun x => (((F x)ᵀ * (F x).map star).det).re) K :=
    subframe_continuous_det.comp_continuousOn hF
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGc
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hGc
  have hGpos : ∀ x ∈ K, 0 < (((F x)ᵀ * (F x).map star).det).re := by
    intro x hx
    have hpd := subframe_gram_posDef (F x) (hrank x hx)
    rw [hT] at hpd
    have := GlobalTheory.re_det_pos_of_posDef hpd
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, m = (((F x₀)ᵀ * (F x₀).map star).det).re := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact hGpos x₀ hx₀K
  have hA0 : 0 ≤ c⁻¹ ^ k * |M| := mul_nonneg (pow_nonneg (inv_nonneg.2 hc.le) k) (abs_nonneg M)
  have hB0 : 0 ≤ |C| ^ k / m := div_nonneg (pow_nonneg (abs_nonneg C) k) hmpos.le
  refine ⟨c⁻¹ ^ k * |M| + |C| ^ k / m + 1, by linarith, ?_⟩
  intro x hx Y r hr h1 h2 d
  have hd : d = (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re := rfl
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · subst hg0
    have hk : k = 0 := by
      have := Matrix.rank_le_height (F x)
      rw [hrank x hx] at this
      omega
    subst hk
    have hd1 : d = 1 := by
      rw [hd, Matrix.det_isEmpty, Complex.one_re]
    rw [hd1]
    simp only [pow_zero, one_mul, mul_one] at hA0 hB0 ⊢
    refine ⟨?_, ?_⟩ <;> linarith
  · have hdiag := (h1.add h2).diag_nonneg (i := ⟨0, hgpos⟩)
    have hcr : c ≤ C * r := by
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq] at hdiag
      linarith
    have hCr : 0 < C * r := lt_of_lt_of_le hc hcr
    have hr0 : 0 < r := by linarith
    have hC : 0 < C := by nlinarith
    have hinv := subframe_inv_bounds Y hc hCr h1 h2
    have hb := subframe_det_bounds ((F x).map star) ((Y⁻¹).map Complex.ofReal)
      (inv_nonneg.2 hCr.le) hinv.1 hinv.2
    rw [hT] at hb
    obtain ⟨hlo, hhi⟩ := hb
    have hGx_le : (((F x)ᵀ * (F x).map star).det).re ≤ |M| := by
      have := hM x hx
      simp only [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) (le_trans this (le_abs_self M))
    have hGx_ge : m ≤ (((F x)ᵀ * (F x).map star).det).re := by
      have := isMinOn_iff.mp hx₀ x hx
      rw [hm]; exact this
    rw [hd]
    generalize (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re = D at hlo hhi ⊢
    generalize (((F x)ᵀ * (F x).map star).det).re = Gx at hlo hhi hGx_le hGx_ge
    have hpk : 0 < (C * r)⁻¹ ^ k := pow_pos (inv_pos.2 hCr) k
    refine ⟨?_, ?_⟩
    · have h3 : c⁻¹ ^ k * Gx ≤ c⁻¹ ^ k * |M| :=
        mul_le_mul_of_nonneg_left hGx_le (pow_nonneg (inv_nonneg.2 hc.le) k)
      linarith
    · have hDlo : (C * r)⁻¹ ^ k * m ≤ D := le_trans (mul_le_mul_of_nonneg_left hGx_ge hpk.le) hlo
      have hone : |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) = 1 := by
        rw [abs_of_pos hC, inv_pow, mul_pow]
        field_simp
      calc (1 : ℝ) = |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) := hone.symm
        _ ≤ (c⁻¹ ^ k * |M| + |C| ^ k / m + 1) * r ^ k * D := by
          apply mul_le_mul _ hDlo (mul_nonneg hpk.le hmpos.le)
          · exact mul_nonneg (by linarith) (pow_nonneg hr0.le k)
          · exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0.le k)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem xiPot_logSin_change_of_frame : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  intro G g hG hg
  have herm2_conj_lemma : ∀ (u w : Fin 2 → ℂ), herm2 (gᴴ * G * g) u w = herm2 G (g *ᵥ u) (g *ᵥ w) := by
    intro u w
    unfold herm2
    rw [← Matrix.mulVec_mulVec w (gᴴ * G) g, ← Matrix.mulVec_mulVec (g *ᵥ w) gᴴ G,
      Matrix.dotProduct_mulVec (star u) gᴴ, Matrix.star_mulVec g u]
  have herm2_smul_lemma_2 : ∀ (s t : ℂ) (u w : Fin 2 → ℂ),
      herm2 G (s • u) (t • w) = star s * t * herm2 G u w := by
    intro s t u w
    have hsu : star (s • u) = star s • star u := by
      ext i
      simp [star_mul']
    unfold herm2
    rw [Matrix.mulVec_smul, hsu, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have ratio_lemma_3 : ∀ (x y p q r : ℝ), x ≠ 0 → y ≠ 0 →
      (x * y * r) ^ 2 / (x ^ 2 * p * (y ^ 2 * q)) = r ^ 2 / (p * q) := by
    intro x y p q r hx hy
    rw [show (x * y * r) ^ 2 = r ^ 2 * (x ^ 2 * y ^ 2) by ring,
      show x ^ 2 * p * (y ^ 2 * q) = (p * q) * (x ^ 2 * y ^ 2) by ring]
    exact mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
  have hdet : g.det ≠ 0 := hg.ne_zero
  have hv : ∀ b : ℂ, (![1, b] : Fin 2 → ℂ) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    simp at h0
  have hre : ∀ b : ℂ, 0 < (herm2 G ![1, b] ![1, b]).re := fun b =>
    (Complex.pos_iff.1 (hG.dotProduct_mulVec_pos (hv b))).1
  have hdG : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hcc : ∀ c : ℂ, star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hre_mul : ∀ c z : ℂ, (star c * c * z).re = ‖c‖ ^ 2 * z.re := by
    intro c z
    rw [hcc, Complex.re_ofReal_mul]
  have hc : ∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → g *ᵥ ![1, a] =
      (g 0 0 + g 0 1 * a) • ![1, (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)] := by
    intro a ha
    have ha' : g 0 0 + a * g 0 1 ≠ 0 := by rwa [mul_comm a]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  refine ⟨hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)), ?_, ?_⟩
  · intro a ha
    unfold xiPot
    rw [herm2_conj_lemma, hc a ha, herm2_smul_lemma_2, hre_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose,
      show star g.det * G.det * g.det = star g.det * g.det * G.det by ring, hre_mul,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)) (hre _).ne',
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdet)) hdG.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  · intro a₀ a₁ h₀ h₁
    unfold logSin
    rw [herm2_conj_lemma, herm2_conj_lemma, herm2_conj_lemma, hc a₀ h₀, hc a₁ h₁, herm2_smul_lemma_2,
      herm2_smul_lemma_2, herm2_smul_lemma_2, hre_mul, hre_mul, norm_mul, norm_mul, norm_star,
      ratio_lemma_3 _ _ _ _ _ (norm_ne_zero_iff.mpr h₀) (norm_ne_zero_iff.mpr h₁)]

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_mobius_transform : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | exact GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame <;> assumption)
end
end
