module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SharedDedup_Exists_equivariant_proj_of_le_sum_irreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SlashCocycle

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

theorem cmp_det (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v) _).symm

theorem det_mul_apply (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v * (h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [← cmp_det, ← cmp_det, ← cmp_det, map_mul, map_mul, Units.val_mul]

theorem det_inv_apply (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      ((h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v)⁻¹ := by
  rw [← cmp_det, ← cmp_det, map_inv, map_inv, Units.val_inv_eq_inv_val]

theorem denom_cmp_mul (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (z : ℍ) :
    denom (cmp v h * cmp v h') z = denom (cmp v h) ((cmp v h' • z : ℍ) : ℂ) * denom (cmp v h') z := by
  have hp : 0 < ((cmp v h').det : ℝ) := by rw [cmp_det]; exact hh' v
  rw [denom_cocycle_σ, σ, if_pos hp]
  rfl

theorem act_mul (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (z : Hn F) : act (h * h') z = act h (act h' z) := by
  funext v
  simp only [act, map_mul]
  exact mul_smul _ _ _

theorem act_one (z : Hn F) : act (1 : GL (Fin 2) (InfinitePlace F → ℝ)) z = z := by
  funext v
  simp only [act, map_one]
  exact one_smul _ _

theorem hilbertSlashUnnormalized_mul (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (f : Hn F → ℂ) :
    sl0 k (h * h') f = sl0 k h' (sl0 k h f) := by
  funext z
  simp only [sl0, act_mul, map_mul]
  simp only [act, denom_cmp_mul _ h h' hh', Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

theorem hilbertSlashUnnormalized_one (k : ℕ) (f : Hn F → ℂ) : sl0 k 1 f = f := by
  funext z
  simp [sl0, act_one, denom_one]

theorem hilbertSlashUnnormalized_const_mul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (c : ℂ) (f : Hn F → ℂ) (z : Hn F) :
    sl0 k h (fun w => c * f w) z = c * sl0 k h f z := by
  simp only [sl0]; ring

theorem slash_cocycle : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (f : Hn F → ℂ), Pos h → Pos h' → Pos (h * h') ∧ Pos h⁻¹ ∧ sl0 k (h * h') f = sl0 k h' (sl0 k h f) ∧ sl k (h * h') f = sl k h' (sl k h f) ∧ sl0 k 1 f = f ∧ sl k 1 f = f := by
  intro F _ _ k h h' f hh hh'
  refine ⟨fun v => ?_, fun v => ?_, hilbertSlashUnnormalized_mul k h h' hh' f, ?_, hilbertSlashUnnormalized_one k f, ?_⟩
  · rw [det_mul_apply]; exact mul_pos (hh v) (hh' v)
  · rw [det_inv_apply]; exact inv_pos.mpr (hh v)
  · funext z
    have hprod : (∏ v, |((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) =
        (∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) *
          ∏ v, |(h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
      simp only [det_mul_apply, abs_mul, Finset.prod_mul_distrib]
    have hsl : sl k h f = fun w => ((((∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) * sl0 k h f w := rfl
    simp only [sl]
    rw [hsl, hilbertSlashUnnormalized_const_mul, hilbertSlashUnnormalized_mul k h h' hh' f, hprod,
      Real.mul_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _) (Finset.prod_nonneg fun v _ => abs_nonneg _)]
    push_cast
    ring
  · funext z
    simp [sl, hilbertSlashUnnormalized_one]

end GlobalTheory.HilbertThetaSeries.SlashCocycle
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.FormLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem symm_of_evenPos {G : Matrix κ κ ℤ} (hG : EvenPos G) : Gᵀ = G := by
  have h := hG.1.1
  ext i j
  have := congrFun (congrFun h i) j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply] at this
  simp only [Matrix.transpose_apply]
  exact_mod_cast this

theorem bf_symm {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : BF G x y = BF G y x := by
  unfold BF
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.transpose_map, hG]

theorem bf_add_left (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G (x + y) z = BF G x z + BF G y z := by
  unfold BF; rw [add_dotProduct]

theorem bf_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  unfold BF; rw [Matrix.mulVec_add, dotProduct_add]

theorem bf_smul_left (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G (a • x) y = a * BF G x y := by
  unfold BF; rw [smul_dotProduct, smul_eq_mul]

theorem bf_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  unfold BF; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem qf_add {G : Matrix κ κ ℤ} (hG : Gᵀ = G) (x y : κ → F) : QF G (x + y) = QF G x + BF G x y + QF G y := by
  unfold QF
  rw [bf_add_left, bf_add_right, bf_add_right, bf_symm hG y x]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem mem_LL {x : κ → F} : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]

theorem intCast_isIntegral (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem bf_int (G : Matrix κ κ ℤ) {x y : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) :
    IsIntegral ℤ (BF G x y) := by
  unfold BF
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  exact IsIntegral.sum _ fun i _ => (hx i).mul (IsIntegral.sum _ fun j _ => (intCast_isIntegral _).mul (hy j))

theorem trace_int {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  have := Algebra.isIntegral_trace (L := ℚ) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  exact ⟨n, by rw [← hn]; simp⟩

theorem qf_single (G : Matrix κ κ ℤ) (i : κ) (c : F) : QF G (Pi.single i c) = c * ((G i i : F) * c) / 2 := by
  simp [QF, BF, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem qf_int {G : Matrix κ κ ℤ} (hG : EvenPos G) {x : κ → F} (hx : ∀ i, IsIntegral ℤ (x i)) : IsIntegral ℤ (QF G x) := by
  have hs : Gᵀ = G := symm_of_evenPos hG
  have hsingle : ∀ i, IsIntegral ℤ (QF G (Pi.single i (x i))) := by
    intro i
    obtain ⟨m, hm⟩ := hG.2 i
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : QF G (Pi.single i (x i)) = (m : F) * x i * x i := by
      rw [qf_single, hm]; push_cast; field_simp; ring
    rw [this]
    exact ((intCast_isIntegral m).mul (hx i)).mul (hx i)
  have hvi : ∀ (s : Finset κ) (j : κ), IsIntegral ℤ ((∑ i ∈ s, Pi.single i (x i) : κ → F) j) := by
    intro s j
    rw [Finset.sum_apply]
    exact IsIntegral.sum _ fun i _ => by
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  have key : ∀ s : Finset κ, IsIntegral ℤ (QF G (∑ i ∈ s, Pi.single i (x i))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [QF, BF] using (isIntegral_zero : IsIntegral ℤ (0 : F))
    · intro i s hi ih
      rw [Finset.sum_insert hi, qf_add hs]
      refine ((hsingle i).add (bf_int G ?_ (hvi s))).add ih
      intro j
      by_cases h : j = i
      · subst h; simpa using hx j
      · simp [Pi.single_apply, h, isIntegral_zero]
  simpa [Finset.univ_sum_single] using key Finset.univ

theorem et_props (x y : F) : et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧
    (IsIntegral ℤ x → et x = 1) := by
  have h0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hiff : et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n := by
    unfold et
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        apply mul_left_cancel₀ h0
        rw [hn]; push_cast; ring
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn]; push_cast; ring⟩
  refine ⟨?_, ?_, hiff, fun hx => hiff.mpr (trace_int hx)⟩
  · unfold et; rw [map_add (f := _), Rat.cast_add, mul_add, Complex.exp_add]
  · unfold et
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ) =
        ((2 * Real.pi * (Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]

end GlobalTheory.HilbertThetaSeries.FormLat


open GlobalTheory.HilbertThetaSeries.FormLat in
theorem GlobalTheory.HilbertThetaSeries.formLatticeProps : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  intro F _ _ κ _ _ G hG
  have hs : Gᵀ = G := symm_of_evenPos hG
  refine ⟨fun x y => ⟨bf_symm hs x y, qf_add hs x y⟩, fun a x y => ⟨bf_smul_left G a x y, ?_, ?_⟩,
    bf_add_left G, fun x hx => ⟨qf_int hG (mem_LL.mp hx), fun y hy => bf_int G (mem_LL.mp hx) (mem_LL.mp hy)⟩,
    fun x => mem_LL, fun a x => ?_, et_props, ?_⟩
  · unfold QF; rw [bf_smul_left, bf_smul_right]; ring
  · unfold QF BF; rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  · unfold aL
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · intro y hy l hl
    exact trace_int (bf_int G (mem_LL.mp hy) (mem_LL.mp hl))

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenPos_gramForm_integral_lattice_properties : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x y : κ → F, BF G x y = BF G y x ∧ QF G (x + y) = QF G x + BF G x y + QF G y) ∧ (∀ (a : F) (x y : κ → F), BF G (a • x) y = a * BF G x y ∧ QF G (a • x) = a ^ 2 * QF G x ∧ QF G (-x) = QF G x) ∧ (∀ x y z : κ → F, BF G (x + y) z = BF G x z + BF G y z) ∧ (∀ x ∈ LL F κ, IsIntegral ℤ (QF G x) ∧ ∀ y ∈ LL F κ, IsIntegral ℤ (BF G x y)) ∧ (∀ x : κ → F, x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i)) ∧ (∀ (a : F) (x : κ → F), x ∈ aL κ a ↔ ∃ l ∈ LL F κ, x = a • l) ∧ (∀ x y : F, et (x + y) = et x * et y ∧ ‖et x‖ = 1 ∧ (et x = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F x = n) ∧ (IsIntegral ℤ x → et x = 1)) ∧ LL F κ ≤ dualL F G := by
  first | exact @GlobalTheory.HilbertThetaSeries.formLatticeProps | exact GlobalTheory.HilbertThetaSeries.formLatticeProps | (intros; apply GlobalTheory.HilbertThetaSeries.formLatticeProps <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.RatSlash

variable {F : Type} [Field F] [NumberField F]

theorem cmp_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).toMonoidHom t) * cmp v h := by
  rw [map_mul]
  congr 1
  ext i j
  simp [cmp, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det =
      (t : InfinitePlace F → ℝ) ^ 2 * (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_mul]

theorem unit_ne (t : (InfinitePlace F → ℝ)ˣ) (v : InfinitePlace F) : (t : InfinitePlace F → ℝ) v ≠ 0 := fun h0 => by
  have := congrFun t.mul_inv v
  simp [h0] at this

theorem denom_scalar_mul (u : ℝˣ) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) z = ((u : ℝ) : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl_scalar_mul {k : ℕ} (hk : Even k) (f : Hn F → ℂ) (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f := by
  obtain ⟨m, rfl⟩ := hk
  funext z
  have hact : act (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) z = act h z := by
    unfold act
    funext v
    rw [cmp_scalar_mul, mul_smul, UpperHalfPlane.glScalar_smul]
  have hdet : ∏ v, |((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| =
      (∏ v, (t : InfinitePlace F → ℝ) v) ^ 2 * ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
    rw [det_scalar_mul, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    simp [abs_mul, sq_abs]
  have hden : ∏ v, UpperHalfPlane.denom (cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h)) (z v) =
      ((∏ v, (t : InfinitePlace F → ℝ) v : ℝ) : ℂ) * ∏ v, UpperHalfPlane.denom (cmp v h) (z v) := by
    simp_rw [cmp_scalar_mul, denom_scalar_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    simp
  have hP : (∏ v, (t : InfinitePlace F → ℝ) v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => unit_ne t v)
  have hQ : 0 ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
    Finset.prod_nonneg (fun v _ => abs_nonneg _)
  have hexp : (((m + m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by
    push_cast
    ring
  unfold sl sl0
  rw [hact, hdet, hden, Real.mul_rpow (by positivity) hQ, hexp, Real.rpow_natCast, ← pow_mul]
  set P := ∏ v, (t : InfinitePlace F → ℝ) v
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  rw [mul_inv, mul_pow, inv_pow (P : ℂ)]
  field_simp
  ring

variable [IsTotallyReal F]

theorem ofReal_rhom (v : InfinitePlace F) (x : F) : ((rhom x v : ℝ) : ℂ) = v.embedding x :=
  InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem rhom_apply (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  unfold rhom reAt
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem ofReal_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_apply, ofReal_rhom]


variable (F) in
def embEquiv : InfinitePlace F ≃ (F →+* ℂ) where
  toFun v := v.embedding
  invFun φ := InfinitePlace.mk φ
  left_inv v := InfinitePlace.mk_embedding v
  right_inv φ := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∏ v : InfinitePlace F, v.embedding x = ∏ φ : F →+* ℂ, φ x :=
    Equiv.prod_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∏ φ : F →+* ℂ, φ x = ∏ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.prod_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast]

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Equiv.sum_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.sum_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← trace_eq_sum_embeddings ℂ, eq_ratCast]

theorem det_toInf (γ : GL (Fin 2) F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
  rw [RingHom.map_det]; rfl

theorem toInf_scalar (η : Fˣ) : toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η) := by
  ext i j v
  simp [toInf, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem rat_slash : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  intro F _ _ _ k f
  refine ⟨rhom_apply, fun γ => ⟨?_, ?_⟩, fun hk t h hh => ⟨?_, sl_scalar_mul hk f t h⟩, toInf_scalar,
    fun x => ⟨prod_reAt x, sum_reAt x⟩⟩
  · unfold Pos TP
    rw [det_toInf]
    simp only [rhom_apply]
  · funext z
    unfold sl
    rw [det_toInf]
    simp only [rhom_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.abs_prod, prod_reAt]
  · unfold Pos at hh ⊢
    intro v
    rw [det_scalar_mul]
    have h1 := unit_ne t v
    have h2 := hh v
    simp only [Pi.mul_apply, Pi.pow_apply]
    positivity

end GlobalTheory.HilbertThetaSeries.RatSlash

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_slash_rational_matrix_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | exact GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | (intros; apply GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.KMem

variable {F : Type} [Field F] [NumberField F]

theorem mem_Ohat_iff {x : Af F} : x ∈ Ohat F ↔ ∀ w, Valued.v (pLoc F w x) ≤ 1 := by
  simp only [Ohat, Subring.mem_iInf, Subring.mem_comap, ValuationSubring.mem_toSubring,
    HeightOneSpectrum.mem_adicCompletionIntegers]

theorem eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = a * b := h.symm
    _ ≤ a * 1 := by gcongr
    _ = a := mul_one a

theorem det_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (A : Matrix (Fin 2) (Fin 2) K) (h : ∀ i j, v (A i j) ≤ 1) : v A.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (v.map_sub _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
  · exact mul_le_one' (h 0 0) (h 1 1)
  · exact mul_le_one' (h 0 1) (h 1 0)

theorem det_mul_det_inv (g : GL (Fin 2) (Af F)) :
    (g : Matrix (Fin 2) (Fin 2) (Af F)).det * ((g⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem v_det (g : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (h : ∀ i j, Valued.v (pLoc F w (g.val i j)) ≤ 1) :
    Valued.v (pLoc F w g.val.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact det_le _ _ h

theorem mem_KLev_iff (u : GL (Fin 2) (Af F)) :
    u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1 := by
  rw [mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    have ha' : ∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1 := fun w i j => mem_Ohat_iff.1 (ha i j) w
    have hb' : ∀ w i j, Valued.v (pLoc F w ((u⁻¹ : GL (Fin 2) (Af F)).val i j)) ≤ 1 :=
      fun w i j => mem_Ohat_iff.1 (hb i j) w
    refine ⟨ha', fun w => eq_one_of_mul (v_det u w (ha' w)) (v_det _ w (hb' w)) ?_⟩
    rw [← Valuation.map_mul, ← map_mul, det_mul_det_inv, map_one, Valuation.map_one]
  · rintro ⟨ha, hd⟩
    have hinv : ∀ w, Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      intro w
      have h1 : Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det u : (Af F)ˣ) : Af F)) *
          Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
      rw [Matrix.GeneralLinearGroup.val_det_apply, hd w, one_mul] at h1
      exact h1
    have hO : ∀ a b, u a b ∈ Ohat F := fun a b => mem_Ohat_iff.2 fun w => ha w a b
    refine ⟨hO, fun a b => mem_Ohat_iff.2 fun w => ?_, fun a b => ⟨u a b - (1 : Matrix (Fin 2) (Fin 2) (Af F)) a b, ?_, by simp⟩⟩
    · rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit,
        Matrix.smul_apply, smul_eq_mul, map_mul, Valuation.map_mul, hinv w, one_mul, Matrix.adjugate_fin_two]
      fin_cases a <;> fin_cases b <;> simp [ha w]
    · refine sub_mem (hO a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

end GlobalTheory.HilbertThetaSeries.KMem


open GlobalTheory.HilbertThetaSeries.KMem in
theorem GlobalTheory.HilbertThetaSeries.kMem : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  intro F _ _
  refine ⟨mem_KLev_iff, fun u x hu hx => ⟨?_, ?_⟩, fun w g hg => ?_, fun x w => ?_, fun x => ?_⟩
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [aff, (hu w).le, hx w]
    · simp [aff, Matrix.det_fin_two, hu w]
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, (hu w).le]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, hu w]
  · obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hg
    have hk : ∀ i j, Valued.v ((k.val i j : w.adicCompletionIntegers F) : w.adicCompletion F) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (k.val i j).2
    refine (mem_KLev_iff _).2 ⟨fun v i j => ?_, fun v => ?_⟩
    · change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val i j) ≤ 1
      by_cases hv : v = w
      · subst hv; rw [pLoc_locGL]; exact hk i j
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    · rw [RingHom.map_det]
      change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val.det) = 1
      by_cases hv : v = w
      · subst hv
        rw [pLoc_locGL]
        have e : ((Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k).val).det =
            (((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          rw [Matrix.GeneralLinearGroup.val_det_apply]
          exact ((v.adicCompletionIntegers F).subtype.map_det k.val).symm
        rw [e]
        refine eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ).val.2)
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletionIntegers F)ˣ).val.2) ?_
        rw [← Valuation.map_mul]
        have h := congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) (Matrix.GeneralLinearGroup.det k).mul_inv
        exact (congrArg Valued.v h).trans (Valuation.map_one _)
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.det_one, Valuation.map_one]
  · exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  · constructor
    · intro h
      obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro h w
      have e : x = algebraMap (𝓞 F) F ⟨x, h⟩ := rfl
      rw [e]
      exact HeightOneSpectrum.valuation_le_one w _

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  first | exact @GlobalTheory.HilbertThetaSeries.kMem | exact GlobalTheory.HilbertThetaSeries.kMem | (intros; apply GlobalTheory.HilbertThetaSeries.kMem <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible
open CategoryTheory
open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

theorem exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := _root_.DedupShared.dedup_exists_equivariant_proj_of_le_sum_irreducible_7 (M := M) (O := O) act V hVst hV

theorem exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩

end GlobalTheory.BorelCoh
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos
open NumberField GlobalTheory.BorelCoh UpperTheory.V.TR
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.WeakApproxGL

theorem denseRange_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange ((pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F))) := by
  have hc : Continuous (infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

theorem exists_rat_det_pos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ)
    (g : GL (Fin a) (InfinitePlace F → ℝ)), ∃ h : GL (Fin a) F, ∀ v, 0 < ((((Matrix.GeneralLinearGroup.map (pInf F)).comp
      (GlobalTheory.CuspRep.ratGL F a)) h) * g).val.det v := by
  intro F _ _ _ a g
  set φ : F →+* (InfinitePlace F → ℝ) := (pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F)) with hφ
  have hcomp : ∀ h : GL (Fin a) F, (((Matrix.GeneralLinearGroup.map (pInf F)).comp (GlobalTheory.CuspRep.ratGL F a)) h).val
      = (h.val).map φ := fun h => by
    ext i j; rfl
  have hdu : IsUnit g.val.det := Matrix.isUnits_det_units g
  have hd : ∀ v, g.val.det v ≠ 0 := fun v => ((Pi.isUnit_iff.1 hdu) v).ne_zero
  have hopen : IsOpen {y : InfinitePlace F → ℝ | ∀ v, 0 < y v * g.val.det v} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  obtain ⟨t, ht⟩ := (denseRange_inf F).exists_mem_open hopen
    ⟨fun v => (g.val.det v)⁻¹, fun v => by simp [hd v]⟩
  have ht' : ∀ v, 0 < φ t v * g.val.det v := ht
  cases a with
  | zero =>
    refine ⟨1, fun v => ?_⟩
    rw [Matrix.det_isEmpty]
    exact one_pos
  | succ n =>
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have := ht' v
      simp at this
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.diagonal (Function.update 1 0 t)
    have hD : D.det = t := by
      rw [Matrix.det_diagonal, Fin.prod_univ_succ]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (hD ▸ ht0), fun v => ?_⟩
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
    rw [Units.val_mul, Matrix.det_mul, hcomp, e, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hD]
    exact ht' v

end GlobalTheory.WeakApproxGL
end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    ((algebraMap F (Ad F) x).1 v) = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x
  rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe
    (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_GL2_infinite_finite_factor : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F), ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem slash_add_smul_pow : ∀ (F : Type) [Field F] [NumberField F] (k M : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f g : Hn F → ℂ) (c : ℂ), sl0 k h (f + g) = sl0 k h f + sl0 k h g ∧ sl0 k h (c • f) = c • sl0 k h f ∧ sl0 (k * M) h (f ^ M) = sl0 k h f ^ M ∧ sl k h (f + g) = sl k h f + sl k h g ∧ sl k h (c • f) = c • sl k h f ∧ sl (k * M) h (f ^ M) = sl k h f ^ M := by
  intro F _ _ k M h f g c
  have h0a : sl0 k h (f + g) = sl0 k h f + sl0 k h g := by
    funext z; simp only [sl0, Pi.add_apply]; ring
  have h0s : sl0 k h (c • f) = c • sl0 k h f := by
    funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring
  have h0p : sl0 (k * M) h (f ^ M) = sl0 k h f ^ M := by
    funext z; simp only [sl0, Pi.pow_apply]; rw [mul_pow, pow_mul]
  refine ⟨h0a, h0s, h0p, ?_, ?_, ?_⟩
  · funext z; simp only [sl, h0a, Pi.add_apply]; ring
  · funext z; simp only [sl, h0s, Pi.smul_apply, smul_eq_mul]; ring
  · funext z
    simp only [sl, h0p, Pi.pow_apply]
    rw [mul_pow]
    congr 1
    have hx : (0 : ℝ) ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
      Finset.prod_nonneg fun v _ => abs_nonneg _
    rw [← Complex.ofReal_pow, ← Real.rpow_mul_natCast hx]
    congr 2
    push_cast; ring

end GlobalTheory.HilbertThetaSeries
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DelGen

variable {F : Type} [Field F] [NumberField F]

theorem exists_pos_val (T : Finset (HeightOneSpectrum (𝓞 F))) (γ : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ))
    (hγ : ∀ w ∈ T, γ w ≠ 0) :
    ∃ a : F, (∀ w ∈ T, w.valuation F a = γ w) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuation_surjective F (γ w)
  set M : ℕ := T.sup (fun w => (WithZero.log (γ w)).natAbs) + 1 with hM
  obtain ⟨a, ha, hpos⟩ := GlobalTheory.FinPlaceApproxPos.approxpos_target F T t M
  refine ⟨a, fun w hw => ?_, hpos⟩
  have hle : (WithZero.log (γ w)).natAbs ≤ T.sup (fun w => (WithZero.log (γ w)).natAbs) :=
    Finset.le_sup (f := fun w => (WithZero.log (γ w)).natAbs) hw
  have hlt : WithZero.exp (-(M : ℤ)) < γ w := by
    conv_rhs => rw [← WithZero.exp_log (hγ w hw)]
    rw [WithZero.exp_lt_exp]
    omega
  rw [← ht w]
  exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt (ha w hw) (by rw [ht w]; exact hlt))

theorem finite_over (p : ℕ) (hp : p ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∈ T ↔ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine ⟨(Ideal.finite_factors h0).toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end GlobalTheory.HilbertThetaSeries.DelGen


open GlobalTheory.HilbertThetaSeries.DelGen in
theorem GlobalTheory.HilbertThetaSeries.del_exists_and_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  intro F _ _ _ p hp
  obtain ⟨T, hT⟩ := finite_over (F := F) p hp.ne_zero
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_pos_val T (fun w => WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
      (fun w _ => WithZero.exp_ne_zero)
    exact ⟨a, fun w hw => ha w ((hT w).2 hw)⟩
  · intro δ hδ y
    have hne : ∀ w ∈ T, Valued.v (pLoc F w (y : Af F)) * w.valuation F δ ≠ 0 := by
      intro w hw
      refine mul_ne_zero ?_ ?_
      · rw [Ne, map_eq_zero]
        exact ((y.map (pLoc F w).toMonoidHom).ne_zero)
      · rw [hδ w ((hT w).1 hw)]
        exact WithZero.exp_ne_zero
    obtain ⟨a, ha, hpos⟩ := exists_pos_val T (fun w => (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ)⁻¹)
      (fun w hw => inv_ne_zero (hne w hw))
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have ha0 : a ≠ 0 := by
      intro h
      have h1 := hpos (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      rw [h, map_zero] at h1
      exact lt_irrefl _ h1
    refine ⟨Units.mk0 a ha0, fun u => ?_, fun w hw => ?_⟩
    · show 0 < (u.embedding a).re
      rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal u), Complex.ofReal_re]
      exact hpos _
    · have hw' := (hT w).2 hw
      rw [Units.val_mul, Units.coe_map, map_mul]
      show Valued.v ((a : w.adicCompletion F) * pLoc F w (y : Af F)) * w.valuation F δ = 1
      rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ha w hw', mul_assoc, inv_mul_cancel₀ (hne w hw')]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_different_generator_totallyPositive_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.del_exists_and_move | exact GlobalTheory.HilbertThetaSeries.del_exists_and_move | (intros; apply GlobalTheory.HilbertThetaSeries.del_exists_and_move <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_lin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  intro F _ _ _ f g a b c hf hg
  obtain ⟨⟨D, hD, hfa⟩, hfs⟩ := hf
  obtain ⟨⟨E, hE, hgb⟩, hgs⟩ := hg
  have hez : ∀ z : Hn F, ez (0 : F) z = 1 := by
    intro z
    simp [ez, reAt]
  have scale : ∀ (ξ : F) (m k : ℕ), IsIntegral ℤ ((m : F) * ξ) →
      IsIntegral ℤ (((m * k : ℕ) : F) * ξ) ∧ IsIntegral ℤ (((k * m : ℕ) : F) * ξ) := by
    intro ξ m k h
    have e1 : ((m * k : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have e2 : ((k * m : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have hk : IsIntegral ℤ ((k : ℤ) : F) := isIntegral_algebraMap
    exact ⟨e1 ▸ hk.mul h, e2 ▸ hk.mul h⟩
  have both : ∀ ξ : F, a ξ ≠ 0 ∨ b ξ ≠ 0 →
      (ξ = 0 ∨ TP ξ) ∧ IsIntegral ℤ (((D * E : ℕ) : F) * ξ) := by
    intro ξ h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := hfa ξ h
      exact ⟨h1, (scale ξ D E h2).1⟩
    · obtain ⟨h1, h2⟩ := hgb ξ h
      exact ⟨h1, (scale ξ E D h2).2⟩
  have hDE : 0 < D * E := Nat.mul_pos hD hE
  refine ⟨⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨D, hD, ?_⟩, ?_⟩, ⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨1, one_pos, ?_⟩, ?_⟩⟩
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.add_apply, add_mul] using (hfs z).add (hgs z)
  · intro ξ h
    apply hfa
    intro h0
    apply h
    simp [h0]
  · intro z
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using (hfs z).mul_left c
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.sub_apply, sub_mul] using (hfs z).sub (hgs z)
  · intro ξ h
    have h0 : ξ = 0 := by
      by_contra hne
      apply h
      simp [hne]
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : F))
  · intro z
    have := hasSum_single (f := fun ξ : F => (open Classical in if ξ = 0 then c else 0) * ez ξ z) (0 : F) (by
      intro ξ hξ
      simp [hξ])
    convert this using 1
    simp [hez z]
end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_linear_combination : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_lin | exact GlobalTheory.HilbertThetaSeries.hasQ_lin | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_lin <;> assumption)
end
