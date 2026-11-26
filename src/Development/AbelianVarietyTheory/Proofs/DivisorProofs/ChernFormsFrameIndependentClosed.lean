module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZero
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.ChernDbar

variable {n : ℕ}

theorem dbar_dbar_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e (a b : V n) : dbar (fun x => dbar u x a) z b = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z b a
      + Complex.I * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) a + Complex.I * fderiv ℝ (fderiv ℝ u) z b (Complex.I • a)
      - fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a)) := by
    have e0 : (fun x => dbar u x a) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + Complex.I • fderiv ℝ u x (Complex.I • a)) :=
      funext fun x => dbar_apply u x a
    rw [e0, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, dbar_apply,
      fderiv_fderiv_apply hu, smul_eq_mul]
    linear_combination (1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a) * Complex.I_mul_I
  rw [e, e, hs.eq w v, hs.eq (Complex.I • w) v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem dbarAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ} (hg : ∀ p, DifferentiableAt ℝ (g p) v)
    (c : ι → Alt n) : dbarAt (fun x => ∑ p, g p x • c p) v =
      ∑ a, ∑ p, dbar (g p) v (coordVec a) • (dzb a * c p) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have : coefwise (fun f => dbar f v (coordVec a)) (fun x => ∑ p, g p x • c p) =
      ∑ p, dbar (g p) v (coordVec a) • c p := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [dbar_sum (A := fun p x => g p x * (bas n).repr (c p) S) (fun p _ => (hg p).mul (differentiableAt_const _)),
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dbar_mul (hg p) (differentiableAt_const _)]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem differentiableAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ}
    (hg : ∀ p, DifferentiableAt ℝ (g p) v) (c : ι → Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (∑ p, g p x • c p) S) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact DifferentiableAt.fun_sum fun p _ => (hg p).mul (differentiableAt_const _)

theorem dbarAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v := by
  simp only [dbarAt, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  simp only [map_add (f := _), Finsupp.add_apply, FormMul.repr_coefwise]
  rw [dbar_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem dbarAt_const (c : Alt n) (v : V n) : dbarAt (fun _ => c) v = 0 := by
  simp [dbarAt, coefwise]

def IsClosedAt (v : V n) (F : V n → Ev n) : Prop :=
  (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ dbarAt (fun x => (F x : Alt n)) v = 0

theorem isClosedAt_const (v : V n) (c : Ev n) : IsClosedAt v fun _ => c :=
  ⟨fun _ => differentiableAt_const _, dbarAt_const _ _⟩

def closedAt (v : V n) : Subsemiring (V n → Ev n) where
  carrier := {F | IsClosedAt v F}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · rw [show (fun x => (bas n).repr ((F * G) x : Alt n) S) = _ from
        funext fun x => FormMul.repr_mul (F x : Alt n) (G x : Alt n) S]
      exact DifferentiableAt.fun_sum fun p _ => ((hF _).mul (hG _)).mul (differentiableAt_const _)
    · obtain ⟨y, hy⟩ := FormMul.dbarAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  one_mem' := isClosedAt_const v 1
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [dbarAt_add hF hG, hF0, hG0, add_zero]
  zero_mem' := isClosedAt_const v 0

theorem const_mem (v : V n) (c : Ev n) : (fun _ => c) ∈ closedAt v := isClosedAt_const v c

def closedRing (v : V n) : Subring (V n → Ev n) :=
  { closedAt v with
    neg_mem' := fun {F} hF => by
      have := (closedAt v).mul_mem (const_mem v (-1)) hF
      have e : (fun _ => (-1 : Ev n)) * F = -F := funext fun x => neg_one_mul _
      rwa [e] at this }

theorem dzb_dz_dzb (a b c : Fin n) : dzb c * (dz a * dzb b) = -(dzb b * (dz a * dzb c)) := by
  have h (b c : Fin n) : dzb c * (dz a * dzb b) = dz a * dzb b * dzb c :=
    Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dzb c)
  rw [h, h, mul_assoc, mul_assoc, ← mul_neg]
  exact congrArg _ (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _))

theorem dbar_form_mem {v : V n} {θ : Fin n → V n → ℂ} (hθ : ∀ a, ContDiffAt ℝ 2 (θ a) v) :
    (fun x => ∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b)) ∈ closedRing v := by
  have e (x : V n) : ((∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b) : Ev n) : Alt n) =
      ∑ p : Fin n × Fin n, dbar (θ p.1) x (coordVec p.2) • (dz p.1 * dzb p.2) := by
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym, Fintype.sum_prod_type]
  have hd (p : Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (θ p.1) x (coordVec p.2)) v :=
    differentiableAt_dbar_apply (hθ p.1) _
  change IsClosedAt v _
  refine ⟨fun S => ?_, ?_⟩
  · simp only [e]
    exact differentiableAt_sum_smul hd _ S
  · simp only [e]
    rw [dbarAt_sum_smul hd]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    set s : Alt n := ∑ c, ∑ b, dbar (fun x => dbar (θ a) x (coordVec b)) v (coordVec c) • (dzb c * (dz a * dzb b))
      with hs
    have h2 : s = -s := by
      conv_lhs => rw [hs, Finset.sum_comm]
      rw [hs, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dzb_dz_dzb a b c, dbar_dbar_comm (hθ a), smul_neg]
    have h3 : (2 : ℂ) • s = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h2
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

theorem coeff_charpolyRev_map {A B r : Type} [CommRing A] [CommRing B] [Fintype r] [DecidableEq r] (f : A →+* B)
    (M : Matrix r r A) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map, charpolyRev, charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  apply congrArg (fun p : Polynomial B => p.coeff j)
  apply congrArg Matrix.det
  ext i k
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

theorem dbarAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)),
    IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s,
    dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have hθ (i k : r) (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn H x (coordVec a) i k) v :=
    h3.conn (hu v hv) (by norm_num) (coordVec a) i k
  let M : Matrix r r (closedRing v) := Matrix.of fun i k => ⟨_, dbar_form_mem (hθ i k)⟩
  have key (w : V n) : MvPolynomial.aeval sym (chernPoly H w j) = (M.charpolyRev.coeff j : V n → Ev n) w := by
    have h1 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have h2 := coeff_charpolyRev_map ((Pi.evalRingHom (fun _ : V n => Ev n) w).comp (closedRing v).subtype) M j
    refine h1.symm.trans (Eq.trans ?_ h2)
    apply congrArg (fun N : Matrix r r (Ev n) => N.charpolyRev.coeff j)
    ext i k
    simp [M, curvPoly, curv, Algebra.smul_def]
  have hm : IsClosedAt v _ := (closedRing v).mul_mem (const_mem v (algebraMap ℂ _ (kappa ^ j))) (M.charpolyRev.coeff j).2
  have e : (fun w => (chernAt H w j : Alt n)) = fun w =>
      ((algebraMap ℂ (Ev n) (kappa ^ j) * (M.charpolyRev.coeff j : V n → Ev n) w : Ev n) : Alt n) :=
    funext fun w => by rw [chernAt, key, Algebra.smul_def]
  rw [e]
  exact hm.2

end GlobalTheory.CxForm.ChernDbar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZeroStatement
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | exact GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZero
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.ChernDel

variable {n : ℕ}

theorem del_del_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (ξ η : V n) :
    del (fun x => del u x ξ) z η = del (fun x => del u x η) z ξ := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key : ∀ a b : V n, del (fun x => del u x a) z b = (1 / 2 : ℂ) • (del (fun x => fderiv ℝ u x a) z b -
      Complex.I • del (fun x => fderiv ℝ u x (Complex.I • a)) z b) := by
    intro a b
    simp only [del_apply u]
    rw [del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), del_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [del_apply, fderiv_fderiv_apply hu, hs.eq ξ, hs.eq (Complex.I • ξ), smul_eq_mul]
  ring

section Mat

variable {r : Type} [Fintype r] [DecidableEq r]

theorem mdel_conn {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : V n) :
    mdel (fun x => conn H x ξ) z η = mdel (fun x => conn H x η) z ξ +
      (conn H z ξ * conn H z η - conn H z η * conn H z ξ) := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have hc : mdel (fun x => mdel H x ξ) z η = mdel (fun x => mdel H x η) z ξ := by
    ext a b; exact del_del_comm (h a b) ξ η
  simp only [conn]
  rw [mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) η).transpose,
    mdel_inv h1.transpose hu', mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ξ),
    mdel_transpose (fun x => mdel H x η), hc, mdel_transpose, mdel_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem mdel_curv_comm {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 3 H z) (hu : IsUnit (H z).det)
    {ξ η : V n} (hξ : conn H z ξ = 0) (hη : conn H z η = 0) (ζ : V n) :
    mdel (fun x => curv H x ξ ζ) z η = mdel (fun x => curv H x η ζ) z ξ := by
  have h2 : MContDiffAt 2 H z := h.of_le (by norm_num)
  have c2 : ∀ a, MContDiffAt 2 (fun x => conn H x a) z := fun a => h.conn hu (by norm_num) a
  have c1 : ∀ a, MContDiffAt 1 (fun x => conn H x a) z := fun a => (c2 a).of_le one_le_two
  have he : (fun x => mdel (fun y => conn H y ξ) x η) =ᶠ[𝓝 z] fun x => mdel (fun y => conn H y η) x ξ +
      (conn H x ξ * conn H x η + -(conn H x η * conn H x ξ)) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu] with x h3 h4
    rw [mdel_conn h3 h4, sub_eq_add_neg]
  simp only [curv]
  rw [mdel_neg, mdel_neg, mdel_mdbar (c2 ξ), mdel_mdbar (c2 η), ← mdbar_mdel (c2 ξ), ← mdbar_mdel (c2 η),
    mdbar_congr he, mdbar_add ((c2 η).mdel (by norm_num) ξ) (((c1 ξ).mul (c1 η)).add ((c1 η).mul (c1 ξ)).neg),
    mdbar_add ((c1 ξ).mul (c1 η)) ((c1 η).mul (c1 ξ)).neg, mdbar_neg, mdbar_mul (c1 ξ) (c1 η),
    mdbar_mul (c1 η) (c1 ξ), hξ, hη]
  simp

end Mat

theorem delAt_congr {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {u : ι → V n → ℂ} (hu : ∀ i, DifferentiableAt ℝ (u i) v)
    (α : ι → Alt n) :
    delAt (fun x => ∑ i, u i x • α i) v = ∑ c, ∑ i, del (u i) v (coordVec c) • (dz c * α i) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have : coefwise (fun f => del f v (coordVec c)) (fun x => ∑ i, u i x • α i) =
      ∑ i, del (u i) v (coordVec c) • α i := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [del_sum fun i _ => (hu i).mul_const _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (hu i) (differentiableAt_const _), del_const]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  simp only [map_add (f := _), Finsupp.add_apply, FormMul.repr_coefwise]
  rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem delAt_const (α : Alt n) (v : V n) : delAt (fun _ => α) v = 0 := by
  simp [delAt, coefwise]

def closedAt (v : V n) : Subalgebra ℂ (V n → Ev n) where
  carrier := {F | (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧
    delAt (fun x => (F x : Alt n)) v = 0}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.mul_apply, Subalgebra.coe_mul, FormMul.repr_mul (F _ : Alt n)]
      exact DifferentiableAt.fun_sum fun p _ => ((hF p.1).mul (hG p.2)).mul_const _
    · obtain ⟨y, hy⟩ := FormMul.delAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [delAt_add hF hG, hF0, hG0, add_zero]
  algebraMap_mem' c := ⟨fun S => differentiableAt_const ((bas n).repr (algebraMap ℂ (Ev n) c : Alt n) S),
    delAt_const (algebraMap ℂ (Ev n) c : Alt n) v⟩

theorem mem_closedAt {v : V n} {F : V n → Ev n} : F ∈ closedAt v ↔
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ delAt (fun x => (F x : Alt n)) v = 0 :=
  Iff.rfl

theorem coeff_charpolyRev_map {R S r : Type} [CommRing R] [CommRing S] [Fintype r] [DecidableEq r] (f : R →+* S)
    (M : Matrix r r R) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  apply congrArg (fun A : Matrix r r (Polynomial S) => A.det.coeff j)
  ext a b
  simp [Matrix.one_apply, apply_ite (Polynomial.map f)]

theorem mem_closedAt_of_symm {v : V n} {u : Fin n × Fin n → V n → ℂ} (hu : ∀ p, DifferentiableAt ℝ (u p) v)
    (hs : ∀ a b c, del (u (a, b)) v (coordVec c) = del (u (c, b)) v (coordVec a)) :
    (fun x => ∑ p, u p x • sym p) ∈ closedAt v := by
  refine mem_closedAt.2 ⟨fun S => ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, map_sum, map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul]
    exact DifferentiableAt.fun_sum fun p _ => (hu p).mul_const _
  · simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul]
    rw [delAt_sum_smul hu]
    simp only [Fintype.sum_prod_type]
    set T : Alt n := ∑ c, ∑ a, ∑ b, del (u (a, b)) v (coordVec c) • (dz c * (sym (a, b) : Alt n)) with hT
    have h2 : T = -T := by
      conv_rhs => rw [hT, Finset.sum_comm]
      rw [hT]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs a b c, ← smul_neg]
      congr 1
      show dz c * (dz a * dzb b) = -(dz a * (dz c * dzb b))
      rw [← mul_assoc, ← mul_assoc, ← neg_mul]
      congr 1
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h3 : (2 : ℂ) • T = 0 := by rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel T
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable {r : Type} [Fintype r] [DecidableEq r]

theorem delAt_chernAt_of_conn_eq_zero {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 3 H v)
    (hu : IsUnit (H v).det) (h0 : ∀ a, conn H v (coordVec a) = 0) (j : ℕ) :
    delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  have hm : ∀ i k, (fun x => ∑ p : Fin n × Fin n, curv H x (coordVec p.1) (coordVec p.2) i k • sym p) ∈ closedAt v :=
    fun i k => mem_closedAt_of_symm (u := fun p x => curv H x (coordVec p.1) (coordVec p.2) i k)
      (fun p => (h.curv hu (j := 1) (by norm_num) _ _).diff i k)
      fun a b c => congrFun (congrFun (mdel_curv_comm h hu (h0 a) (h0 c) (coordVec b)) i) k
  let M : Matrix r r (closedAt v) := Matrix.of fun i k => ⟨_, hm i k⟩
  set_option synthInstance.maxHeartbeats 200000 in
  have e : (fun w => chernAt H w j) = (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v) := by
    funext w
    let ev : closedAt v →+* Ev n := (Pi.evalRingHom (fun _ => Ev n) w).comp (closedAt v).val.toRingHom
    have e1 := coeff_charpolyRev_map ev (-M) j
    have e2 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have e3 : (-M).map ev = (-curvPoly H w).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom := by
      ext i k : 2
      simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      congr 1
      simp [M, ev, curvPoly, Fintype.sum_prod_type, Algebra.smul_def]
    rw [e3, e2] at e1
    show kappa ^ j • _ = kappa ^ j • ev _
    rw [← e1]
    rfl
  set_option synthInstance.maxHeartbeats 200000 in
  have := (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v).2
  rw [← e] at this
  exact (mem_closedAt.1 this).2

theorem delAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have h2 : MContDiffAt 2 H v := h3.of_le (by norm_num)
  let L : r → r → V n →L[ℂ] ℂ := fun i k => ∑ a, conn H v (coordVec a) i k • EuclideanSpace.proj a
  let A : V n → Matrix r r ℂ := fun w => Matrix.of fun i k => (1 : Matrix r r ℂ) i k + L i k v - L i k w
  have hAv : A v = 1 := by ext i k; simp [A]
  have hAa : ∀ w i k, AnalyticAt ℂ (fun w => A w i k) w := fun w i k => analyticAt_const.sub ((L i k).analyticAt w)
  have hA3 : MContDiffAt 3 A v := fun i k => (hAa v i k).contDiffAt.restrict_scalars ℝ
  have hAu : IsUnit (A v).det := by rw [hAv, det_one]; exact isUnit_one
  have hA0 : ∀ η, mdbar A v η = 0 := fun η => by
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hAa v a b).differentiableAt]
    rfl
  have hAd : ∀ c, mdel A v (coordVec c) = -conn H v (coordVec c) := fun c => by
    ext i k
    rw [mdel_apply, del_eq_fderiv (hAa v i k).differentiableAt]
    have : HasFDerivAt (fun w => A w i k) (-L i k) v := (L i k).hasFDerivAt.const_sub _
    rw [this.fderiv]
    simp [L, Pi.single_apply]
  have hK : MContDiffAt 3 (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) v :=
    (hA3.transpose.mul h3).mul hA3.conjTranspose.transpose
  have hKu : IsUnit ((A v)ᵀ * H v * (A v)ᴴᵀ).det := by simpa [hAv] using hu v hv
  have he : (fun w => (chernAt H w j : Alt n)) =ᶠ[𝓝 v]
      fun w => (chernAt (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) w j : Alt n) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit (hu v hv), hA3.eventually_isUnit hAu] with w a1 a2 a3
    rw [chernAt_changeFrame (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) H A w a1 a2 (hAa w) a3
      (Eventually.of_forall fun _ => rfl) j]
  rw [delAt_congr he]
  refine delAt_chernAt_of_conn_eq_zero hK hKu (fun a => ?_) j
  rw [conn_changeFrame (h3.of_le (by norm_num)) (hu v hv) (hA3.of_le (by norm_num)) hAu hA0, hAd, hAv]
  simp

end GlobalTheory.CxForm.ChernDel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZeroStatement
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDel.delAt_chernAt | exact GlobalTheory.CxForm.ChernDel.delAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDel.delAt_chernAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficients
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernSmooth

section General

variable {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing B] [Algebra ℂ B]

def WeakSmooth (s : Set E) (F : E → B) : Prop := ∀ φ : B →ₗ[ℂ] ℂ, ContDiffOn ℝ ∞ (fun v => φ (F v)) s

def mult (B : Type) [CommRing B] [Algebra ℂ B] (s : Set E) : Subring (E → B) where
  carrier := {G | ∀ F, WeakSmooth s F → WeakSmooth s (G * F)}
  mul_mem' {a b} ha hb F hF := by rw [mul_assoc]; exact ha _ (hb _ hF)
  one_mem' F hF := by rwa [one_mul]
  add_mem' {a b} ha hb F hF φ := by
    simpa [add_mul] using (ha F hF φ).add (hb F hF φ)
  zero_mem' F hF φ := by simpa using contDiffOn_const
  neg_mem' {a} ha F hF φ := by simpa using (ha F hF φ).neg

theorem smul_mem {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f s) (b : B) : (fun v => f v • b) ∈ mult B s := by
  intro F hF φ
  simpa using hf.mul (hF (φ ∘ₗ LinearMap.mulLeft ℂ b))

theorem const_mem (s : Set E) (b : B) : (fun _ => b) ∈ mult B s := by
  simpa using smul_mem (s := s) (f := fun _ => (1 : ℂ)) contDiffOn_const b

theorem weakSmooth_of_mem {s : Set E} {G : E → B} (h : G ∈ mult B s) : WeakSmooth s G := by
  simpa using h 1 fun φ => by simpa using contDiffOn_const

theorem det_mem {s : Set E} {r : Type} [Fintype r] [DecidableEq r] {M : E → Matrix r r B}
    (h : ∀ i j, (fun v => M v i j) ∈ mult B s) : (fun v => (M v).det) ∈ mult B s := by
  have : (fun v => (M v).det) = ∑ σ : Equiv.Perm r, ((Equiv.Perm.sign σ : ℤ) : E → B) * ∏ i, fun v => M v (σ i) i := by
    funext v
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

end General

theorem contDiffOn_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  intro n r _ _ H s hs hH hu j S
  have hc : ∀ ξ η a b, ContDiffOn ℝ ∞ (fun v => curv H v ξ η a b) s := fun ξ η a b v hv =>
    (MContDiffAt.curv (k := ∞) (j := ∞) (fun a b => (hH a b).contDiffAt (hs.mem_nhds hv)) (hu v hv)
      (by norm_cast) ξ η a b).contDiffWithinAt
  have hd : (fun v => (-curvPoly H v).charpolyRev) ∈ mult (Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) s := by
    unfold Matrix.charpolyRev
    refine det_mem fun a b => ?_
    have : (fun v => (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
        (-curvPoly H v).map Polynomial.C) a b) = (fun _ => (1 : Matrix r r _) a b) + ∑ c, ∑ d, fun v =>
          curv H v (coordVec c) (coordVec d) a b • (Polynomial.X * Polynomial.C (MvPolynomial.X (c, d))) := by
      funext v
      simp [curvPoly, Finset.sum_apply, Finset.mul_sum, MvPolynomial.C_mul', ← Polynomial.smul_C]
    rw [this]
    exact add_mem (const_mem _ _) (sum_mem fun c _ => sum_mem fun d _ => smul_mem (hc _ _ _ _) _)
  let φ : Polynomial (MvPolynomial (Fin n × Fin n) ℂ) →ₗ[ℂ] ℂ :=
    (bas n).coord S ∘ₗ (Subalgebra.center ℂ (Alt n)).val.toLinearMap ∘ₗ (kappa ^ j • (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toLinearMap) ∘ₗ
      (Polynomial.lcoeff _ j).restrictScalars ℂ
  exact weakSmooth_of_mem hd φ

end GlobalTheory.ChernSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficientsStatement
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  first | exact @GlobalTheory.ChernSmooth.contDiffOn_chernAt | exact GlobalTheory.ChernSmooth.contDiffOn_chernAt | (intros; apply GlobalTheory.ChernSmooth.contDiffOn_chernAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology MeasureTheory
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ChernFrame

theorem chernAt_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {H K : V n → Matrix r r ℂ} {v : V n}
    (h : H =ᶠ[𝓝 v] K) (j : ℕ) : chernAt H v j = chernAt K v j := by
  unfold chernAt chernPoly curvPoly
  simp only [curv_congr h]

theorem delAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem dbarAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.dbar_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem chern_frame_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  intro M _ n A ι _ _ κ U hUo hUc g hg G hGs hGp hGt j
  have hop : ∀ i a, IsOpen ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a =>
    (A.e i).isOpen_inter_preimage_symm (hUo a)
  have hsm : ∀ i a p q, ContDiffOn ℝ ∞ (fun v => G a ((A.e i).symm v) p q)
      ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a p q => hGs a p q i
  have hun : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a, IsUnit (G a ((A.e i).symm v)).det :=
    fun i a v hv => (isUnit_iff_isUnit_det _).1 (hGp a _ hv.2).isUnit
  have hpt : ∀ (x : A.Pt) a, x.pt ∈ U a → x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' U a :=
    fun x a ha => ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact ha⟩
  have hfr : ∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x := by
    intro a b x ha hb
    have hN : IsOpen ((A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b)) :=
      (A.e x.1.1).isOpen_inter_preimage_symm ((hUo a).inter (hUo b))
    have hsym : (A.e x.1.1).symm x.crd = x.pt := x.ch.left_inv x.2
    have hx : x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b) :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [hsym]; exact ⟨ha, hb⟩⟩
    have hK : MContDiffAt 2 (fun v => G a ((A.e x.1.1).symm v)) x.crd := fun p q =>
      ((hsm x.1.1 a p q).contDiffAt ((hop x.1.1 a).mem_nhds (hpt x a ha))).of_le (by norm_cast)
    have hKu : IsUnit (G a ((A.e x.1.1).symm x.crd)).det := hun x.1.1 a _ (hpt x a ha)
    have hA : ∀ p q, AnalyticAt ℂ (fun w => g a b ((A.e x.1.1).symm w) p q) x.crd := fun p q =>
      GlobalTheory.SCV.analyticAt_of_differentiableOn (hg a b p q x.1.1) (hN.mem_nhds hx)
    have hAu : IsUnit (g a b ((A.e x.1.1).symm x.crd)).det := by
      rw [hsym]
      have h2 := (isUnit_iff_isUnit_det _).1 (hGp b _ hb).isUnit
      rw [hGt a b x.pt ⟨ha, hb⟩, chg, det_mul, det_mul] at h2
      simpa using isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2)
    have hev : (fun v => G b ((A.e x.1.1).symm v)) =ᶠ[𝓝 x.crd]
        fun v => chg (g a b ((A.e x.1.1).symm v)) (G a ((A.e x.1.1).symm v)) :=
      Filter.eventually_of_mem (hN.mem_nhds hx) fun v hv => hGt a b _ hv.2
    exact (GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange _ _ _ _ hK hKu hA hAu hev j).symm
  refine ⟨hfr, fun P hP => ?_⟩
  have hloc : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a,
      A.loc P i v = (chernAt (fun w => G a ((A.e i).symm w)) v j : Alt n) := by
    intro i a v hv
    rw [HolAtlas.loc, dite_eq_left hv.1, hP a ⟨(i, (A.e i).symm v), (A.e i).map_target hv.1⟩ hv.2]
    show ((chernAt (fun w => G a ((A.e i).symm w)) ((A.e i) ((A.e i).symm v)) j : Ev n) : Alt n) = _
    rw [(A.e i).right_inv hv.1]
  have hgerm : ∀ i a v, v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a →
      A.loc P i =ᶠ[𝓝 v] fun w => (chernAt (fun w' => G a ((A.e i).symm w')) w j : Alt n) :=
    fun i a v hv => Filter.eventually_of_mem ((hop i a).mem_nhds hv) (hloc i a)
  refine ⟨⟨fun i S => ?_, fun x x' hxx => ?_⟩, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
    obtain ⟨a, ha⟩ := hUc ((A.e i).symm v)
    refine ⟨_, hop i a, ⟨hv, ha⟩, ?_⟩
    refine ((GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients _ _ (hop i a) (hsm i a) (hun i a) j S).mono inter_subset_right).congr fun w hw => ?_
    rw [hloc i a w hw.2]
  · obtain ⟨a, ha⟩ := hUc x.pt
    have ha' : x'.pt ∈ U a := hxx ▸ ha
    rw [hP a x ha, hP a x' ha']
    have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hxW : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; show x.pt ∈ _; rw [hxx]; exact x'.2⟩
    have hφ : AnalyticAt ℂ (x'.ch ∘ x.ch.symm) x.crd := GlobalTheory.SCV.analyticAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hW.mem_nhds hxW)
    have hφv : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      simp only [Function.comp_apply]; rw [x.ch.left_inv x.2]; show x'.ch x.pt = x'.ch x'.pt; rw [hxx]
    have hH2 : MContDiffAt 2 (fun v => G a (x'.ch.symm v)) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hφv]
      exact fun p q => ((hsm x'.1.1 a p q).contDiffAt ((hop x'.1.1 a).mem_nhds (hpt x' a ha'))).of_le
        (by norm_cast)
    have hHu : IsUnit (G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
      rw [hφv]; exact hun x'.1.1 a _ (hpt x' a ha')
    have key := GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic (fun v => G a (x'.ch.symm v)) (x'.ch ∘ x.ch.symm) x.crd hφ hH2 hHu j
    rw [hφv] at key
    have hge : (fun v => G a (x.ch.symm v)) =ᶠ[𝓝 x.crd] fun w => G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) w)) :=
      Filter.eventually_of_mem (hW.mem_nhds hxW) fun w hw => by
        simp only [Function.comp_apply]; rw [x'.ch.left_inv hw.2]
    show ((chernAt (fun v => G a (x.ch.symm v)) x.crd j : Ev n) : Alt n) = _
    rw [chernAt_congr hge j, key]
    rfl
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show delAt (A.loc P x.1.1) x.crd = 0
    rw [delAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show dbarAt (A.loc P x.1.1) x.crd = 0
    rw [dbarAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)

end GlobalTheory.ChernFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForms_frame_independent_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  first | exact @GlobalTheory.ChernFrame.chern_frame_closed | exact GlobalTheory.ChernFrame.chern_frame_closed | (intros; apply GlobalTheory.ChernFrame.chern_frame_closed <;> assumption)
end
