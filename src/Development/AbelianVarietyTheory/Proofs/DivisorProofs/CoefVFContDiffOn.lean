module

public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.VFComp

variable {d : ℕ}

theorem dw_contDiffOn {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) :
    ∀ w : List (Fin d), ContDiffOn ℝ ∞ (dw w u) U
  | [] => hu
  | j :: w => by
    have h : ContDiffOn ℝ ∞ (fderiv ℝ (dw w u)) U :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ) hU).mp (dw_contDiffOn hU hu w)).2
    exact h.clm_apply contDiffOn_const

theorem diffAt_of {U : Set (E d)} (hU : IsOpen U) {f : E d → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {x : E d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hf).1).differentiableAt (hU.mem_nhds hx)

def coefB (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  if n ≤ m then ∑ j, c j x * fderiv ℝ (a n w) x (ev j) else 0

def coefA (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ) :
    (n : ℕ) → (Fin n → Fin d) → E d → ℂ
  | 0, _ => fun _ => 0
  | k + 1, w => fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0

def coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  coefA m a c n w x + coefB m a c n w x

theorem sum_cons {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin d) → M) :
    ∑ w : Fin (k + 1) → Fin d, g w = ∑ j : Fin d, ∑ w : Fin k → Fin d, g (Fin.cons j w) := by
  rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem coefVF_contDiffOn {U : Set (E d)} (hU : IsOpen U) (m : ℕ)
    (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) (w : Fin n → Fin d) :
    ContDiffOn ℝ ∞ (coefVF m a c n w) U := by
  have hB : ContDiffOn ℝ ∞ (coefB m a c n w) U := by
    unfold coefB
    split_ifs
    · exact ContDiffOn.sum fun j _ => (hc j).mul (dw_contDiffOn hU (ha n w) [j])
    · exact contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (coefA m a c n w) U := by
    cases n with
    | zero => exact contDiffOn_const
    | succ k =>
      show ContDiffOn ℝ ∞ (fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0) U
      split_ifs
      · exact (hc _).mul (ha _ _)
      · exact contDiffOn_const
  exact hA.add hB

theorem symb_coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (x ξ : E d) : symb (m + 1) (coefVF m a c) x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ := by
  unfold symb coefVF coefB
  rw [sum_cons, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [coefA, le_refl, if_true, show ¬ (m + 1 ≤ m) by omega, if_false, add_zero, Fin.cons_zero,
    Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem fderiv_apOp {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) {x : E d} (hx : x ∈ U)
    (j : Fin d) :
    fderiv ℝ (apOp m a u) x (ev j) = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (fderiv ℝ (a n w) x (ev j) * dw (List.ofFn w) u x + a n w x * dw (j :: List.ofFn w) u x) := by
  have hd := HasFDerivAt.sum (u := Finset.range (m + 1)) (x := x)
    (A := fun n => ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u) fun n _ =>
      HasFDerivAt.sum (u := Finset.univ) fun w _ =>
        (diffAt_of hU (ha n w) hx).hasFDerivAt.mul
          (diffAt_of hU (dw_contDiffOn hU hu (List.ofFn w)) hx).hasFDerivAt
  have he : apOp m a u = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u := by
    funext y
    simp [apOp, Finset.sum_apply]
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [dw]
  ring

end GlobalTheory.VFComp

namespace GlobalTheory.VFComp
variable {d : ℕ}

theorem apOp_coefVF {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (c : Fin d → E d → ℂ) (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E d} (hx : x ∈ U) :
    ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) (coefVF m a c) u x := by
  have hL : ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [fderiv_apOp hU m a ha hu hx, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      ring
  have hR : apOp (m + 1) (coefVF m a c) u x =
      (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (∑ j, c j x * fderiv ℝ (a n w) x (ev j)) * dw (List.ofFn w) u x) +
      ∑ n ∈ Finset.range (m + 1), ∑ j : Fin d, ∑ w : Fin n → Fin d,
        c j x * a n w x * dw (j :: List.ofFn w) u x := by
    simp only [apOp, coefVF, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_range_succ]
      have h0 : ∑ w : Fin (m + 1) → Fin d, coefB m a c (m + 1) w x * dw (List.ofFn w) u x = 0 := by
        simp [coefB]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun w _ => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      simp [coefB, this]
    · rw [Finset.sum_range_succ']
      have h0 : ∑ w : Fin 0 → Fin d, coefA m a c 0 w x * dw (List.ofFn w) u x = 0 := by
        simp [coefA]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [sum_cons]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      simp [coefA, this, List.ofFn_cons]
  rw [hL, hR]

end GlobalTheory.VFComp

theorem GlobalTheory.VFComp.vectorField_comp : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ j, ContDiffOn ℝ ∞ (c j) U) → ∃ a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) ∧ (∀ x ξ : E d, symb (m + 1) a' x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ) ∧ ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ∀ x ∈ U, ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) a' u x := by
  intro d m U hU a c ha hc
  exact ⟨GlobalTheory.VFComp.coefVF m a c, GlobalTheory.VFComp.coefVF_contDiffOn hU m a c ha hc,
    GlobalTheory.VFComp.symb_coefVF m a c, fun u hu x hx => GlobalTheory.VFComp.apOp_coefVF hU m a c ha hu hx⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm
set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationCommStatement
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivations
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivationsStatement
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  first | exact @GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | exact GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | (intros; apply GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd <;> assumption)
end
end

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations (Hol (K.W k)) (dw a) (dw b) (GlobalTheory.T.fibreCoordinatePartialDerivation_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (K.sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (K.sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosed
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.ClosedSq

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)

theorem diff (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k))
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (hn : ∀ a, n a ∈ T.J) (hnn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.fst : Hol (K.W k)) + ∑ a, f₁.φ (θ.snd a : Hol (K.W k)) * n a := by
  obtain ⟨χ, hd, h0, h1, hχ⟩ := exists_jet_factor K f₁ f₂ n (d₁.trans d₂.symm) hn hnn hf
  have e0 := hh _ _ _ (jet0 k) χ rfl (hd.trans d₁)
  have e1 := hh _ _ _ (jet1 k) χ rfl (hd.trans d₁)
  rw [h0] at e0
  rw [h1] at e1
  rw [← hχ θ, hθ, h₁, h₂, e0, e1]
  exact (add_sub_add_right_eq_sub _ _ _).trans (map_sub χ.φ _ _).symm

theorem sum_single {O : Type} [CommRing O] (v : Fin g → O) (a : Fin g) (e : O) :
    ∑ c, v c * (Pi.single a e : Fin g → O) c = v a * e := by
  simp [Pi.single_apply]

theorem diff1 (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k)) (h0 : θ.fst = 0)
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (a : Fin g) (e : T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (he : e ∈ T.J) (hee : e * e = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + f₁.φ (dw a x : Hol (K.W k)) * e) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.snd a : Hol (K.W k)) * e := by
  have := diff K h hh k θ hθ f₁ f₂ (Pi.single a e) d₁ d₂
    (fun c ↦ by rw [Pi.single_apply]; split_ifs; exacts [he, T.J.zero_mem])
    (fun c d ↦ by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      exacts [hee, mul_zero _, zero_mul _, mul_zero _])
    (fun x ↦ (hf x).trans (congrArg (f₁.φ x + ·) (sum_single (fun c ↦ f₁.φ (dw c x : Hol (K.W k))) a e).symm)) u₁ u₂ h₁ h₂
  rw [this, h0, sum_single (fun c ↦ f₁.φ (θ.snd c : Hol (K.W k)))]
  exact (congrArg (· + _) (map_zero f₁.φ)).trans (zero_add _)

theorem units_mul_relation_rearrange_commRing {C : Type} [CommRing C] (u₀ u₁ u₂ u₃ A B A' B' A₂ B₁ e₁ e₂ : C) (h1 : u₀ - u₁ = A * e₁)
    (h2 : u₁ - u₃ = B₁ * e₂) (h3 : u₀ - u₂ = B * e₂) (h4 : u₂ - u₃ = A₂ * e₁) (h5 : B₁ = B + B' * e₁)
    (h6 : A₂ = A + A' * e₂) : (B' - A') * e₁ * e₂ = 0 := by
  subst h5 h6
  linear_combination -h1 - h2 + h3 + h4

theorem connForm_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  intro I _ g Λ _ F K h hh k θ hθ
  have h0 : θ.fst = 0 := by
    have := diff K h hh k θ hθ (𝟙 (K.triv k)) (𝟙 (K.triv k)) (fun _ ↦ 0) rfl rfl (fun _ ↦ (K.triv k).J.zero_mem)
      (fun _ _ ↦ mul_zero _) (fun x ↦ by simp only [mul_zero, Finset.sum_const_zero, add_zero]) _ _ rfl rfl
    simp only [mul_zero, Finset.sum_const_zero, add_zero, sub_self] at this
    exact this.symm
  refine ⟨h0, fun a b ↦ ?_⟩
  obtain ⟨T, φ₀, φ₁, φ₂, φ₃, e₁, e₂, d₀, d₁, d₂, d₃, m₁, m₂, s₁, s₂, p₁, p₂, p₃, p₄, inj⟩ :=
    exists_second_order_nbhd I g Λ F K k a b
  refine sub_eq_zero.1 (inj _ ?_)
  have := units_mul_relation_rearrange_commRing _ _ _ _ _ _ _ _ _ _ e₁ e₂
    (diff1 K h hh k θ hθ h0 φ₀ φ₁ a e₁ d₀ d₁ m₁ s₁ p₁ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₁ φ₃ b e₂ d₁ d₃ m₂ s₂ p₃ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₀ φ₂ b e₂ d₀ d₂ m₂ s₂ p₂ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₂ φ₃ a e₁ d₂ d₃ m₁ s₁ p₄ _ _ rfl rfl) (p₁ _) (p₂ _)
  exact (congrArg (· * e₁ * e₂) (map_sub φ₀.φ _ _)).trans this

end GlobalTheory.AnPer.ClosedSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosedStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  first | exact @GlobalTheory.AnPer.ClosedSq.connForm_closed | exact GlobalTheory.AnPer.ClosedSq.connForm_closed | (intros; apply GlobalTheory.AnPer.ClosedSq.connForm_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFin
noncomputable section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FreeCusp

theorem charpoly_one {F : Type} [Field F] (M : Matrix (Fin 1) (Fin 1) F) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem rootSum_X_sub_C {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (a : F) :
    rootSum θ k (X - C a) = θ (algebraMap F (AlgebraicClosure F) a) ^ k := by
  unfold rootSum
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]
  simp

theorem cusp_one {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (x : GL (Fin 1) F) :
    cusp θ 1 k x = θ (algebraMap F (AlgebraicClosure F) ((x : Matrix (Fin 1) (Fin 1) F) 0 0)) ^ k := by
  have hs := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  unfold cusp psiG
  rw [psi_eq]
  have hz : ∑ᶠ W : {W : Submodule F (Fin 1 → F) // W ≠ ⊤ ∧ ∀ v ∈ W,
      Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F) v ∈ W},
      psi (rootSum θ k) W.1 ((Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F)).restrict W.2.2) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    have h1 := Submodule.finrank_lt W.2.1
    rw [Module.finrank_fin_fun] at h1
    haveI : Subsingleton W.1 := (Module.finrank_zero_iff (R := F)).mp (by omega)
    exact PsiPrimitive.psi_trivial _ hs _ _
  rw [hz, sub_zero, Matrix.charpoly_toLin', charpoly_one, rootSum_X_sub_C]
  simp

theorem hfree_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ)
    (hk : ¬ k ≡ 0 [MOD Nat.card F - 1]) : HFree (cusp θ 1 k) := by
  intro _
  have hset : {x : GL (Fin 1) F | ∀ i j : Fin 1, (j : ℕ) + 1 < 1 →
      (x : Matrix (Fin 1) (Fin 1) F) i j = (1 : Matrix (Fin 1) (Fin 1) F) i j} = Set.univ :=
    Set.eq_univ_of_forall fun x i j h => absurd h (by omega)
  rw [hset, finsum_mem_univ]
  letI := Fintype.ofFinite (GL (Fin 1) F)
  rw [finsum_eq_sum_of_fintype]
  let f : GL (Fin 1) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F) : F →* AlgebraicClosure F).comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  have hf : ∀ x, f x = cusp θ 1 k x := by
    intro x
    rw [cusp_one]
    simp [f, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [← Finset.sum_congr rfl fun x _ => hf x]
  refine sum_hom_units_eq_zero f ?_
  intro h1
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  let x : GL (Fin 1) F := Matrix.GeneralLinearGroup.mk'' (Matrix.of fun _ _ => (u : F))
    (by rw [Matrix.det_fin_one]; exact u.isUnit)
  have hx : f x = 1 := by rw [h1]; rfl
  have hx' : f x = θ (algebraMap F (AlgebraicClosure F) ((u : F) ^ k)) := by
    simp [f, x, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, map_pow]
  rw [hx', ← map_one θ] at hx
  have hne : algebraMap F (AlgebraicClosure F) ((u : F) ^ k) ≠ 0 := by
    rw [_root_.map_ne_zero]; exact pow_ne_zero _ u.ne_zero
  have h2 := hθ _ _ hne one_ne_zero hx
  rw [← map_one (algebraMap F (AlgebraicClosure F))] at h2
  have h3 : (u : F) ^ k = 1 := (algebraMap F (AlgebraicClosure F)).injective h2
  have h4 : u ^ k = 1 := Units.ext (by simpa using h3)
  have h5 := orderOf_dvd_iff_pow_eq_one.mpr h4
  rw [hu, Nat.card_units] at h5
  exact hk (Nat.modEq_zero_iff_dvd.mpr h5)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

variable {F : Type} [Field F]

def hyp {m : ℕ} (l : Fin m) : Submodule F (Fin m → F) := LinearMap.ker (LinearMap.proj l)

theorem mem_hyp {m : ℕ} (l : Fin m) (v : Fin m → F) : v ∈ hyp l ↔ v l = 0 := by
  simp [hyp]

def dg {m : ℕ} (l : Fin m) (d : F) : Matrix (Fin m) (Fin m) F := Matrix.diagonal fun i => if i = l then d else 1

theorem dg_off {m : ℕ} (l : Fin m) (d : F) (i j : Fin m) (hj : j ≠ l) :
    dg l d i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
  by_cases h : i = j
  · subst h; simp [dg, hj]
  · simp [dg, Matrix.one_apply, h]

theorem mem_nilRad_of {m : ℕ} (l : Fin m) (M : Matrix (Fin m) (Fin m) F)
    (h1 : ∀ i j, j ≠ l → M i j = 0) (h2 : M l l = 0) : Matrix.toLin' M ∈ nilRad (hyp l) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_hyp, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [h2, zero_mul]
    · rw [h1 l j hj, zero_mul]
  · rw [mem_hyp] at hv
    funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [hv, mul_zero]
    · rw [h1 i j hj, zero_mul]

theorem of_mem_nilRad {m : ℕ} (l : Fin m) (h : Module.End F (Fin m → F)) (hh : h ∈ nilRad (hyp l)) :
    (∀ i j, j ≠ l → LinearMap.toMatrix' h i j = 0) ∧ LinearMap.toMatrix' h l l = 0 := by
  refine ⟨fun i j hj => ?_, ?_⟩
  · rw [LinearMap.toMatrix'_apply, hh.2 _ ((mem_hyp l _).2 (Pi.single_eq_of_ne (Ne.symm hj) _))]
    rfl
  · rw [LinearMap.toMatrix'_apply]
    exact (mem_hyp l _).1 (hh.1 _)

theorem det_of_cols {m : ℕ} (l : Fin m) (hl : (l : ℕ) + 1 = m) (M : Matrix (Fin m) (Fin m) F)
    (h : ∀ i j, j ≠ l → M i j = (1 : Matrix (Fin m) (Fin m) F) i j) : M.det = M l l := by
  have hlt : ∀ j : Fin m, j ≠ l → j < l := fun j hj => by
    rw [Fin.lt_iff_val_lt_val]; have := j.2; have : (j : ℕ) ≠ l := fun e => hj (Fin.ext e); omega
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_single l (fun i _ hi => ?_) (fun h' => absurd (Finset.mem_univ l) h')
    rw [h i i hi, Matrix.one_apply_eq]
  · intro i j hij
    have hj : j ≠ l := fun e => by subst e; exact absurd (hlt i (ne_of_gt hij)) (not_lt.2 (le_of_lt hij))
    rw [h i j hj]; exact Matrix.one_apply_ne (ne_of_gt hij)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

theorem hfree_two_le {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k m : ℕ) (hm : 2 ≤ m) :
    HFree (cusp θ m k) := by
  intro _
  letI := Fintype.ofFinite F
  let l : Fin m := ⟨m - 1, by omega⟩
  have hl1 : (l : ℕ) + 1 = m := by simp only [l]; omega
  have hjl : ∀ j : Fin m, (j : ℕ) + 1 < m ↔ j ≠ l := fun j => by
    constructor
    · intro h e; rw [e] at h; omega
    · intro h; have := j.2; have : (j : ℕ) ≠ m - 1 := fun e => h (Fin.ext e); omega
  have hs : IsAdditive (rootSum θ k) := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  haveI : Finite (Module.End F (Fin m → F)) := Finite.of_injective _ DFunLike.coe_injective
  have hN : (nilRad (hyp l) : Set (Module.End F (Fin m → F))).Finite := Set.toFinite _
  have hSf : {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf]
  unfold cusp
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  unfold psiG
  have hNcols : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) → ∀ i j, j ≠ l →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro d h hh i j hj
    rw [map_add (f := _), LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).1 i j hj, add_zero,
      dg_off l d i j hj]
  have hNll : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) l l = d := by
    intro d h hh
    rw [map_add (f := _), LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).2, add_zero]
    simp [dg]
  have hxcols : ∀ x ∈ hSf.toFinset, ∀ i j, j ≠ l →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro x hx i j hj
    exact (hSf.mem_toFinset.1 hx) i j ((hjl j).2 hj)
  have key : ∑ x ∈ hSf.toFinset, psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
      = ∑ p ∈ (Finset.univ.filter (fun d : F => d ≠ 0)) ×ˢ hN.toFinset,
        psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (dg l p.1) + p.2) := by
    refine Finset.sum_bij'
      (fun x _ => ((x : Matrix (Fin m) (Fin m) F) l l,
        Matrix.toLin' ((x : Matrix (Fin m) (Fin m) F) - dg l ((x : Matrix (Fin m) (Fin m) F) l l))))
      (fun p hp => Matrix.GeneralLinearGroup.mk'' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2))
        (by
          have hp' := Finset.mem_product.1 hp
          have h1 := (Finset.mem_filter.1 hp'.1).2
          have h2 := hN.mem_toFinset.1 hp'.2
          rw [det_of_cols l hl1 _ (hNcols _ _ h2), hNll _ _ h2]
          exact h1.isUnit)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hd : (x : Matrix (Fin m) (Fin m) F) l l ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det x).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply, det_of_cols l hl1 _ (hxcols x hx)] at this
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, hN.mem_toFinset.2 ?_⟩
      refine mem_nilRad_of l _ (fun i j hj => ?_) ?_
      · rw [Matrix.sub_apply, hxcols x hx i j hj, dg_off l _ i j hj, sub_self]
      · rw [Matrix.sub_apply]; simp [dg]
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      refine hSf.mem_toFinset.2 fun i j hj => ?_
      exact hNcols _ _ h2 i j ((hjl j).1 hj)
    · intro x hx
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      change LinearMap.toMatrix' _ i j = _
      rw [← map_add (f := _), add_sub_cancel, LinearMap.toMatrix'_toLin']
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      change (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l,
        Matrix.toLin' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2)
          - dg l (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l))) = p
      rw [hNll _ _ h2, map_sub, Matrix.toLin'_toMatrix', add_sub_cancel_left]
    · intro x hx
      congr 1
      rw [map_sub, add_sub_cancel]
  rw [key, Finset.sum_product]
  have hA0 : hyp (F := F) l ≠ ⊥ := by
    intro e
    have h0 : Pi.single (⟨0, by omega⟩ : Fin m) (1 : F) ∈ hyp l :=
      (mem_hyp l _).2 (Pi.single_eq_of_ne (fun e' => by have := congrArg Fin.val e'; simp [l] at this; omega) _)
    rw [e, Submodule.mem_bot] at h0
    have := congr_fun h0 ⟨0, by omega⟩
    simp at this
  have hA1 : hyp (F := F) l ≠ ⊤ := by
    intro e
    have h0 : Pi.single l (1 : F) ∈ hyp l := e ▸ Submodule.mem_top
    rw [mem_hyp] at h0
    simp at h0
  refine Finset.sum_eq_zero fun d _ => ?_
  dsimp only
  rw [← finsum_mem_eq_finite_toFinset_sum]
  refine isPrimitive_psi F _ _ hs (hyp l) hA0 hA1 _ fun v hv => ?_
  rw [mem_hyp] at hv ⊢
  rw [Matrix.toLin'_apply, dg, Matrix.mulVec_diagonal, hv, mul_zero]

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin

theorem hFree_cusp : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  intro F _ _ θ hθ m k h
  rcases h with hm | hk
  · exact FreeCusp.hfree_two_le θ k m hm
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · intro h0; exact absurd h0 (lt_irrefl 0)
      · exact FreeCusp.hfree_one θ hθ k hk
    · exact FreeCusp.hfree_two_le θ k m hm

end GlobalTheory.Shin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFinStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  first | (exact @GlobalTheory.Shin.hFree_cusp) | (exact GlobalTheory.Shin.hFree_cusp) | (intros; apply GlobalTheory.Shin.hFree_cusp  <;> assumption)
end
end
