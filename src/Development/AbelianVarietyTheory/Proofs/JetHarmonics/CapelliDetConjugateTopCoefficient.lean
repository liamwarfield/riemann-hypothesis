module

public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.CapelliTop

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sum_smul {t n : ℕ} (q : Fin t → Fin n → ℂ) (x : Fin t → Fin n → A) :
    (List.ofFn fun k : Fin t => ∑ d, q k d • x k d).prod =
      ∑ d : Fin t → Fin n, (∏ k, q k (d k)) • (List.ofFn fun k => x k (d k)).prod := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply]
  simp only [RingHom.id_apply]

theorem qminor_eq_zero {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (d : Fin n → Fin n)
    (hd : ¬ Function.Injective d) (u : ℂ) : qminor E id d u = 0 := by
  simp only [Function.Injective, not_forall] at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have h := quantumMinorColSkew_holds A n n E hE id d (Equiv.swap i j) u
  have e : d ∘ Equiv.swap i j = d := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [e, Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_add_self_eq_zero
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  exact add_eq_zero_iff_eq_neg.mpr h

theorem det_smul_qdet {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u : ℂ) : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod := by
  classical
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • qminor E id d u := by
    simp only [Finset.smul_sum, qminor]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [prod_ofFn_sum_smul (fun k d => Q k d) (fun k d => Tm E (u - (k : ℂ)) (σ k) d),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  rw [h1, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro d hd
    rw [qminor_eq_zero E hE d, smul_zero]
    intro hinj
    exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.mp hinj), rfl⟩
  · intro τ
    have h := quantumMinorColSkew_holds A n n E hE id id τ u
    rw [Function.id_comp] at h
    rw [h, mul_comm, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl

theorem mul_pow_shift (x y δ : A) (h : x * δ = δ * (x + y)) (hy : y * δ = δ * y) (s : ℕ) :
    x * δ ^ s = δ ^ s * (x + (s : ℂ) • y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, add_mul, h, smul_mul_assoc, hy,
      Nat.cast_succ, add_smul, one_smul, ← mul_smul_comm, ← mul_add]
    congr 2
    abel

theorem prod_ofFn_semiconj {t : ℕ} (x y : Fin t → A) (g : A) (h : ∀ k, x k * g = g * y k) :
    (List.ofFn x).prod * g = g * (List.ofFn y).prod := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ (fun k => h k.succ), ← mul_assoc, h, mul_assoc]

theorem pt_prod {t : ℕ} (x y : Fin t → A) :
    TL.PT t (fun s : ℂ => (List.ofFn fun k => x k + s • y k).prod) (List.ofFn y).prod := by
  induction t with
  | zero => exact (TL.PT.const 1).congr (fun s => by simp) (by simp)
  | succ t ih =>
    have h := ih (fun k => x k.succ) (fun k => y k.succ)
    refine ((h.mulL (x 0)).up.add (h.mulL (y 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem sum_smul_Tm {n : ℕ} (E : Fin n → Fin n → A) (q : Fin n → ℂ) (u : ℂ) (a : Fin n) :
    ∑ d, q d • Tm E u a d = (q a * u) • (1 : A) + ∑ d, q d • E a d := by
  simp [shiftedGenerator_eq_ite_smul_add, Finset.sum_add_distrib, smul_smul, ite_smul]

theorem top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  intro A _ _ p m E Q δ ν u hE h1 h2 h3
  set X : Equiv.Perm (Fin (p + m)) → Fin p → A := fun σ k =>
    ∑ d, Q (Fin.castAdd m k) d • Tm E (u - ((k : ℕ) : ℂ)) (σ (Fin.castAdd m k)) d with hX
  set Y : Equiv.Perm (Fin (p + m)) → A := fun σ => (List.ofFn fun k : Fin m =>
    ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod with hY
  have e1 : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn (X σ)).prod * Y σ) := by
    rw [det_smul_qdet E hE]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [List.ofFn_add, List.prod_append]
    simp only [hX, hY, Fin.val_natAdd, Nat.cast_add, sub_sub]
    rfl
  have eY : ∀ σ (s : ℕ), Y σ * δ ^ s = δ ^ s * Y σ := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => Commute.pow_right (?_ : _ * _ = _ * _) s
    rw [sum_smul_Tm, add_mul, mul_add, h2]
    simp
  have eX : ∀ σ (s : ℕ), (List.ofFn (X σ)).prod * δ ^ s =
      δ ^ s * (List.ofFn fun k => X σ k + (s : ℂ) • ν (σ (Fin.castAdd m k)) k).prod := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => mul_pow_shift _ _ _ ?_ (h3 _ _) s
    simp only [hX]
    rw [sum_smul_Tm, add_mul, h1, add_assoc, mul_add δ (_ • _)]
    simp
  have e2 : ∀ s : Fin (p + 1), Q.det • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) =
      ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (δ ^ p *
        ((List.ofFn fun k => X σ k + ((s : ℕ) : ℂ) • ν (σ (Fin.castAdd m k)) k).prod * Y σ)) := by
    intro s
    rw [← mul_smul_comm, ← smul_mul_assoc, e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, eY, ← mul_assoc _ (δ ^ (s : ℕ)), eX, mul_assoc,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)]
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_comm Q.det, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := (((pt_prod (X σ) (fun k => ν (σ (Fin.castAdd m k)) k)).mulR (Y σ)).mulL (δ ^ p)).lag
  rw [mul_smul_comm]
  refine Eq.trans ?_ (congrArg _ h.symm)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

end GlobalTheory.CapelliTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficientStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_conjugate_top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  first | exact @GlobalTheory.CapelliTop.top_coefficient | exact GlobalTheory.CapelliTop.top_coefficient | (intros; apply GlobalTheory.CapelliTop.top_coefficient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.RhvPoly

inductive IsPol {V : Type} [AddCommGroup V] [Module ℂ V] : (ℂ → V) → Prop
  | const (a : V) : IsPol fun _ => a
  | add {f g : ℂ → V} : IsPol f → IsPol g → IsPol fun y => f y + g y
  | xsmul {f : ℂ → V} : IsPol f → IsPol fun y => y • f y

section module

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end module

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

end alg

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_finset_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → V}
    (hf : ∀ i ∈ s, _root_.GlobalTheory.RhvPoly.IsPol (f i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_pow_smul (n : ℕ) (v : V) : _root_.GlobalTheory.RhvPoly.IsPol fun y : ℂ => y ^ n • v := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    exact ih.xsmul

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eval_smul (p : Polynomial ℂ) (v : V) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => p.eval y • v := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]
  refine isPol_finset_sum _ fun i _ => ?_
  convert isPol_pow_smul i (p.coeff i • v) using 1
  funext y
  exact smul_comm _ _ _

variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_linearMap_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℂ) →ₗ[ℂ] A)
    (p : ι → Polynomial ℂ) : _root_.GlobalTheory.RhvPoly.IsPol fun y => g (fun ρ => (p ρ).eval y) := by
  have h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ) := by
    intro y
    ext ρ'
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_smul]
  exact isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_linearMap_comp (g : V →ₗ[ℂ] W) {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => g (f y) := by
  induction hf with
  | const a => exact .const _
  | add _ _ ihf ihg => simpa only [map_add (f := _)] using ihf.add ihg
  | xsmul _ ih => simpa only [map_smul] using ih.xsmul

variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_mul {f g : ℂ → A} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (hg : _root_.GlobalTheory.RhvPoly.IsPol g) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg
  | add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg
  | xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul

variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_algebraMap_eval (p : Polynomial ℂ) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => algebraMap ℂ A (p.eval y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPol_eval_smul p (1 : A)

variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_list_prod {ι : Type} (l : List ι) {F : ι → ℂ → A}
    (hF : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol (F i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => (l.map fun i => F i y).prod := by
  induction l with
  | nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)
  | cons a l ih => simpa using isPol_mul (hF a) ih

variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_Tvprod' {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvprod y := by
  have hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i := by
    intro i
    have : (fun y => L.Tvl y i) =
        fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0] := by
      funext y
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvl
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    rw [this]
    exact (_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)
  have h : (fun y => L.Tvprod y) =
      fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod := by
    funext y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod
    simp [List.ofFn_eq_map, List.map_reverse]
  rw [h]
  exact isPol_list_prod _ hT

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma exists_polynomial_eq_functional_of_isPol {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (φ : V →ₗ[ℂ] ℂ) :
    ∃ p : Polynomial ℂ, ∀ y, φ (f y) = p.eval y := by
  induction hf with
  | const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, fun y => by simp [hp, hq]⟩
  | xsmul _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨Polynomial.X * p, fun y => by simp [hp]⟩

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eq_zero_of_infinite_zeros {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) {S : Set ℂ}
    (hS : S.Infinite) (h0 : ∀ y ∈ S, f y = 0) (y : ℂ) : f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨p, hp⟩ := exists_polynomial_eq_functional_of_isPol hf φ
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    (hS.mono fun x hx => by simp [← hp, h0 x hx])
  simp [hp, this]

theorem _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A]
    (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite →
    (∀ y ∈ S, _root_.GlobalTheory.HatNF.rhv d y ∈ K) → ∀ y : ℂ, _root_.GlobalTheory.HatNF.rhv d y ∈ K := by
  intro P A _ _ _ d K S hS hmem y
  classical
  have hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y := by
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC
    simp [Polynomial.eval_prod]
  have hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y := by
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.S12
    refine isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.M.xEx
    simp [Polynomial.eval_prod]
  have hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y := by
    have := (_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add
      (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi)))
        (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.m0
    simp [sub_eq_add_neg]
  have hTv := isPol_Tvprod' d.L
  have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j :=
    fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv
  have hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y := by
    have h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y =>
        d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 +
          d.L.GG * d.x y * d.L.Tvprod y 1 0) := by
      funext y
      unfold _root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr
      simp
    rw [h]
    refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12)
      (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))
  have hq := isPol_linearMap_comp K.mkQ hpol
  have := isPol_eq_zero_of_infinite_zeros hq hS
    (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y
  exact (Submodule.Quotient.mk_eq_zero K).1 this

end GlobalTheory.RhvPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfiniteStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightOperatorDual_mem_of_infinite : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite → (∀ y ∈ S, rhv d y ∈ K) → ∀ y : ℂ, rhv d y ∈ K := by
  first | exact @GlobalTheory.RhvPoly.rhv_mem_of_infinite | exact GlobalTheory.RhvPoly.rhv_mem_of_infinite | (intros; apply GlobalTheory.RhvPoly.rhv_mem_of_infinite <;> assumption)
end
end
