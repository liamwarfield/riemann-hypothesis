module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PowEntryCommutator
namespace GlobalTheory.PowEntryCommutator

open Matrix

theorem pow_entry_commutator {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ) (c e : Fin n) :
    E a b * ((Matrix.of E) ^ m) c e - ((Matrix.of E) ^ m) c e * E a b =
      (if b = c then ((Matrix.of E) ^ m) a e else 0) -
        (if e = a then ((Matrix.of E) ^ m) c b else 0) := by
  induction m generalizing c e with
  | zero =>
    clear hE
    simp only [pow_zero, Matrix.one_apply]
    by_cases h1 : c = e <;> by_cases h2 : b = c <;> by_cases h3 : e = a <;>
      simp only [h1, h2, h3, if_true, if_false, mul_one, one_mul, mul_zero, zero_mul, sub_self] <;>
      subst_vars <;> simp_all <;> intro h <;> subst h <;> simp_all
  | succ m ih =>
    have hs : ∀ x y : Fin n, ((Matrix.of E) ^ (m + 1)) x y
        = ∑ k, ((Matrix.of E) ^ m) x k * E k y := by
      intro x y; rw [pow_succ, Matrix.mul_apply]; rfl
    have key : ∀ k, E a b * (((Matrix.of E) ^ m) c k * E k e)
          - ((Matrix.of E) ^ m) c k * E k e * E a b
        = (E a b * ((Matrix.of E) ^ m) c k - ((Matrix.of E) ^ m) c k * E a b) * E k e
          + ((Matrix.of E) ^ m) c k * (E a b * E k e - E k e * E a b) := by
      intro k; noncomm_ring
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [key, ih, hE a b]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero]
    split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem target : ∀ {A : Type} [inst : Ring A] {n : ℕ} (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ (a b : Fin n) (m : ℕ) (c e : Fin n),
    E a b * ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e -
      ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e * E a b =
    (if b = c then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) a e
      else (0 : A)) -
    if e = a then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c b
      else (0 : A) :=
  fun E hE a b m c e => pow_entry_commutator E hE a b m c e

end GlobalTheory.PowEntryCommutator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

section GelfandCentral

variable {A : Type} [Ring A] {n : ℕ}

theorem sum_fin_succ_fun_cons {M : Type} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin n) → M) :
    ∑ idx, f idx = ∑ c : Fin n, ∑ idx : Fin k → Fin n, f (Fin.cons c idx) := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp f).symm

theorem pow_of_apply_eq_sum_paths (E : Fin n → Fin n → A) (k : ℕ) (c e : Fin n) :
    (Matrix.of E ^ (k + 1)) c e = ∑ idx : Fin k → Fin n, (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons c idx : Fin (k + 1) → Fin n) a) ((Fin.snoc idx e : Fin (k + 1) → Fin n) a)).prod := by
  induction k generalizing c with
  | zero => simp [Fin.snoc]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_fun_cons]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [List.ofFn_succ (n := k + 1), List.prod_cons, ← Fin.cons_snoc_eq_snoc_cons]
    simp

theorem gelfA_eq_sum_pow (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA E k = ∑ c, (Matrix.of E ^ (k + 1)) c c := by
  rw [gelfA, sum_fin_succ_fun_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_of_apply_eq_sum_paths]
  refine Finset.sum_congr rfl fun idx _ => ?_
  congr 2
  funext a
  congr 1
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · rw [Fin.coeSucc_eq_succ]; simp

theorem comm_pow_of_apply (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ)
    (c e : Fin n) : E a b * (Matrix.of E ^ m) c e - (Matrix.of E ^ m) c e * E a b =
      (if b = c then (Matrix.of E ^ m) a e else 0) - (if e = a then (Matrix.of E ^ m) c b else 0) := by
  first
  | exact @_root_.GlobalTheory.PowEntryCommutator.target
  | exact _root_.GlobalTheory.PowEntryCommutator.target
  | (apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEntryCommutator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEntryCommutator.target ..)

end GelfandCentral

theorem commute_gelfA : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  intro A _ _ n E hE k a b
  rw [← sub_eq_zero, gelfA_eq_sum_pow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  first | exact @GlobalTheory.SmoothForms.commute_gelfA | exact GlobalTheory.SmoothForms.commute_gelfA | (intros; apply GlobalTheory.SmoothForms.commute_gelfA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.QuadNormBase

theorem norm_of_basis {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • B 0 + y • B 1) * B 0 = x • B 0 + y • B 1 := by rw [h0, mul_one]
  have e1 : (x • B 0 + y • B 1) * B 1 = (y * d) • B 0 + x • B 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, smul_smul, add_comm]
    congr 1
    rw [h0, one_mul]
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp
  ring

theorem exists_basis (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨x0, hx0⟩ := hne
  have hsm : ∀ (c : F) (e : E), σ (c • e) = c • σ e := fun c e => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  set θ : E := x0 - σ x0 with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hx0.symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add (f := _), hsm, hsm, map_one, hσθ, map_zero, smul_neg] at h2
    have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hst - h2
    have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
    have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right hθ0
    subst ht
    exact ⟨by simpa using hst, rfl⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hrep := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hb0, hb1] at hrep
  set s := b.repr (θ * θ) 0
  set t := b.repr (θ * θ) 1
  have h2 := congrArg σ hrep
  rw [map_add (f := _), hsm, hsm, map_one, map_mul, hσθ, smul_neg] at h2
  have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hrep - h2
  have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
  have hsq : θ * θ = algebraMap F E s := by
    rw [← hrep, h4, add_zero, Algebra.algebraMap_eq_smul_one]
  refine ⟨s, b, ?_, hb0, by rw [hb1, hσθ], by rw [hb1, hsq]⟩
  rintro ⟨r, hr⟩
  rw [hr, map_mul, mul_self_eq_mul_self_iff] at hsq
  have hfix : σ θ = θ := by
    rcases hsq with h | h
    · rw [h, AlgHom.commutes]
    · rw [h, map_neg, AlgHom.commutes]
  have h5 : (2 : E) * θ = 0 := by linear_combination hσθ - hfix
  exact hθ0 (by simpa only [mul_eq_zero, two_ne_zero, false_or] using h5)

theorem norm_form : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  intro F E _ _ _ _ σ hr hσ hne
  obtain ⟨δ, b, hδ, hb0, hb1, hsq⟩ := exists_basis F E σ hr hσ hne
  refine ⟨δ, hδ, ?_⟩
  intro R _ _
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  refine ⟨fun z => ?_, fun x y => ⟨_, key x y⟩⟩
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two] at hz
  refine ⟨B.repr z 0, B.repr z 1, ?_, ?_⟩
  · rw [← norm_of_basis B _ h0 h1, hz]
  · rw [← key, hz]

end GlobalTheory.QuadNormBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebraStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticExt_norm_form_over_algebra : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  first | exact @GlobalTheory.QuadNormBase.norm_form | exact GlobalTheory.QuadNormBase.norm_form | (intros; apply GlobalTheory.QuadNormBase.norm_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.DerLinear

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem anti_exp (H : IsLieData σ j s) (a : 𝔸) : σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let f : 𝔸 →+* 𝔸ᵐᵒᵖ :=
    { toFun := fun b => MulOpposite.op (σ b)
      map_one' := by simp [H.one]
      map_mul' := fun b c => by simp [H.anti]
      map_zero' := by simp
      map_add' := fun b c => by simp }
  have hf : Continuous f := MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)
  have h := NormedSpace.map_exp f hf a
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact h

theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hs : σ (j X) = -j X := (H.skew (j X)).2 ⟨X, rfl⟩
  rw [anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel,
    NormedSpace.exp_zero]

theorem contDiff_exp (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by
  have : FiniteDimensional ℝ L := Module.Finite.of_injective j H.inj
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact hexp.comp (LinearMap.toContinuousLinearMap j).contDiff

omit [FiniteDimensional ℝ 𝔸] in
theorem der_eq_fderiv {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by
  have hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0 :=
    ((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0
  have hd : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X) := by
    rw [zero_smul]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hd).deriv

theorem sm_der (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    Sm (expMap j s) (Der (expMap j s) X φ) := by
  intro g
  have hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1 := exp_unitary H
  let c : L × ℝ → 𝔸 := fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))
  have hcd : ContDiff ℝ ∞ c :=
    ((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hcu : ∀ p, σ (c p) * c p = 1 := by
    intro p
    simp only [c]
    rw [H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]
  have hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0 := fun g => (hφ g).contDiffAt
  have hF := contDiff_family H hl hφ0 hcd hcu g
  have key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) =
      fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ)) := by
    intro Y
    have h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t))) := by
      funext t
      simp only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]
    have hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)
    have hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p)))
        (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0) :=
      ((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt
    show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _
    rw [h1]
    exact (hFd.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp_rw [key]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

end GlobalTheory.SmoothForms.DerLinear

namespace GlobalTheory.SmoothForms

theorem der_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ
  refine ⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩
  · funext g
    rw [Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add (f := _)]
  · funext g
    rw [Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul,
      smul_eq_mul]

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinearStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  first | exact @GlobalTheory.SmoothForms.der_smooth_and_linear | exact GlobalTheory.SmoothForms.der_smooth_and_linear | (intros; apply GlobalTheory.SmoothForms.der_smooth_and_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hp : ∀ n : ℕ, σ (X ^ n) = σ X ^ n := fun n => by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, anti, ih, pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).map σ.toAddMonoidHom
    σ.continuous_of_finiteDimensional
  refine h1.unique ?_
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ X) using 1
  funext n
  simp [hp]

theorem exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hc : ContDiffAt ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) 0).contDiffAt
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := hasFDerivAt_exp_zero
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse hd hn, ?_, ?_, (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  · have := hc.to_localInverse hd hn
    rwa [NormedSpace.exp_zero] at this
  · have := (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at this
    exact this

theorem hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j := by
  first | exact @GlobalTheory.SmoothForms.hasLog_of_isLieData | exact GlobalTheory.SmoothForms.hasLog_of_isLieData | (intros; apply GlobalTheory.SmoothForms.hasLog_of_isLieData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracket
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracket
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.Bracket

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

private theorem isLieData_map_pow (H : IsLieData σ j s) (x : 𝔸) (n : ℕ) : σ (x ^ n) = σ x ^ n := by
  induction n with
  | zero => simpa using H.one
  | succ n ih => rw [pow_succ, H.anti, ih, pow_succ']

private theorem isLieData_map_exp (H : IsLieData σ j s) (x : 𝔸) :
    σ (NormedSpace.exp x) = NormedSpace.exp (σ x) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  have := (LinearMap.toContinuousLinearMap σ).map_tsum hs
  simpa [LinearMap.coe_toContinuousLinearMap', map_smul, isLieData_map_pow H] using this

theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hb : ∀ y : 𝔸, y ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := fun y =>
    (NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  rw [isLieData_map_exp H, (H.skew (j X)).2 ⟨X, rfl⟩,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_left (Commute.refl _)) (hb _) (hb _),
    neg_add_cancel, NormedSpace.exp_zero]

omit [FiniteDimensional ℝ 𝔸] in
theorem unitary_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) :
    σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem hasDerivAt_exp (A : 𝔸) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)

theorem der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ} {a : 𝔸} (ha : σ a * a = 1)
    (hF : DifferentiableAt ℝ F a) (he : ∀ᶠ h in 𝓝 a, σ h * h = 1 → φ (g * s h) = F h) (Y : L) :
    Der (expMap j s) Y φ (g * s a) = fderiv ℝ F a (a * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (a * j Y) 0 :=
    (hasDerivAt_exp (j Y)).const_mul a
  have hc0 : a * NormedSpace.exp ((0 : ℝ) • j Y) = a := by
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j Y)) * NormedSpace.exp (t • j Y) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • Y)
  have hFd : HasFDerivAt F (fderiv ℝ F a) (a * NormedSpace.exp ((0 : ℝ) • j Y)) := by
    rw [hc0]; exact hF.hasFDerivAt
  have hFc := hFd.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have hlim : Filter.Tendsto (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (𝓝 0) (𝓝 a) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have heq : (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (a * NormedSpace.exp (t • j Y))) := by
    filter_upwards [hlim.eventually he] with t ht
    have hm : g * s a * s (NormedSpace.exp (j (t • Y))) = g * s (a * NormedSpace.exp (t • j Y)) := by
      rw [j.map_smul t Y, mul_assoc, ← H.mul a _ ha (hu t)]
    show φ (g * s a * s (NormedSpace.exp (j (t • Y)))) = _
    rw [hm]
    exact ht (unitary_mul H ha (hu t))
  show deriv (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) 0 = _
  exact (hFc.congr_of_eventuallyEq heq).deriv

theorem der_der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ}
    (hF : ContDiffAt ℝ 2 F 1) (he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = F h) (X Y : L) :
    Der (expMap j s) X (Der (expMap j s) Y φ) g =
      fderiv ℝ (fderiv ℝ F) 1 (j X) (j Y) + fderiv ℝ F 1 (j X * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • j X)) (j X) 0 := hasDerivAt_exp (j X)
  have hc0 : NormedSpace.exp ((0 : ℝ) • j X) = 1 := by rw [zero_smul, NormedSpace.exp_zero]
  have hlim : Filter.Tendsto (fun t : ℝ => NormedSpace.exp (t • j X)) (𝓝 0) (𝓝 1) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j X)) * NormedSpace.exp (t • j X) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • X)
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ F) 1 := hF.fderiv_right (by norm_num)
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) 1) (NormedSpace.exp ((0 : ℝ) • j X)) := by
    rw [hc0]; exact (hF1.differentiableAt one_ne_zero).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)))
      (fderiv ℝ (fderiv ℝ F) 1 (j X)) 0 := hA.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have h3 := h1.clm_apply (hcd.mul_const (j Y))
  have hd : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hev : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y ∧
      ∀ᶠ h in 𝓝 y, σ h * h = 1 → φ (g * s h) = F h := hd.and he.eventually_nhds
  have heq : (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)) (NormedSpace.exp (t • j X) * j Y)) := by
    filter_upwards [hlim.eventually hev] with t ht
    show Der (expMap j s) Y φ (g * s (NormedSpace.exp (j (t • X)))) = _
    rw [j.map_smul t X]
    exact der_eq H (hu t) ht.1 ht.2 Y
  show deriv (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) 0 = _
  rw [(h3.congr_of_eventuallyEq heq).deriv, hc0, one_mul]

theorem der_bracket : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G),
    IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L,
    j Z = j X * j Y - j Y * j X →
    Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) =
      Der (expMap j s) Z φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ X Y Z hZ
  funext g
  obtain ⟨Λ, hΛ, hΛ1, -⟩ := hl
  have hFs : ContDiffAt ℝ ∞ (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    (hφ g).contDiffAt.comp (1 : 𝔸) hΛ
  have hF2 : ContDiffAt ℝ 2 (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    hFs.of_le (WithTop.coe_le_coe.2 le_top)
  have he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = φ (g * expMap j s (Λ h)) := by
    filter_upwards [hΛ1] with h hh hu
    show φ (g * s h) = φ (g * s (NormedSpace.exp (j (Λ h))))
    rw [hh hu]
  have hs1 : s 1 = 1 := by
    have h11 := H.mul 1 1 (by rw [H.one, one_mul]) (by rw [H.one, one_mul])
    rw [one_mul] at h11
    simpa using h11
  have hZd := der_eq H (a := 1) (g := g) (by rw [H.one, one_mul]) (hF2.differentiableAt two_ne_zero) he Z
  rw [hs1, mul_one, one_mul] at hZd
  have hsym := hF2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [Pi.sub_apply, der_der_eq H hF2 he X Y, der_der_eq H hF2 he Y X, hZd, hZ, map_sub, hsym (j X) (j Y)]
  abel

end GlobalTheory.SmoothForms.Bracket
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracketStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L, j Z = j X * j Y - j Y * j X → Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) = Der (expMap j s) Z φ := by
  first | exact @GlobalTheory.SmoothForms.Bracket.der_bracket | exact GlobalTheory.SmoothForms.Bracket.der_bracket | (intros; apply GlobalTheory.SmoothForms.Bracket.der_bracket <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonal
open Matrix

namespace GlobalTheory.MonomialDiag

private theorem star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      if 0 < x then (1 : ℂ) else -1 := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [star_inv₀, hst,
    show ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      ((x / (Real.sqrt |x| * Real.sqrt |x|) : ℝ) : ℂ) by push_cast; ring, hs]
  split_ifs with h
  · rw [abs_of_pos h, div_self hx, Complex.ofReal_one]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg_self hx]
    push_cast
    ring

private theorem star_sqrt_abs_mul_sign_mul_sqrt_abs_eq (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ) * (if 0 < x then (1 : ℂ) else -1) * ((Real.sqrt |x| : ℝ) : ℂ) =
      (x : ℂ) := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [hst]
  split_ifs with h
  · rw [mul_one, ← Complex.ofReal_mul, hs, abs_of_pos h]
  · rw [mul_neg_one, neg_mul, ← Complex.ofReal_mul, hs, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]
    push_cast
    ring

private theorem Jpq_equiv_apply_eq_ite_sign {n p q : ℕ} (d : Fin n → ℝ) (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, 0 < d i ↔ (e i).isLeft = true) (i j : Fin n) :
    Formalism.UG.Jpq p q (e i) (e j) = if i = j then (if 0 < d i then (1 : ℂ) else -1) else 0 := by
  unfold Formalism.UG.Jpq
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hi := he i
    revert hi
    generalize e i = x
    rcases x with a | a <;> intro hi <;> simp_all
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [if_neg hij]
    revert hne
    generalize e i = x
    generalize e j = y
    rcases x with a | a <;> rcases y with b | b <;> intro hne <;> simp_all

private theorem conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (C : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ i a, C i a = if i = e.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) :
    Cᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * C = Formalism.UG.Jpq p q := by
  ext a b
  have key := Jpq_equiv_apply_eq_ite_sign d e he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at key
  rw [key, Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, hC, hC]
    simp only [↓reduceIte]
    by_cases hab : e.symm a = e.symm b
    · rw [if_pos hab.symm, if_pos hab, hab]
      exact star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign _ (hd _)
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero, zero_mul, zero_mul]
  · intro i _ hi
    rw [hC i b, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : ∀ a i, B a i = if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0) :
    Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · rw [Matrix.conjTranspose_apply, hB, hB]
      simp only [↓reduceIte]
      rw [Jpq_equiv_apply_eq_ite_sign d e he, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        exact star_sqrt_abs_mul_sign_mul_sqrt_abs_eq _ (hd _)
      · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]
    · intro b _ hb
      rw [Matrix.conjTranspose_apply, hB, if_neg hb, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [hB a j, if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_monomial : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  intro n p q G Q d hG hQ hd hQG
  classical
  obtain ⟨hcard, Q₁, hQ₁⟩ := Formalism.UG.P.sig_data G p q hG
  rw [Fintype.card_fin] at hcard

  let e₀ : Fin n ≃ Fin (Fintype.card {i // 0 < d i}) ⊕ Fin (Fintype.card {i // ¬ 0 < d i}) :=
    (Equiv.sumCompl (fun i => 0 < d i)).symm.trans
      (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
  have he₀ : ∀ i, 0 < d i ↔ (e₀ i).isLeft = true := by
    intro i
    by_cases h : 0 < d i
    · simp [e₀, h]
    · simp [e₀, h]
  have hn₀ : n = Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} := by
    simpa using Fintype.card_congr e₀

  have h₂ : (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
      G * (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0)) =
      Formalism.UG.Jpq _ _ := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
          (Qᴴ * G * Q) * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hQG]
          exact conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq d hd e₀ he₀ _ (fun i a => rfl)
  have i1 := Formalism.UG.P.sig_dim G Q₁ hQ₁ _ h₂
  have i2 := Formalism.UG.P.sig_dim G _ h₂ Q₁ hQ₁
  rw [Fintype.card_fin] at i1 i2
  have hp : Fintype.card {i // 0 < d i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < d i} = q := by omega
  let e : Fin n ≃ Fin p ⊕ Fin q := e₀.trans (Equiv.sumCongr (finCongr hp) (finCongr hq))
  have he : ∀ i, 0 < d i ↔ (e i).isLeft = true := by
    intro i
    rw [he₀ i]
    simp only [e, Equiv.trans_apply]
    cases e₀ i <;> rfl
  let B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
    Matrix.of (fun a i => if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0)
  have hB : Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) :=
    conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal d hd e he B (fun a i => rfl)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hQQ : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQu
  have hQQ' : (Q⁻¹)ᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  refine ⟨B * Q⁻¹, ?_, ?_⟩
  · calc (B * Q⁻¹)ᴴ * Formalism.UG.Jpq p q * (B * Q⁻¹) = (Q⁻¹)ᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * Q⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᴴ * (Qᴴ * G * Q) * Q⁻¹ := by rw [hB, hQG]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * G * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hQQ', hQQ, Matrix.one_mul, Matrix.mul_one]
  · intro a i j hi hj
    have hBQ : B * Q⁻¹ * Q = B := by
      rw [Matrix.mul_assoc, Q.nonsing_inv_mul hQu, Matrix.mul_one]
    rw [hBQ] at hi hj
    have hai : a = e i := by
      by_contra h
      exact hi (by simp [B, h])
    have haj : a = e j := by
      by_contra h
      exact hj (by simp [B, h])
    exact e.injective (hai.symm.trans haj)

end GlobalTheory.MonomialDiag
end
