module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
noncomputable section

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wOld (N l : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), a; (N : ℤ) * l, (l : ℤ) * b]

def gaOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (j : ℤ) + a; (N : ℤ), (N : ℤ) * j + l * b], by
    rw [Matrix.det_fin_two_of]; linear_combination h⟩

def trOld (k : ℤ) (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ) : ℍ → ℂ :=
  G + ∑ j ∈ Finset.range l, G ∣[k] gaOld N l a b h j

def ChiInv (k : ℤ) (N M : ℕ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → G ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • G

def CuspAll (k : ℤ) (G : ℍ → ℂ) : Prop :=
  MDiff G ∧ ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt G k

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL
  rw [dite_eq_right hg]
  rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g).det : ℝ) = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_val g hg, ← RingHom.map_det]
  simp

lemma toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  apply Units.ext
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh]
  exact map_mul (Int.castRingHom ℝ).mapMatrix g h

lemma slash_SL_eq (k : ℤ) (γ : SL(2, ℤ)) (G : ℍ → ℂ) : G ∣[k] γ = G ∣[k] toGL (mat γ) := by
  rw [ModularForm.SL_slash]
  congr 1
  apply Units.ext
  rw [toGL_val _ (by simp [mat])]
  ext i j
  simp [mat]

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma sigma_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℂ) : σ g z = z := by
  rw [σ, if_pos hg]
  rfl

lemma slash_scalar (k : ℤ) (c : ℝ) (hc : 0 < c) (G : ℍ → ℂ) :
    G ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')) = ((c : ℂ) ^ (k - 2)) • G := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val = c ^ 2 := by
    simp [Matrix.GeneralLinearGroup.det_scalar]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val := by
    rw [hdet]; positivity
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ModularForm.slash_apply, sigma_pos hpos, hdet, abs_of_pos (by positivity),
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  have he : (c : ℂ) ^ (k - 2) = (c : ℂ) ^ (((2 : ℕ) : ℤ) * (k - 1)) * (c : ℂ) ^ (-k) := by
    rw [← zpow_add₀ hc']
    congr 1
    push_cast
    ring
  rw [he]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g hg.ne']
  exact_mod_cast hg

lemma smul_slash_toGL (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (c : ℂ) (G : ℍ → ℂ) :
    (c • G) ∣[k] toGL M = c • (G ∣[k] toGL M) := by
  rw [ModularForm.smul_slash, sigma_pos (toGL_det_pos M hM)]

lemma toGL_smul (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    toGL ((c : ℤ) • g) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c : ℝ) (by positivity)) * toGL g := by
  have h1 : ((c : ℤ) • g).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hg, hc.ne']
  apply Units.ext
  rw [Units.val_mul, toGL_val _ h1, toGL_val _ hg, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul,
    Units.val_mk0, Matrix.smul_apply, smul_eq_mul]
  simp

lemma slash_toGL_smul (k : ℤ) (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det)
    (G : ℍ → ℂ) : G ∣[k] toGL ((c : ℤ) • g) = ((c : ℂ) ^ (k - 2)) • (G ∣[k] toGL g) := by
  rw [toGL_smul c hc g hg.ne', SlashAction.slash_mul, slash_scalar k (c : ℝ) (by positivity),
    smul_slash_toGL k g hg, Complex.ofReal_natCast]

lemma ulFam_det (l : ℕ) (hl : 0 < l) (j : Fin l) : 0 < (ulFam l j).det := by
  simp [ulFam, Matrix.det_fin_two_of]
  exact_mod_cast hl

lemma ulF_add (k : ℤ) (l : ℕ) (F G : ℍ → ℂ) : UlF k l (F + G) = UlF k l F + UlF k l G := by
  simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]

lemma ulF_smul (k : ℤ) (l : ℕ) (hl : 0 < l) (c : ℂ) (F : ℍ → ℂ) : UlF k l (c • F) = c • UlF k l F := by
  simp only [UlF, hkF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_slash_toGL k _ (ulFam_det l hl j) c F

lemma ulF_sub (k : ℤ) (l : ℕ) (hl : 0 < l) (F G : ℍ → ℂ) : UlF k l (F - G) = UlF k l F - UlF k l G := by
  have h := ulF_smul k l hl (-1) G
  rw [sub_eq_add_neg, ulF_add, sub_eq_add_neg]
  congr 1
  simpa using h

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices
open CongruenceSubgroup

lemma chiInv_add {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F G : ℍ → ℂ} (hF : ChiInv k N M χ F)
    (hG : ChiInv k N M χ G) : ChiInv k N M χ (F + G) := by
  intro γ hγ
  rw [SlashAction.add_slash, hF γ hγ, hG γ hγ, smul_add]

lemma chiInv_smul {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} (c : ℂ) (hF : ChiInv k N M χ F) :
    ChiInv k N M χ (c • F) := by
  intro γ hγ
  rw [ModularForm.SL_smul_slash, hF γ hγ, smul_comm]

lemma cuspAll_add {k : ℤ} {F G : ℍ → ℂ} (hF : CuspAll k F) (hG : CuspAll k G) : CuspAll k (F + G) := ⟨hF.1.add hG.1, fun c hc => (hF.2 c hc).add (hG.2 c hc)⟩

lemma cuspAll_smul {k : ℤ} {F : ℍ → ℂ} (c : ℂ) (hF : CuspAll k F) : CuspAll k (c • F) := by
  refine ⟨hF.1.const_smul c, fun p hp g hg => ?_⟩
  rw [ModularForm.smul_slash]
  exact Filter.ZeroAtFilter.smul _ (hF.2 p hp g hg)

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivativeCyclotomicMul
open GlobalTheory.K5 Polynomial TrivSqZeroExt

noncomputable section
namespace GlobalTheory.K5.DlogUniq

section generic
variable {R : Type*} [CommRing R]

theorem aeval_dual {S : Type*} [CommRing S] [Algebra R S] (a m : S) (f : R[X]) :
    (aeval (inl a + inr m : DualNumber S) f).fst = aeval a f ∧
    (aeval (inl a + inr m : DualNumber S) f).snd = aeval a (derivative f) * m := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add (f := _), fst_add, snd_add, hf.1, hf.2, hg.1, hg.2, map_add (f := _), map_add (f := _), map_add (f := _), add_mul]
    exact ⟨rfl, rfl⟩
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, derivative_monomial, aeval_monomial]
    constructor
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_pow]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_pow]
      ring

theorem exists_derivation (Φ : R[X]) (N : ℕ) (q : R) (I : Ideal R[X][X])
    (hI : I = Ideal.span {C Φ, X ^ N - C (C q)}) (S : Type*) [CommRing S] [Algebra R S]
    [Algebra (R[X][X] ⧸ I) S] [IsScalarTower R (R[X][X] ⧸ I) S] (mx my : S)
    (hx : algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) (derivative Φ)) * mx = 0)
    (hy : (N : S) * my = 0) :
    ∃ D : Derivation R (R[X][X] ⧸ I) S,
      D (Ideal.Quotient.mk I (C X)) = mx ∧ D (Ideal.Quotient.mk I X) = my := by
  let π : R[X][X] →+* S := (algebraMap (R[X][X] ⧸ I) S).comp (Ideal.Quotient.mk I)
  let ψ0 : R[X][X] →+* DualNumber S :=
    eval₂RingHom (aeval (inl (π (C X)) + inr mx : DualNumber S) : R[X] →ₐ[R] DualNumber S).toRingHom
      (inl (π X) + inr my)
  have hC : ∀ f : R[X], ψ0 (C f) = aeval (inl (π (C X)) + inr mx : DualNumber S) f := by
    intro f; simp [ψ0]
  have hX : ψ0 X = inl (π X) + inr my := by simp [ψ0]
  have hπC : ∀ f : R[X], aeval (π (C X)) f = π (C f) := by
    intro f
    have : (aeval (π (C X)) : R[X] →ₐ[R] S).toRingHom = π.comp C := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
        exact IsScalarTower.algebraMap_apply R (R[X][X] ⧸ I) S a
      · simp
    exact congrArg (fun g => g f) this
  have hπC' : ∀ f : R[X], aeval (π (C X)) f =
      algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) f) := by
    intro f
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R (R[X][X] ⧸ I) S) (Ideal.Quotient.mk I (C X)) f)
  have hfst : ∀ f, (ψ0 f).fst = π f := by
    intro f
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp ψ0 = π := by
      apply Polynomial.ringHom_ext
      · intro a
        show (ψ0 (C a)).fst = _
        rw [hC, (aeval_dual _ _ _).1, hπC]
      · show (ψ0 X).fst = _
        rw [hX]; simp
    exact congrArg (fun g => g f) this
  have hπI : ∀ f ∈ I, π f = 0 := by
    intro f hf
    show algebraMap (R[X][X] ⧸ I) S (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hker : ∀ f ∈ I, ψ0 f = 0 := by
    have : I ≤ RingHom.ker ψ0 := by
      have h1 : C Φ ∈ I := hI ▸ Ideal.subset_span (by simp)
      have h2 : X ^ N - C (C q) ∈ I := hI ▸ Ideal.subset_span (by simp)
      refine hI.le.trans (Ideal.span_le.2 ?_)
      rintro f (rfl | rfl)
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h1]; rfl
        · rw [hC, (aeval_dual _ _ _).2, hπC']; exact hx
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h2]; rfl
        · rw [map_sub, map_pow, hX, hC, aeval_C, snd_sub, snd_pow, TrivSqZeroExt.algebraMap_eq_inl']
          simp only [snd_add, snd_inl, snd_inr, zero_add, sub_zero, snd_zero, smul_eq_mul, nsmul_eq_mul]
          rw [mul_left_comm, hy, mul_zero]
    exact fun f hf => this hf
  let ψ : (R[X][X] ⧸ I) →+* DualNumber S := Ideal.Quotient.lift I ψ0 hker
  have hψ : ∀ z, (ψ z).fst = algebraMap (R[X][X] ⧸ I) S z := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hfst f
  have hleib : ∀ a b, (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd := by
    intro a b
    rw [map_mul, DualNumber.snd_mul, hψ, hψ, Algebra.smul_def, Algebra.smul_def, mul_comm (ψ a).snd]
  have halg : ∀ c : R, (ψ (algebraMap R _ c)).snd = 0 := by
    intro c
    show (ψ0 (C (C c))).snd = 0
    rw [hC, (aeval_dual _ _ _).2]; simp
  let L : (R[X][X] ⧸ I) →ₗ[R] S :=
    { toFun := fun z => (ψ z).snd
      map_add' := fun a b => by rw [RingHom.map_add ψ, snd_add]
      map_smul' := fun c z => by
        rw [Algebra.smul_def, hleib, halg, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' L hleib, ?_, ?_⟩
  · show (ψ0 (C X)).snd = mx
    rw [hC]; simp
  · show (ψ0 X).snd = my
    rw [hX]; simp

end generic

variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_quot {A : Type*} [CommRing A] (k l : ℕ) :
    ((k ^ l : ℕ) : A ⧸ Ideal.span {(k : A) ^ l}) * 1 = 0 := by
  rw [mul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(k : A) ^ l})),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

theorem aeval_xn (n : ℕ) (f : (O0 p)[X]) :
    aeval (xn p n) f = Ideal.Quotient.mk (towerIdeal p n) (C f) := by
  have : (aeval (xn p n) : (O0 p)[X] →ₐ[O0 p] On p n).toRingHom =
      (Ideal.Quotient.mk (towerIdeal p n)).comp C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
      rfl
    · simp [xn]
  exact congrArg (fun g => g f) this

theorem aeval_xn_cyclotomic (n : ℕ) : aeval (xn p n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  rw [aeval_xn, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem isUnit_xn (m : ℕ) : IsUnit (xn p (m + 1)) := by
  have h := congrArg (aeval (xn p (m + 1))) (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  rw [map_mul, aeval_xn_cyclotomic, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact IsUnit.of_pow_eq_one (sub_eq_zero.1 h.symm) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem isUnit_yn (n : ℕ) : IsUnit (yn p n) := by
  have hq : IsUnit (qO p) := by
    refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
    rw [HahnSeries.single_mul_single]; simp
  have h : yn p n ^ (p ^ n) = Ideal.Quotient.mk (towerIdeal p n) (C (C (qO p))) := by
    rw [yn, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)
  have h2 : IsUnit (yn p n ^ (p ^ n)) := h ▸ ((hq.map _).map _).map _
  exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h2

theorem derivative_cyclotomic_mul (m : ℕ) :
    aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p))) * (xn p (m + 1) ^ p ^ m - 1) =
      (p : On p (m + 1)) ^ (m + 1) * xn p (m + 1) ^ (p ^ (m + 1) - 1) := by
  have h := congrArg (fun f => aeval (xn p (m + 1)) (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, map_add (f := _), map_mul, aeval_xn_cyclotomic, zero_mul, add_zero] at h
  simpa [derivative_X_pow] using h

end GlobalTheory.K5.DlogUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGamma0
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_transform {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (A B C D : ℤ) (hdet : A * D - B * C = 1)
    (hA : (A : ZMod N) = 1) (hD : (D : ZMod N) = 1) (hCN : (C : ZMod N) = 0)
    (hCl : (C : ZMod l) = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex ((A * z + B) / (C * z + D))) = (C * z + D) ^ k * f (ofComplex z) := by
  let g : SL(2, ℤ) := ⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩
  have hg : g ∈ lev N l := by
    refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]
  let w : ℍ := ⟨z, hz⟩
  have h1 := congrFun (hf g hg) w
  rw [SL_slash_apply] at h1
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D := by
    have e1 : g 1 0 = C := rfl
    have e2 : g 1 1 = D := rfl
    have := (show denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by
      simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])
    rw [this, e1, e2]
  have hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D) := by
    rw [specialLinearGroup_apply]; simp [g, w]
  have hne : (C * z + D : ℂ) ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hw : ofComplex z = w := ofComplex_apply_of_im_pos hz
  rw [← hsm, ofComplex_apply, hw, ← h1, zpow_neg]
  field_simp

theorem lev_periodic {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (z + 1)) = f (ofComplex z) := by
  have h := lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz
  simpa using h

theorem sum_range_affine {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Function.Periodic F q)
    (u v : ℤ) (hu : ∃ w : ZMod q, w * u = 1) :
    ∑ j ∈ Finset.range q, F (v + u * j) = ∑ j ∈ Finset.range q, F j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let G : ZMod q → ℂ := fun x => F (x.val : ℤ)
  have hFG : ∀ m : ℤ, F m = G m := by
    intro m
    simp only [G, ZMod.val_intCast]
    have := (hF.int_mul (m / q)) (m % q)
    rw [← this]; congr 1
    rw [Int.cast_id]; linear_combination (Int.mul_ediv_add_emod m q).symm
  have hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x := by
    intro H
    symm
    refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j _; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _; rw [ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := hu
  have hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have : (u : ZMod q) * x = u * y := add_left_cancel hxy
    calc x = w * (u * x) := by rw [← mul_assoc, hw, one_mul]
      _ = y := by rw [this, ← mul_assoc, hw, one_mul]
  calc ∑ j ∈ Finset.range q, F (v + u * j)
      = ∑ j ∈ Finset.range q, G ((v : ZMod q) + u * (j : ZMod q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl
    _ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))
    _ = ∑ x, G x := hbij.sum_comp G
    _ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm
    _ = ∑ j ∈ Finset.range q, F j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl

theorem uOp_slash_lev : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    (∀ γ ∈ lev N l, f ∣[k] γ = f) → ∀ γ ∈ lev N l, uOp q f ∣[k] γ = uOp q f := by
  intro N l q k f _ _ hq hqNl hf γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha, hd, hcN⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hqc : (q : ℤ) ∣ γ 1 0 := by
    rcases hq.dvd_mul.1 hqNl with h | h
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)
  obtain ⟨t, ht⟩ := hqc
  funext τ
  rw [SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [specialLinearGroup_apply]; simp
  have hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  set a := γ 0 0 with ha_def
  set b := γ 0 1 with hb_def
  set c := γ 1 0 with hc_def
  set d := γ 1 1 with hd_def
  let F : ℤ → ℂ := fun m => f (ofComplex (((τ : ℂ) + m) / q))
  have hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im := by
    intro m
    have : (((τ : ℂ) + m) / q).im = τ.im / q := by simp [Complex.div_natCast_im]
    rw [this]; exact div_pos τ.im_pos hqpos
  have hper : Function.Periodic F (q : ℤ) := by
    intro m
    have e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1 := by
      push_cast; field_simp; ring
    show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))
    rw [e]; exact lev_periodic hf _ (hzim m)
  have hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) =
      (c * τ + d) ^ k * F (d * b + d * d * j) := by
    intro j
    set j' : ℤ := d * b + d * d * j with hj'
    set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def
    have he : e * q = b + j * d - (a + j * c) * j' := by
      rw [he_def, hj']
      linear_combination (b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht
    have heC : (e : ℂ) * q = b + j * d - (a + j * c) * j' := by exact_mod_cast he
    have h := lev_transform hf (a + j * c) e (q * c) (d - c * j')
      (by linear_combination hdet - c * he)
      (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN])
      (by push_cast; simp [h0]) _ (hzim j')
    have hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d := by
      push_cast; field_simp; ring
    rw [hCD] at h
    have harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) =
        ((a * τ + b) / (c * τ + d) + j) / q := by
      push_cast
      field_simp
      linear_combination heC
    rw [harg] at h
    exact h
  have hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1 := by
    refine ⟨(a : ZMod q) * a, ?_⟩
    have h := congrArg (Int.cast : ℤ → ZMod q) hdet
    rw [ht] at h
    push_cast at h
    rw [ZMod.natCast_self] at h
    push_cast
    linear_combination ((a : ZMod q) * d + 1) * h
  unfold uOp
  rw [hsm, hden]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]
  have hF : ∑ j ∈ Finset.range q, F j =
      ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q)) := by simp [F]
  rw [hF, zpow_neg]
  field_simp

end GlobalTheory.Hk
end

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) → ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.uOp q f ∣[k] γ = GlobalTheory.Hk.uOp q f := by
  first | exact @GlobalTheory.Hk.uOp_slash_lev | exact GlobalTheory.Hk.uOp_slash_lev | (intros; apply GlobalTheory.Hk.uOp_slash_lev <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.NormFormGauss

theorem card_eq_sq {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by
  let T : k →+ k := s.toAddMonoidHom - AddMonoidHom.id k
  have hT : ∀ x, T x = s x - x := fun x => rfl
  have h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [AddMonoidHom.mem_ker, hT, sub_eq_zero]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have h4 : Nat.card T.range = Nat.card T.ker := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)
    · have hu : s u = u := by
        have := u.2
        rw [AddMonoidHom.mem_ker, hT, sub_eq_zero] at this
        exact this
      rw [hT, map_mul, hu]; ring
    · intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (mul_left_cancel₀ hr this)
    · rintro ⟨_, t, rfl⟩
      refine ⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]
        field_simp
        ring
      · apply Subtype.ext
        simp only [hT]
        field_simp
  rw [← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]

theorem sum_norm_units {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    ∃ m : ℕ, Fintype.card kˣ = m * (Finset.univ.filter (fun x : kˣ => s x = x)).card ∧
      ∀ f : k → ℂ, ∑ x : kˣ, f (x * s x) =
        m * ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y := by
  let S : kˣ →* kˣ := Units.map s.toMonoidHom
  have hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x := fun x => rfl
  let N : kˣ →* kˣ := MonoidHom.id _ * S
  let D : kˣ →* kˣ := MonoidHom.id _ / S
  have hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x := fun x => rfl
  have hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x := fun x => by
    simp [D, hS]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have hne : ∀ x : kˣ, s x ≠ 0 := fun x => by simp
  have hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]
  have hker : N.ker = D.range := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]
    constructor
    · intro hx
      by_cases h : (1 + x : k) = 0
      · refine ⟨Units.mk0 _ hr, Units.ext ?_⟩
        rw [hD, Units.val_mk0, hθ, div_neg, div_self hr]
        linear_combination -h
      · refine ⟨Units.mk0 _ h, Units.ext ?_⟩
        have h' := hne (Units.mk0 _ h)
        rw [hD, div_eq_iff h', Units.val_mk0, map_add (f := _), map_one]
        linear_combination -hx
    · rintro ⟨y, rfl⟩
      rw [hD, map_div₀, hs]
      have := hne y
      have := y.ne_zero
      field_simp
  have c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
  have c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]
  have c3 : Nat.card N.range = Nat.card D.ker := by
    rw [← hker, c1, mul_comm] at c2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos c2
  have hle : N.range ≤ D.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hDk, hN, map_mul, hs, mul_comm]
  have hr' : N.range = D.ker := Subgroup.eq_of_le_of_card_ge hle c3.ge
  have c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, hDk]
  refine ⟨Nat.card N.ker, ?_, fun f => ?_⟩
  · rw [← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]
  · have himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x) := by
      ext x
      simp only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    have := Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N
    simp only [hN] at this
    rw [this, ← himg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nsmul_eq_mul]
    congr 2
    have hy' : y ∈ Set.range N := by simpa using hy
    rw [MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1

theorem sum_eq_zero_add_units {k : Type} [Field k] [Fintype k] {M : Type} [AddCommMonoid M]
    (g : k → M) : ∑ x : k, g x = g 0 + ∑ x : kˣ, g x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
  congr 1
  symm
  refine Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro b hb
    exact ⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩
  · intro a _; rfl

theorem gauss_field {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by
  obtain ⟨m, hm, hsum⟩ := sum_norm_units s hs r hr
  have hq := card_eq_sq s hs r hr
  set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef
  set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef
  have hqa : q = 1 + a := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)
    rw [hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]
  have ha : 0 < a := Finset.card_pos.2 ⟨1, by simp⟩
  have hcard : Fintype.card k = 1 + Fintype.card kˣ := by
    have := sum_eq_zero_add_units (fun _ : k => (1 : ℕ))
    simpa using this
  have hmq : m = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right ha
    rw [hm, hq, hqa] at hcard
    rw [hqa]
    nlinarith
  have hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) =
        ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y := by
      refine Finset.sum_equiv (Equiv.addLeft u) ?_ ?_
      · intro i; simp [hu]
      · intro i _; rfl
    simp only [hadd, ← Finset.mul_sum] at h1
    have h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)
  have hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1 := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)
    rw [← Finset.sum_filter, hz, ← Finset.sum_filter] at this
    simp only [map_zero, if_true, h0] at this
    linear_combination -this
  rw [sum_eq_zero_add_units, hsum, hu1, hq, hmq]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp [h0]

theorem gauss_quotient : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by
  intro R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ (fun r hr => hst r hr)
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
  have hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q := fun q => Quotient.out_eq q
  have hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b := by
    intro a b h
    have h1 := hχP _ (Ideal.Quotient.eq.1 h)
    have h2 := hadd (a - b) b
    rw [h1, one_mul, sub_add_cancel] at h2
    exact h2
  let f : R ⧸ P → ℂ := fun q => χ (w * Quotient.out q)
  have hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a) := fun a =>
    hcongr _ _ (by rw [map_mul, map_mul, hout])
  have key := gauss_field s
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, hσ])
    (Ideal.Quotient.mk P r)
    (by
      rw [hs, ← map_sub]
      exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))
    f
    (fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_add (f := _), hf, hf, hf, mul_add, hadd])
    (by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])
    (Ideal.Quotient.mk P (t + σ t))
    (by rw [hs, map_add σ, hσ, add_comm])
    (by
      rw [hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]
      exact ht)
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [← hout q]
  rw [hs, ← map_mul, hf, mul_assoc]

end GlobalTheory.NormFormGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0Level
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0Level
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_mul_inv_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N →
    GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  intro N l d σ τ _ hσ hτ
  obtain ⟨hσc, hσd⟩ := hσ
  obtain ⟨hτc, hτd⟩ := hτ
  have detσ := Matrix.SpecialLinearGroup.det_coe σ
  have detτ := Matrix.SpecialLinearGroup.det_coe τ
  rw [Matrix.det_fin_two] at detσ detτ
  have e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσc hτc
  push_cast at hσc hτc
  have hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0 := by
    rw [e10]
    exact dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)
  have hτN : ((τ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)
  have dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detσ
  have dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detτ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast
      linear_combination (τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ
        + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN
    · rw [e11]; push_cast
      linear_combination (σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ
        + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)
  · rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0LevelStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.dia_mul_inv_mem_lev | exact GlobalTheory.Hk.dia_mul_inv_mem_lev | (intros; apply GlobalTheory.Hk.dia_mul_inv_mem_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCongr
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  intro N l k d σ τ hN hσ hτ f
  have h := GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level N l d σ τ hN hσ hτ
  have hτ' : τ = (τ * σ⁻¹) * σ := by group
  have hinv : ⇑f ∣[k] (τ * σ⁻¹) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ h)
  unfold GlobalTheory.Hk.dia
  rw [hτ', SlashAction.slash_mul, hinv]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCongrStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_congr | exact GlobalTheory.Hk.dia_congr | (intros; apply GlobalTheory.Hk.dia_congr <;> assumption)
end
end
