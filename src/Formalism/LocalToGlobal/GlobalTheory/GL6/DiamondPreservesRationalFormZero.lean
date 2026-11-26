module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical

variable (D : D7) (u : D.what₂.Word)

def HeckeRationalLevelZero : Prop :=
  ∀ v x, (∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x))

theorem norm_eq_sum_diamond (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    Nm D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, dia D u i v a φ := by
  unfold Nm; rw [LinearMap.sum_apply]

theorem mem_ramified_forms_iff {i : ℕ} (φ : Fn D u i) :
    φ ∈ MramI D u i ↔ φ ∈ (D.fm u).Fi i ∧ ∀ v, Nm D u i v φ = 0 := by
  unfold MramI
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem U_D_of_D_U_on_finite_dim {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (U Dm : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0) (hU : ∀ x ∈ W, U x ∈ W)
    (hDU : ∀ x ∈ W, Dm (U x) = c • x) : ∀ x ∈ W, U (Dm x) = c • x := by
  intro x hx
  have hinj : Function.Injective (U.restrict hU) := by
    intro a b hab
    have h1 : U a = U b := congrArg Subtype.val hab
    have h2 : c • (a : V) = c • (b : V) := by rw [← hDU a a.2, ← hDU b b.2, h1]
    exact Subtype.ext (smul_right_injective V hc h2)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨x, hx⟩
  have hy' : U y = x := congrArg Subtype.val hy
  rw [← hy', hDU y y.2, map_smul]

theorem forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ ((D.fm u).Fi i) := by
  have h := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun a => (D.fm u).emb i (((D.fm u).lat i).b a)))
  rwa [((D.fm u).emb_basis i).2] at h

theorem ramified_forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ (MramI D u i) := by
  have := forms_finite_dimensional D u i
  exact Submodule.finiteDimensional_of_le (inf_le_left : MramI D u i ≤ (D.fm u).Fi i)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem diamond_conj_mem_level (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) : δ.1⁻¹ * κ.1 * δ.1 ∈ S.U := _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.diamond_conj_mem_level (k := k) (δ := δ) S v hv h κ

theorem level_character_conj_diamond (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) :
    S.chi ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ = S.chi κ := by
  have h1 := h.1
  have key : S.chi (κ⁻¹ * ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp [Subgroup.coe_mul, map_mul, map_inv, h1 v'' hne]
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  exact key.symm

theorem adelic_function_right_translate_diamond {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ}
    {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ)
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb) :
    (fun x => g (x * δ)) ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have e : (x' * δ).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (x * δ).1 *
      (⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ : S.U).1 := by
    simp only [Subgroup.coe_mul, hx]
    group
  have := hg γ hγ (x * δ) (x' * δ) ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ e y y' hy
  rw [level_character_conj_diamond S v hv hb h κ] at this
  exact this

end Gen

variable {D : D7} {u : D.what₂.Word}

def DiamondElementsExist (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
    ∃ δ, IsDia (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ

theorem level_prime_ne_type_prime (A : AtTTied u) (j : Fin 2) : (D.mem u).A.T ≠ D.host.g j := _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.level_prime_ne_type_prime A j

theorem level_places_not_bad (A : AtTTied u) (v : (D.mem u).A.vT) : (A.eV v).1 ∉ badG D := _root_.Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.level_places_not_bad A v

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable (D : D7) (u : D.what₂.Word)

theorem emb_tpow_smul (i n : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i (((D.mem u).A.T : D.what₂.LL) ^ n • x) = tpow D u n • (D.fm u).emb i x := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]
  rfl

theorem eval_subP {ι : Type} [Fintype ι] {n : ℕ} (N Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (N x.1 * Z x.1) x.2.1 x.2.2) P =
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => Z x.1 x.2.1 x.2.2) (Formalism.L2.Forms.subP N P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.L2.Forms.subP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, MvPolynomial.eval_X, hp]
    simp [Formalism.L2.Forms.subP, Matrix.mul_apply, MvPolynomial.eval_sum]

theorem fnOf_mul {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (N M : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.fnOf G s (fun τ => N τ * M τ) P =
      Formalism.L2.Forms.fnOf G s M (MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N P) := by
  funext y
  simp only [Formalism.L2.Forms.fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C]
  have h := eval_subP N (fun τ => M τ * y.1 τ) P
  simp only [← Matrix.mul_assoc] at h
  rw [h]
  simp only [Matrix.mul_assoc (N _), Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
