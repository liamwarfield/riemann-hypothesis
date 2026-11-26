module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpolyHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOf
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHExpInj
set_option autoImplicit false

namespace UpperTheory.Gal.LocalSmoothExtension

theorem hExpInj_of : HExpInj := by
  intro F _ _ n t₀ ε lam h hanti hh i k hik
  rcases hh with ⟨m, -, hh⟩ | ⟨m, -, hh⟩
  · rw [hh i, hh k] at hik
    have hi := i.isLt
    have hk := k.isLt
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti t₀ hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti t₀ hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega
  · rw [hh i, hh k] at hik
    have si : ∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) i =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have sk : ∑ j ∈ Finset.univ.erase k, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) k =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega

end UpperTheory.Gal.LocalSmoothExtension
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWConj
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private lemma roots_map_sigma (σ : ℂ ≃+* ℂ) (p : ℂ[X]) :
    (p.map (σ : ℂ →+* ℂ)).roots = p.roots.map (σ : ℂ →+* ℂ) :=
  (IsAlgClosed.splits p).roots_map _

private lemma sigma_sch (σ : ℂ ≃+* ℂ) {n : ℕ} (μ : Fin n → ℕ) (x : Fin n → ℂ) :
    σ (UpperTheory.Gal.Schur.sch μ x) = UpperTheory.Gal.Schur.sch μ (fun i => σ (x i)) := by
  unfold UpperTheory.Gal.Schur.sch
  exact MvPolynomial.comp_aeval_apply (φ := (σ : ℂ →+* ℂ).toRatAlgHom) x _

theorem UpperTheory.Gal.LocalSmoothExtension.schWConj_of :
    SchWEq → SchWConj := by
  intro hE σ F _ _ n lam χ
  classical
  by_cases h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g
  · obtain ⟨g, hg⟩ := h
    have hg' : Lists χ (fun τ i => σ (g ((σ.symm : ℂ →+* ℂ).comp τ) i)) := by
      intro τ
      have h1 : χ.map τ = (χ.map ((σ.symm : ℂ →+* ℂ).comp τ)).map (σ : ℂ →+* ℂ) := by
        rw [Polynomial.map_map]
        congr 1
        ext x
        simp
      have h2 := hg ((σ.symm : ℂ →+* ℂ).comp τ)
      unfold UpperTheory.Gal.W2.rts at h2 ⊢
      rw [h1, roots_map_sigma, h2, Multiset.map_map]
      rfl
    rw [hE F n (conjWt σ lam) χ _ hg', hE F n lam χ g hg, map_prod]
    let e : (F →+* ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun τ => (σ.symm : ℂ →+* ℂ).comp τ
        invFun := fun τ => (σ : ℂ →+* ℂ).comp τ
        left_inv := fun τ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    refine Fintype.prod_equiv e _ _ fun τ => ?_
    rw [sigma_sch]
    rfl
  · have h0 : schW lam χ = 0 := by
      unfold schW
      exact dif_neg h
    have h1 : schW (conjWt σ lam) χ = 0 := by
      unfold schW
      exact dif_neg h
    rw [h0, h1, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDPairPol
open UpperTheory.Gal.LocalSmoothExtension

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sim_herm {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β u : G.Cˣ) (s : ℚ)
    (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) :
    (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
      (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
  set a : G.C := algebraMap ℚ G.C s with ha
  have hcomm : ∀ x : G.C, a * x = x * a := fun x => Algebra.commutes s x
  have hsh : sh G (u : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) := by
    rw [← hy]
    simp [mul_assoc]
  have key : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C) = a * ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [hsh]
    calc ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C)
        = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * (u : G.C)) := by
          simp [mul_assoc]
      _ = ((β⁻¹ : G.Cˣ) : G.C) * (((u⁻¹ : G.Cˣ) : G.C) * (u : G.C)) * a := by
          rw [hcomm]; simp only [mul_assoc]
      _ = a * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [hcomm]; simp
  have hpa : G.psi v a = (s : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [ha, IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hΓ : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v))
  have hUΓ : (G.psi v (u : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (u : G.C)) := by
    rw [show sh G (u : G.C) = MulOpposite.unop (G.star (u : G.C)) from rfl, G.psi_star]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hΓ, Matrix.one_mul]
  calc (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C))) := by
        rw [map_mul, map_mul, ← Matrix.mul_assoc, hUΓ]
        simp only [Matrix.mul_assoc]
    _ = (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [key, map_mul, hpa, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

private theorem coeff_zero_ne {F A : Type} [Field F] [Ring A] [Algebra F A] [Algebra.IsIntegral F A] [Nontrivial A]
    (g : Aˣ) : (minpoly F (g : A)).coeff 0 ≠ 0 := by
  intro h
  have hint : IsIntegral F (g : A) := Algebra.IsIntegral.isIntegral _
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h
  have hmon : (minpoly F (g : A)).Monic := minpoly.monic hint
  have hqmon : q.Monic := by
    rw [hq] at hmon
    exact Polynomial.monic_X.of_mul_monic_left hmon
  have haeval : Polynomial.aeval (g : A) q = 0 := by
    have h0 := minpoly.aeval F (g : A)
    rw [hq, map_mul, Polynomial.aeval_X] at h0
    have := congrArg (fun y => ((g⁻¹ : Aˣ) : A) * y) h0
    simpa [← mul_assoc] using this
  have hle := minpoly.min F (g : A) hqmon haeval
  rw [hq, Polynomial.degree_mul, Polynomial.degree_X] at hle
  have hq0 : q ≠ 0 := hqmon.ne_zero
  rw [Polynomial.degree_eq_natDegree hq0] at hle
  norm_cast at hle
  omega

theorem dPairPol_of :
    DPairPol := by
  intro p _ G P v
  refine ⟨coeff_zero_ne (F := G.F) (A := G.C) P.γ, (P.c : ℚ), ?_⟩
  intro z hz
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hev : eval₂ v.embedding z (minpoly G.F (P.γ : G.C)) = 0 :=
    (Polynomial.mem_roots_map (minpoly.ne_zero hint)).mp hz
  obtain ⟨x, hx, hMx⟩ := PolyArch.roots_eig_any p G v (P.γ : G.C) z hev
  have hsim := sim_herm G v P.β P.γ (P.c : ℚ) P.sim
  have hform := GlobalTheory.EigenvalueNormSignature.form_mulVec (G.psi v (P.γ : G.C))
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x
  rw [hsim, hMx] at hform
  have hQ : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := P.posR v x hx
    rw [h0] at h1 h2
    simp at h1 h2
    exact h1 h2
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hform
  apply mul_right_cancel₀ hQ
  rw [Complex.star_def] at hform
  push_cast at hform ⊢
  linear_combination hform

end UpperTheory.Gal.LocalSmoothExtension
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLefSum
set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PRootW
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDSumCongr
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.dSumCongr_of :
    DSumCongr := by
  classical
  intro p _ G wt wt' s hw K f r K' φ
  unfold GlobalTheory.LKDef.dSumIrr
  rw [mul_comm _ s, ← smul_eq_mul s, smul_finsum]
  refine finsum_congr (fun q => ?_)
  split_ifs
  · rw [smul_eq_mul, hw]
    ring
  · simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PConjRep
set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension

private def Tw (_σ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance twAdd (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : AddCommGroup (Tw σ V) :=
  inferInstanceAs (AddCommGroup V)

private instance twMod (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw σ V) :=
  Module.compHom V (σ.symm : ℂ →+* ℂ)

private def toTw (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Tw σ V := AddEquiv.refl V

private theorem tw_smul (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : V) :
    toTw σ V (c • x) = σ c • toTw σ V x := by
  change c • x = ((σ.symm : ℂ →+* ℂ) (σ c)) • x
  simp

private theorem tw_smul' (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : Tw σ V) :
    c • x = toTw σ V (σ.symm c • (toTw σ V).symm x) := rfl

private theorem tw_finite (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (Tw σ V) := by
  let b := Module.finBasis ℂ V
  have hsm : ∀ (c : ℂ) (y : Tw σ V), (toTw σ V).symm (c • y) = σ.symm c • (toTw σ V).symm y :=
    fun c y => rfl
  let b' : Module.Basis (Fin (Module.finrank ℂ V)) ℂ (Tw σ V) := Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))
      invFun := fun f => toTw σ V (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        simp [hsm]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))) =
              b.repr ((toTw σ V).symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }
  exact Module.Finite.of_basis b'

private def twMap (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V) :
    Tw σ V →ₗ[ℂ] Tw σ V where
  toFun x := toTw σ V (T ((toTw σ V).symm x))
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.id_apply, tw_smul', tw_smul']
    simp

theorem conjRep_of : ConjRep := by
  intro σ Γ V _ _ _ _ ξ
  let ξ' : Representation ℂ Γ (Tw σ V) :=
    { toFun := fun g => twMap σ V (ξ g)
      map_one' := by
        ext x
        simp [twMap]
      map_mul' := fun g h => by
        ext x
        simp [twMap, Module.End.mul_apply] }
  exact ⟨Tw σ V, twAdd σ V, twMod σ V, tw_finite σ V, ξ', toTw σ V, tw_smul σ V, fun g x => rfl⟩

end UpperTheory.Gal.LocalSmoothExtension
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCoeffOcc
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem coeffOcc_of : CoeffOcc := by
  intro d n t c h hinj hc hEq i
  set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef
  set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro y
    simp only [hPdef, hQdef, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.mul_sum, ← hEq y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [neg_pow]
    ring
  have hQ : Q.coeff (h i) = c := by
    simp only [hQdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun e => hji (hinj e).symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0 := by
    simp only [hPdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  intro ht
  rw [hPQ, hQ] at hP
  split_ifs at hP with hlt
  · rw [ht, mul_zero] at hP
    exact hc hP
  · exact hc hP

end UpperTheory.Gal.LocalSmoothExtension
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.LKDef

section Transport

variable {Γ H V V' : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

private theorem symm_semi {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e) :
    IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [hs]
  simp

private theorem symm_int {ξ : Representation ℂ Γ V} {ξ' : Representation ℂ Γ V'} {e : V ≃+ V'}
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : ∀ g x, e.symm (ξ' g x) = ξ g (e.symm x) := by
  intro g x
  apply e.injective
  rw [hi]
  simp

private theorem forms_left {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (γ : Γ) (g : H) : φ.1 (ι γ * g) = ξ γ (φ.1 g) := φ.2.1 γ g

private theorem forms_right {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (k : H) (hk : k ∈ K) (g : H) : φ.1 (g * k) = φ.1 g := φ.2.2 k hk g

private def fmap (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x))
    (φ : HeckeTraceForms.forms ι K ξ) : HeckeTraceForms.forms ι K ξ' :=
  ⟨fun g => e (φ.1 g), fun γ g => by
      show e (φ.1 (ι γ * g)) = ξ' γ (e (φ.1 g))
      rw [forms_left φ, hi],
    fun k hk g => by
      show e (φ.1 (g * k)) = e (φ.1 g)
      rw [forms_right φ k hk]⟩

private def fequiv (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) :
    HeckeTraceForms.forms ι K ξ ≃+ HeckeTraceForms.forms ι K ξ' where
  toFun := fmap ι K e hi
  invFun := fmap ι K e.symm (symm_int hi)
  left_inv φ := by
    apply Subtype.ext; funext g
    exact e.symm_apply_apply _
  right_inv φ := by
    apply Subtype.ext; funext g
    exact e.apply_symm_apply _
  map_add' a b := by
    apply Subtype.ext; funext g
    exact map_add e _ _

private theorem fequiv_semi (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : IsSemi σ (fequiv ι K e hi) := by
  intro c φ
  apply Subtype.ext; funext g
  exact hs c (φ.1 g)

private theorem transport {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) {F : H → ℂ}
    {T : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (hT : HeckeTraceForms.IsHecke ι K ξ F T) :
    ∃ T' : HeckeTraceForms.forms ι K ξ' →ₗ[ℂ] HeckeTraceForms.forms ι K ξ',
      HeckeTraceForms.IsHecke ι K ξ' (fun h => σ (F h)) T' ∧
        ∀ x, fequiv ι K e hi (T x) = T' (fequiv ι K e hi x) := by
  have hsym := symm_semi (fequiv_semi ι K hs hi)
  refine ⟨{ toFun := fun ψ => fequiv ι K e hi (T ((fequiv ι K e hi).symm ψ))
            map_add' := fun a b => by simp
            map_smul' := fun c ψ => by
              rw [hsym c ψ, map_smul, fequiv_semi ι K hs hi]
              simp }, ?_, ?_⟩
  · intro ψ g
    change e ((T ((fequiv ι K e hi).symm ψ)).1 g) = _
    rw [hT, AddEquiv.map_finsum]
    refine finsum_congr fun q => ?_
    rw [hs]
    congr 1
    exact e.apply_symm_apply _
  · intro x
    change fequiv ι K e hi (T x) = fequiv ι K e hi (T ((fequiv ι K e hi).symm (fequiv ι K e hi x)))
    rw [AddEquiv.symm_apply_apply]

private theorem hecke_unique {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {F : H → ℂ}
    {T T' : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (h : HeckeTraceForms.IsHecke ι K ξ F T)
    (h' : HeckeTraceForms.IsHecke ι K ξ F T') : T = T' := by
  apply LinearMap.ext; intro φ
  apply Subtype.ext; funext g
  rw [h φ g, h' φ g]

end Transport

theorem heckeTraceSemi_of :
    TraceSemi → HeckeTraceSemi := by
  intro hTr σ Γ H V V' _ _ _ _ _ _ ξ ξ' e hs hi ι K F
  by_cases h : ∃ T, HeckeTraceForms.IsHecke ι K ξ F T
  · obtain ⟨T', hT', hint⟩ := transport (ι := ι) (K := K) hs hi h.choose_spec
    have h' : ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := ⟨T', hT'⟩
    have hc : h'.choose = T' := hecke_unique h'.choose_spec hT'
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_left h, dite_eq_left h', hc]
    exact hTr σ _ _ (fequiv ι K e hi) (fequiv_semi ι K hs hi) _ _ hint
  · have h' : ¬ ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := by
      rintro ⟨T', hT'⟩
      obtain ⟨T, hT, -⟩ := transport (ι := ι) (K := K) (symm_semi hs) (symm_int hi) hT'
      refine h ⟨T, ?_⟩
      simpa only [RingEquiv.symm_apply_apply] using hT
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_right h, dite_eq_right h', map_zero]

end UpperTheory.Gal.LocalSmoothExtension
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PListsEx
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.listsEx_of :
    ListsEx := by
  intro F _ _ n χ hχ
  classical
  refine ⟨fun τ i => ((Polynomial.map τ χ).roots.toList).getD i 0, ?_⟩
  intro τ
  have hc : ((Polynomial.map τ χ).roots.toList).length = n := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map, hχ]
  have hl : List.ofFn (fun i : Fin n => ((Polynomial.map τ χ).roots.toList).getD i 0)
      = (Polynomial.map τ χ).roots.toList := by
    apply List.ext_getElem
    · simp [hc]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  show (Polynomial.map τ χ).roots = _
  rw [Fin.univ_val_map, hl, Multiset.coe_toList]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvPolProps
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSpecConj
set_option autoImplicit false

open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)
open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

private theorem map_oneP {p : ℕ} [Fact p.Prime] (σ : ℂ ≃+* ℂ) (G : HTGroup p) (x : Gr G 1) :
    σ (oneP G x) = oneP G x := by
  by_cases h : x ∈ (Kp G : Set (Gr G 1))
  · simp [oneP, Set.indicator_of_mem h]
  · simp [oneP, Set.indicator_of_notMem h]

private theorem dTrace_conj {p : ℕ} [Fact p.Prime] (hH : HeckeTraceSemi) (σ : ℂ ≃+* ℂ) (G : HTGroup p)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ξ : Representation ℂ (G.Cˣ × ℚˣ) V) (ξ' : Representation ℂ (G.Cˣ × ℚˣ) V') (e : V ≃+ V') (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) (K : Subgroup G.GAf) (f : G.GAf → ℂ) :
    dTrace G ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (dTrace G ξ K f (Kp G) (oneP G)) := by
  have hterm : ∀ B : DForm G, B.trace ξ' K (fun g => σ (f g)) (Kp G) (oneP G) = σ (B.trace ξ K f (Kp G) (oneP G)) := by
    intro B
    have h := hH σ (grp G B.β) (G.GAf × Gr G 1) V V' (ξ.comp (grp G B.β).subtype) (ξ'.comp (grp G B.β).subtype) e hs
      (fun g x => hi g.1 x) B.emb (K.prod (Kp G)) (fun h => f h.1 * oneP G h.2)
    have hF : (fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2)) = fun h => σ (f h.1) * oneP G h.2 := by
      funext h
      rw [map_mul, map_oneP]
    rw [hF] at h
    exact h
  unfold dTrace
  have hm := σ.toAddEquiv.map_finsum (fun q : DFCls G => (Quot.out q).trace ξ K f (Kp G) (oneP G))
  calc _ = ∑ᶠ q : DFCls G, σ ((Quot.out q).trace ξ K f (Kp G) (oneP G)) := finsum_congr fun q => hterm _
    _ = _ := hm.symm

theorem UpperTheory.Gal.LocalSmoothExtension.specConj_of :
    TraceSemi → ConjRep → HeckeTraceSemi → GoodConj → SchWConj → PolyFnConj → SpecConj := by
  intro hT hCR hH hG hSW hP σ p _ D G L lam K J ψ θ f hS
  obtain ⟨hcomm, V, i1, i2, i3, ξ, hwt, hsp⟩ := hS
  obtain ⟨V', j1, j2, j3, ξ', e, hse, hint⟩ := hCR σ (G.Cˣ × ℚˣ) V ξ
  have hPf := hP σ G.GAf J K ψ f
  refine ⟨fun j j' w => ?_, V', j1, j2, j3, ξ', ?_, ?_⟩
  · rw [hPf.1, hPf.1, hcomm]
  · intro B y h1 h2
    rw [hSW, ← hwt B y h1 h2]
    exact hT σ V V' e hse (ξ y.1) (ξ' y.1) (fun x => hint y.1 x)
  · intro s' hs'
    obtain ⟨s, rfl⟩ : ∃ s : List J →₀ ℂ, wmap σ.toRingHom s = s' := by
      refine ⟨wmap σ.symm.toRingHom s', ?_⟩
      ext w
      simp [wmap]
    have hw : σ (wop θ s) = wop (fun j => σ (θ j)) (wmap σ.toRingHom s) :=
      UpperTheory.Gal.CertificateRingHomMap.map_wop_wmap σ.toRingHom σ.toRingHom (fun _ => rfl) θ s
    have hne : wop θ s ≠ 0 := by
      intro h0
      apply hs'
      rw [← hw, h0, map_zero]
    obtain ⟨a, hgood, htr⟩ := hsp s hne
    refine ⟨wmap σ.toRingHom a, ?_⟩
    have hc : polyFn K (fun j g => σ (ψ j g)) (wmul (wmap σ.toRingHom a) (wmap σ.toRingHom s)) (fun g => σ (f g)) =
        fun g => σ (polyFn K ψ (wmul a s) f g) := by
      rw [← hPf.2.2, hPf.2.1]
    rw [hc]
    refine ⟨hG σ p G K _ hgood, ?_⟩
    rw [dTrace_conj hH σ G ξ ξ' e hse hint]
    exact fun h0 => htr ((map_eq_zero σ).1 h0)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTestOne
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.testOne_of :
    TestOne := by
  intro p _ G
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.LKMid.isTest_indicator _ _ (by
      rintro _ ⟨k, hk, rfl⟩
      rw [GlobalTheory.LKCx.sigG_one]
      exact hk)
  · exact GlobalTheory.LKDef.HeckeTraceExample.indicator_bi _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PInvRoots
open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private theorem rev_lin (r : ℂ) (hr : r ≠ 0) :
    (X - C r : ℂ[X]).reverse = C (-r) * (X - C r⁻¹) := by
  have h1 : (C (-r) * (X - C r⁻¹) : ℂ[X]) = 1 - C r * X := by
    rw [mul_sub, ← C_mul]
    simp [hr]
    ring
  rw [h1]
  ext n
  rw [coeff_reverse, natDegree_X_sub_C]
  rcases n with _ | _ | n
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C]
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one, coeff_C]

open Polynomial in
private theorem rev_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse.roots = s.map (fun z => z⁻¹) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, ← C_1, reverse_C, roots_C, Multiset.map_zero]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have hm : ((s.map (fun a => X - C a)).prod : ℂ[X]) ≠ 0 :=
      (monic_multiset_prod_of_monic s _ fun a _ => monic_X_sub_C a).ne_zero
    have hm' : ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse ≠ 0 := by
      simpa [reverse_eq_zero] using hm
    have hl : (C (-a) * (X - C a⁻¹) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha)) (X_sub_C_ne_zero _)
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, rev_lin a ha,
      roots_mul (mul_ne_zero hl hm'), roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C, ih',
      Multiset.map_cons, Multiset.singleton_add]

open Polynomial in
private theorem rev_roots (Q : ℂ[X]) (h0 : Q.coeff 0 ≠ 0) :
    Q.reverse.roots = Q.roots.map (fun z => z⁻¹) := by
  have hQ : Q ≠ 0 := fun h => h0 (by simp [h])
  have hc : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hz : ∀ z ∈ Q.roots, z ≠ 0 := by
    rintro z hz rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact (mem_roots hQ).mp hz)
  have hl : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  conv_lhs => rw [← hf]
  rw [reverse_mul_of_domain, reverse_C, roots_C_mul _ hl, rev_prod _ hz]

open Polynomial in
theorem UpperTheory.Gal.LocalSmoothExtension.invRoots_of :
    InvRoots := by
  intro F _ _ P h0 τ
  have hτ : τ (P.coeff 0) ≠ 0 := by simpa using h0
  have hmap : (P.map τ).coeff 0 ≠ 0 := by simpa [coeff_map] using h0
  have hrev : (P.reverse).map τ = (P.map τ).reverse := by
    rw [reverse, reverse, natDegree_map, reflect_map]
  have hinv : (invPol P).map τ = C (τ (P.coeff 0))⁻¹ * (P.map τ).reverse := by
    rw [invPol, Polynomial.map_mul, map_C, hrev, map_inv₀]
  simp only [UpperTheory.Gal.W2.rts]
  rw [hinv, roots_C_mul _ (inv_ne_zero hτ), rev_roots _ hmap]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxLin
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

private theorem semi_symm {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) : IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [h]
  simp

private theorem exists_basis {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ b' : Module.Basis ι ℂ V', ∀ y i, b'.repr y i = σ (b.repr (e.symm y) i) := by
  refine ⟨Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))
      invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        have hs := semi_symm h c y
        simp [hs]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }, ?_⟩
  intro y i
  rfl

theorem UpperTheory.Gal.LocalSmoothExtension.traceSemi_of :
    TraceSemi := by
  intro σ V V' _ _ _ _ e h T T' hT
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    obtain ⟨b', hb'⟩ := exists_basis h b
    have hbj : ∀ j, b' j = e (b j) := by
      intro j
      apply b'.repr.injective
      rw [b'.repr_self]
      ext k
      rw [hb', AddEquiv.symm_apply_apply, b.repr_self]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [Finsupp.single_apply, hjk]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT,
      AddEquiv.symm_apply_apply]
  · have H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V') := by
      rintro ⟨t, ⟨c⟩⟩
      obtain ⟨c', -⟩ := exists_basis (semi_symm h) c
      exact H ⟨_, ⟨c'.reindexFinsetRange⟩⟩
    simp only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSchWEq
open UpperTheory.Gal.LocalSmoothExtension

private theorem exists_perm_of_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, b (e i) = a i :=
  _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq a b h

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dite_eq_left h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
end

namespace UpperTheory.Gal.LocalSmoothExtension

theorem InvRoots_holds : InvRoots := invRoots_of
theorem InvPolProps_holds : InvPolProps := invPolProps_of InvRoots_holds
theorem RootW_holds : RootW :=
  rootW_of UpperTheory.Gal.W2.RootSumW_holds UpperTheory.Gal.W2.RootSumWOff_holds listsEx_of schWEq_of
theorem EigOf_holds : EigOf := eigOf_of UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds
theorem CxLin_holds : CxLin := cxLin_of cxFlat_of
theorem GroupTop_of (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) : GroupTop :=
  groupTop_of h₁ h₂ RootW_holds InvRoots_holds InvPolProps_holds markRoots_of dPairPol_of dSumCongr_of testOf_of testOne_of
theorem HeckeTraceSemi_holds : HeckeTraceSemi := heckeTraceSemi_of traceSemi_of
theorem SpecConj_holds : SpecConj :=
  specConj_of traceSemi_of conjRep_of HeckeTraceSemi_holds goodConj_of (schWConj_of schWEq_of) polyFnConj_of

end UpperTheory.Gal.LocalSmoothExtension
