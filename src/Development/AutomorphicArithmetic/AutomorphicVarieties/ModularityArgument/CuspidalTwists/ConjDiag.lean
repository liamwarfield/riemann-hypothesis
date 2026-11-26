module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjDiag
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourResidualFlag

section Alg

variable {R : Type} [CommRing R]

def mat (P b e : R) : M4 R := !![P, 0, 0, 0; 0, P * e, 0, 0; 0, -(b * e), e, 0; b, 0, 0, 1]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem flg_map {R' : Type} [CommRing R'] (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  rw [flg_eq, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem flg_10 (x s : R) : flg x s 1 0 = s := by
  rw [flg_eq]
  simp

theorem conj_diag (x s dl P b e : R) (i : Fin 4) :
    (adj (flg x s) * (dl • mat P b e) * flg x s) i i = (dl • mat P b e) i i := by
  rw [flg_eq]
  fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]

theorem mat_supp {S : Finset (ℤ × ℤ)} (h1 : wt 2 1 ∈ S) (h2 : wt 3 0 ∈ S) (dl P b e : R) : SuppM S (dl • mat P b e) := by
  intro i j hij hw
  fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij

theorem tn_map {R' : Type} [CommRing R'] (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

theorem tn_eq (g t : M2 R) (hg : g 0 1 = 0) (ht1 : t 0 1 = 0) (ht2 : t 1 0 = 0) (ht0 : t 0 0 = 1)
    (hg1 : g 1 1 = 1) : tn g t = mat (g 0 0) (g 1 0) (t 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]

theorem res_mul {O : Type} [CommRing O] [IsLocalRing O] (u v : Oˣ) {t : ResidueField O}
    (h : residue O ((u * v⁻¹ : Oˣ) : O) = t) : residue O (u : O) = t * residue O (v : O) := by
  have e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O) := by simp
  rw [e, map_mul, h]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem chi_mul {c : Coef l} (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * chi D pr 3 g = chi D pr 1 g * chi D pr 2 g := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]

private theorem inc_mem {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  have hint : (inc h).IsIntegral := by
    intro y
    obtain ⟨p, hp, e⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact e
  haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)
  exact map_nonunit (inc h) x hx

theorem eq_of_res {c c' : Coef l} (h : c.O ≤ c'.O) {R : Type} [CommRing R]
    (f : c'.O →+* R) (hf : ∀ y ∈ maximalIdeal c'.O, f y = 0) {x y : c.O} (e : residue c.O x = residue c.O y) :
    f (inc h x) = f (inc h y) := by
  have h1 : x - y ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, e, sub_self]
  have h2 := hf _ (inc_mem h h1)
  rwa [map_sub, map_sub, sub_eq_zero] at h2

end UpperTheory.V.Cu.RankFourResidualFlag

open UpperTheory.V.Cu.RankFourResidualFlag in
theorem UpperTheory.V.Cu.resOf4 : UpperTheory.V.Cu.ResOf4 := by
  intro Ω _ _ _ l _ d T hT W R _ f hf
  have hpr : T.pr = d.T₀.pr := hT.pr

  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have h01 : ∀ g, f (d.ρ₁ g 0 1) = 0 := fun g => hf _ (d.mod.red g).2.2
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t01 : ∀ g, f (d.τ g 0 1) = 0 := fun g => hf _ (d.tau.red g).2
  have hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0 := fun u => by
    have : IsUnit (f (inc d.h (u : d.c.O))) := (u.isUnit.map (inc d.h)).map f
    exact this.ne_zero

  have sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧
      f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧
      f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 3 (resQ T.F g) : d.c.O)) * e := by
    intro g
    have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
    have hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t →
        residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) =
          t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) := fun t ht => by
      apply res_mul
      simp only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one,
        zpow_zero, mul_one, hres] at ht
      exact ht
    have hprod := congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))
    simp only [Units.val_mul, map_mul] at hprod
    have h0 := hne (chi d.D d.T₀.pr 0 (resQ T.F g))
    by_cases hK : resQ T.F g ∈ d.K'.fixingSubgroup
    · have e1 := hrb 1 (d.quad.on _ (by rwa [hres]))
      rw [one_mul] at e1
      have e2 := eq_of_res d.h f hf e1.symm
      obtain ⟨a1, a2⟩ := d.tau.on _ hK
      refine ⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩
      rw [e2] at hprod
      rw [mul_one]
      exact (mul_left_cancel₀ h0 hprod).symm
    · have e1 := hrb (-1) (d.quad.off _ (by rwa [hres]))
      have e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) =
          residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) := by
        rw [map_neg, e1]
        ring
      have e2 := eq_of_res d.h f hf e1'
      rw [map_neg, map_neg] at e2
      obtain ⟨a1, a2⟩ := d.tau.off _ hK
      refine ⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩
      rw [e2] at hprod
      have := mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) *
        (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))
      rw [this]
      ring

  have hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) •
      tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f) := fun g => by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧
      (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧
      (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 g : d.c.O) = dl := by
    intro g
    obtain ⟨e, -, he, he10, e1, e2⟩ := sgnK g
    have hrg := hr g
    have hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) =
        f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O)) := fun i => by
      rw [← hpr]
      rfl
    generalize resQ T.F g = g' at he he10 e1 e2 hrg hχ
    have r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) =
        f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)) := by
      rw [← map_mul, ← map_mul]
      apply eq_of_res d.h f hf
      rw [map_mul]
      exact d.tw.red0 g'
    have r3 := eq_of_res d.h f hf (d.tw.red3 g')
    refine ⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _)
        (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]
      simp only [Matrix.map_apply]
      rw [h00, he]
    · rw [hχ 0]
      exact r0
    · rw [hχ 1, e1, r0]
      ring
    · rw [hχ 2, e2, r3]
    · rw [hχ 3]
      exact r3
  have hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v))) := fun v => flg_map f _ _
  have hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r := fun S h1 h2 g => by
    obtain ⟨e, P, b, dl, h, -⟩ := key g
    rw [h]
    exact mat_supp h1 h2 dl P b e
  have hsM : Supp nM ((d.Q T).map f).r := hs nM (by decide) (by decide)
  refine ⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key g
    rw [h]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key s
    show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _
    rw [hn v, h, conj_diag]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · rw [hn, flg_10]
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp
  · rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FlagConjSmulTensorSymmetricEq
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.SymplecticFlagConjugation

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, low, nA, Matrix.mul_apply, Fin.sum_univ_four]

theorem adj_flg (x s : R) : adj (flg x s) = !![1, 0, 0, 0; -s, 1, 0, 0; 0, x, 1, 0; -x, x * s, s, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem isGSp_flg (x s : R) : IsGSp 1 (flg x s) := by
  unfold IsGSp
  rw [adj_flg, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gsp_tn (d : R) (g t : Matrix (Fin 2) (Fin 2) R) (h00 : t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1)
    (h01 : t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0) (h11 : t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1) :
    IsGSp (d ^ 2 * g.det) (d • tn g t) := by
  unfold IsGSp
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h00
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h11

theorem flag_conj_smul_tensor_symmetric_eq (x s d a b p q r : R) (hs : s * s = 1) :
    adj (flg x s) * (d • tn !![p, q; (p + q * x) * x - r * x, r] !![a, b; b, a]) * flg x s =
      d • !![(a + b * s) * (p + q * x), b * (p + q * x), -(q * (a * s + b)), a * q;
        0, (a - b * s) * (p + q * x), 0, -(q * (a * s - b));
        0, 0, (a + b * s) * (r - x * q), -(b * (r - x * q));
        0, 0, 0, (a - b * s) * (r - x * q)] := by
  rw [Matrix.mul_smul, Matrix.smul_mul, adj_flg, flg_eq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (-(b * (p + q * x))) * hs
    | linear_combination (-(b * (q * x - r))) * hs
    | linear_combination (b * (p + q * x)) * hs
    | linear_combination (b * (q * x - r)) * hs
    | linear_combination (q * a) * hs

theorem conj_flg (x s d : R) (g t : Matrix (Fin 2) (Fin 2) R) (hs : s * s = 1)
    (hf : g 1 0 + g 1 1 * x = (g 0 0 + g 0 1 * x) * x) (ht : t 1 1 = t 0 0 ∧ t 1 0 = t 0 1) :
    adj (flg x s) * (d • tn g t) * flg x s =
      d • !![(t 0 0 + t 0 1 * s) * (g 0 0 + g 0 1 * x), t 0 1 * (g 0 0 + g 0 1 * x), -(g 0 1 * (t 0 0 * s + t 0 1)), t 0 0 * g 0 1;
        0, (t 0 0 - t 0 1 * s) * (g 0 0 + g 0 1 * x), 0, -(g 0 1 * (t 0 0 * s - t 0 1));
        0, 0, (t 0 0 + t 0 1 * s) * (g 1 1 - x * g 0 1), -(t 0 1 * (g 1 1 - x * g 0 1));
        0, 0, 0, (t 0 0 - t 0 1 * s) * (g 1 1 - x * g 0 1)] := by
  have e1 : g = !![g 0 0, g 0 1; (g 0 0 + g 0 1 * x) * x - g 1 1 * x, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination hf
  have e2 : t = !![t 0 0, t 0 1; t 0 1, t 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]
  conv_lhs => rw [e1, e2]
  exact flag_conj_smul_tensor_symmetric_eq x s d (t 0 0) (t 0 1) (g 0 0) (g 0 1) (g 1 1) hs

theorem form_eqs (t : Matrix (Fin 2) (Fin 2) R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) :
    t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1 ∧ t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0 ∧ t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩

theorem symplecticAdjoint_map_ringHom {R' : Type} [CommRing R'] (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply]

theorem conj_map {R' : Type} [CommRing R'] (f : R →+* R') (N M : M4 R) :
    adj (N.map f) * M.map f * N.map f = (adj N * M * N).map f := by
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul]

theorem gsp_map {R' : Type} [CommRing R'] (f : R →+* R') {ν : R} {M : M4 R} (h : IsGSp ν M) : IsGSp (f ν) (M.map f) := by
  unfold IsGSp at *
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem pow_diag {g : M2 R} (h : g 0 1 = 0 ∧ g 1 0 = 0) (n : ℕ) :
    (g ^ n) 0 1 = 0 ∧ (g ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, ih.1, ih.2]

theorem res_inv {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (h : residue O (u : O) = 1) :
    residue O ((u⁻¹ : Oˣ) : O) = 1 := by
  have e := congrArg (residue O) (Units.inv_mul u)
  rwa [map_mul, h, mul_one, map_one] at e

end Alg

end UpperTheory.V.Cu.SymplecticFlagConjugation

open UpperTheory.V.Cu.SymplecticFlagConjugation in
theorem UpperTheory.V.Cu.pairOf4 : UpperTheory.V.Cu.PairOf4 := by
  intro Ω _ _ _ l _ d T hT hok W R _ f hdet hθ
  have hr : ∀ g, ((d.Q T).map f).r g =
      ((inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn (d.ρ₁ (resQ T.F g)) (d.τ (resQ T.F g))).map f := fun g => rfl
  have hn : ∀ v, ((d.Q T).map f).n v = (flg (d.x (T.pl v)) (d.s (T.pl v))).map f := fun v => rfl
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g x => g.commutes x
  have hcyc : ∀ g : G T.F Ω, cycZ ℚ Ω l (resQ T.F g) = cycZ T.F Ω l g := fun g => rfl
  have hD : ∀ A, ∀ g ∈ Dec (F := T.F) A, resQ T.F g ∈ Dec (F := ℚ) A := fun A g h => mem_Dec.2 (mem_Dec.1 h)
  have hI : ∀ A, ∀ g ∈ Ine (F := T.F) A, resQ T.F g ∈ Ine (F := ℚ) A := fun A g h => mem_Ine.2 (mem_Ine.1 h)
  have hsgn : ∀ A, d.s A * d.s A = 1 := fun A => by
    rcases d.tau.sgn A with h | h <;> rw [h] <;> ring
  refine ⟨fun g => ?_, ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
  · obtain ⟨h00, h01, h11⟩ := form_eqs _ (d.tau.form (resQ T.F g))
    have h1 := gsp_map f (gsp_tn (inc d.h (d.δ (resQ T.F g) : d.c.O)) (d.ρ₁ (resQ T.F g)) _ h00 h01 h11)
    have key : inc d.h (d.δ (resQ T.F g) : d.c.O) ^ 2 * inc d.h (Phi d.D d.T₀.pr d.k (resQ T.F g) : d.c.O) =
        inc d.h (d.D.th (resQ T.F g) : d.c.O) := by
      rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, d.tw.mul]
    rw [map_mul, hdet _ (hF g), ← map_mul, key] at h1
    exact h1
  · rintro g ⟨A, hA, hg, h1⟩
    have hl := hA l (Finset.mem_insert_self _ _)
    have hI' := hI A g hg
    have h2 := d.tw.kill _ ((places ℚ Ω l A).2.2.2 hl hI') h1
    have hK : resQ T.F g ∈ d.K'.fixingSubgroup := by
      by_contra hn'
      have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
      have hoff := d.quad.off (resLe hT.le g) (by rwa [hres])
      have hb : ∀ j, residue d.c.O (d.D.ps j (resQ T.F g) : d.c.O) = 1 := fun j => by
        have e := congrFun (congrFun h1 j) j
        simpa [Raw.rbar, Raw.r0, diagRep] using e
      have hon : d.T₀.rb wAl (resLe hT.le g) = 1 := by
        show residue d.c.O (((chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
          (chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : d.c.Oˣ) : d.c.O) = 1
        have hb' : ∀ i, residue d.c.O (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O) = 1 := fun i => hb (lab d.T₀.pr i)
        rw [zpow_one, zpow_zero, mul_one, Units.val_mul, map_mul, hb', res_inv _ (hb' 1), mul_one]
      have := (UpperTheory.V.Ws.P1.coefRes d.c).2.1
      exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField d.c.O) l]; exact d.ctx.1.l_odd)
        (hoff.symm.trans hon)
    have h3 := d.tau.unr A hl _ hI' hK
    have h4 := d.mod.away A hl _ hI' h2.2 (hθ A hA g hg)
    refine (hr g).trans ?_
    rw [h2.1, h3, h4, tn_one]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · obtain ⟨j, hj⟩ := hT.g0
    have hρ := pow_diag d.mod.nrm (l ^ j)
    have hτ := pow_diag (g := d.τ (resQ d.T₀.F d.T₀.g0)) (by rw [d.tau.nrm]; simp) (l ^ j)
    rw [← map_pow, ← hj] at hρ hτ
    intro a b hab
    refine (congrFun (congrFun (hr T.g0) a) b).trans ?_
    generalize resQ T.F T.g0 = g1 at hρ hτ ⊢
    fin_cases a <;> fin_cases b <;> simp [tn, hρ.1, hρ.2, hτ.1, hτ.2] at hab ⊢
  · change IsLow ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa using gsp_map f (isGSp_flg (d.x (T.pl v)) (d.s (T.pl v)))
    · rw [flg_eq]
      fin_cases i <;> simp
    · rw [flg_eq]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · have hsD := hD _ s hs
    change IsUp (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    rw [conj_map, conj_flg _ _ _ _ _ (hsgn _) (d.mod.flag _ (T.ovl v) _ hsD)
      (d.tau.on _ (d.quad.split _ (T.ovl v) hsD))]
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · obtain ⟨hi, hc⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l d.ctx.1.l_odd _ (T.ovl v) s hs
    have hc' := (hcyc s).trans hc
    have hsD : resQ T.F s ∈ Dec (F := ℚ) (T.pl v) := hD _ s hs.1
    have hsI := hI _ s hi
    have hK := d.quad.split _ (T.ovl v) hsD
    have hδ := (d.tw.kill _ hc' (hok.ineL _ (T.ovl v) s hi)).1
    have hm := d.mod.ine _ (T.ovl v) _ hsI
    have h3 : chiO ℚ Ω l d.c₁.O (resQ T.F s) = 1 := by
      show Units.map _ (cycZ ℚ Ω l _) = 1
      rw [hc', map_one]
    have ht := d.tau.ine _ (T.ovl v) _ hsI
    rw [h3, one_pow, Units.val_one] at ht hm
    obtain ⟨h00, -, -⟩ := form_eqs _ (d.tau.form (resQ T.F s))
    have hon := d.tau.on _ hK
    have hss := hsgn (T.pl v)
    have h4 : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) = 1 := by
      linear_combination (-(d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v))) * ht + h00 +
        (d.τ (resQ T.F s) 1 0 + d.τ (resQ T.F s) 0 1) * hon.2 + (-(d.τ (resQ T.F s) 0 1 ^ 2)) * hss
    change (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f) i i = 1
    rw [conj_map, conj_flg _ _ _ _ _ hss (d.mod.flag _ (T.ovl v) _ hsD) hon, hm.1, hm.2, ht, h4, hδ]
    fin_cases i <;> simp

end
end
