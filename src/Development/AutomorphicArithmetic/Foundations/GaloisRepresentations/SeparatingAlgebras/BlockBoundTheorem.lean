module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SymExPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NullZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaEig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Combine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GlobOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CongSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EqOneOfFinInf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TwistPart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevelEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.KerOpen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenomBdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MaxCpt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PairTerm
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem mono_term {n : ℕ} (l : Fin n → ℤ) (w : Fin n → ℂˣ) (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    monomialChar (fun i => -l (Fin.rev i)) (w ∘ Fin.revPerm) =
      (starRingEnd ℂ) (monomialChar l w) := by
  show ∏ i, (((w (Fin.revPerm i)) ^ (-l (Fin.rev i)) : ℂˣ) : ℂ) =
    (starRingEnd ℂ) (∏ i, ((w i ^ l i : ℂˣ) : ℂ))
  rw [map_prod, ← Equiv.prod_comp Fin.revPerm (fun k => (starRingEnd ℂ) ((w k ^ l k : ℂˣ) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  rw [← Complex.inv_eq_conj (hw _), zpow_neg, inv_zpow]

private theorem pair_term {n : ℕ} (t : ℝ) (w : Fin n → ℂˣ) (hinj : Function.Injective w)
    (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    ∏ p ∈ prs n, ((w (Fin.rev p.1) : ℂ) - (t : ℂ) * (w (Fin.rev p.2) : ℂ)) /
        ((w (Fin.rev p.1) : ℂ) - (w (Fin.rev p.2) : ℂ)) =
      (starRingEnd ℂ) (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) /
        ((w p.1 : ℂ) - (w p.2 : ℂ))) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : Fin.rev p.2 ≠ Fin.rev p.1 := fun h => (ne_of_lt hp) (Fin.rev_injective h).symm
    have hab : (w (Fin.rev p.2) : ℂ) ≠ (w (Fin.rev p.1) : ℂ) :=
      fun h => hne (hinj (Units.val_injective h))
    have ha : (w (Fin.rev p.2) : ℂ) ≠ 0 := Units.ne_zero _
    have hb : (w (Fin.rev p.1) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj (hw _), ← Complex.inv_eq_conj (hw _)]
    generalize (w (Fin.rev p.2) : ℂ) = a at *
    generalize (w (Fin.rev p.1) : ℂ) = b at *
    have h1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have h2 : a⁻¹ - b⁻¹ ≠ 0 := by
      rw [inv_sub_inv ha hb]
      exact div_ne_zero h1 (mul_ne_zero ha hb)
    rw [div_eq_div_iff h1 h2]
    field_simp

theorem UpperTheory.Gal.Gen.rConj_pf :
    UpperTheory.Gal.Gen.RFormula → UpperTheory.Gal.Gen.RConj := by
  intro hR n t l z hinj hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hR n t _ z hinj, hR n t l z hinj, map_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ ?_).symm
  intro σ
  have hw : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hz _
  have hi : Function.Injective (z ∘ σ) := hinj.comp σ.injective
  have h1 := mono_term l (z ∘ σ) hw
  have h2 := pair_term t (z ∘ σ) hi hw
  rw [map_mul]
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.InjAEPf
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.injAE_pf :
    UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.InjAE := by
  intro hN n
  have h : ∀ i j : Fin n, ∀ᵐ θ : Fin n → UnitAddCircle, i ≠ j → pt θ i ≠ pt θ j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun θ h => absurd hij h)
    · have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun e => hij (MvPolynomial.X_injective e))
      filter_upwards [hN n _ hp] with θ hθ _ e
      apply hθ
      simp [e]
  have h2 : ∀ᵐ θ : Fin n → UnitAddCircle, ∀ i j : Fin n, i ≠ j → pt θ i ≠ pt θ j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  filter_upwards [h2] with θ hθ i j e
  by_contra hne
  exact hθ i j hne e
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RIntPf
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rInt_pf :
    UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.RDens → UpperTheory.Gal.Gen.HalfInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.RInt := by
  intro h1 h2 h3 h4 n t ht0 ht1 l hl
  obtain ⟨hh, -, hev, hnorm⟩ := h4 n t ht0 ht1
  have hpt : ∀ (θ : Fin n → UnitAddCircle) (σ : Equiv.Perm (Fin n)), pt θ ∘ ⇑σ = pt (θ ∘ ⇑σ) :=
    fun _ _ => rfl
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hmc : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using this
  have hFc : Continuous F := hmc.mul hh
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      ∫ θ : Fin n → UnitAddCircle, F (θ ∘ ⇑σ) = ∫ θ : Fin n → UnitAddCircle, F θ := by
    intro σ
    have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => UnitAddCircle) σ.symm
    rw [← hmp.integral_comp' F]
    congr 1
    funext θ
    congr 1
    funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hae : (fun θ : Fin n → UnitAddCircle => evalAt (pt θ) (hlR (t : ℂ) l) * dens (t : ℂ) (pt θ)) =ᵐ[volume]
      fun θ => ∑ σ : Equiv.Perm (Fin n), F (θ ∘ ⇑σ) := by
    filter_upwards [h1 n] with θ hθ
    rw [h2 n t ht0 ht1 l (pt θ) hθ (hnorm θ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hpt]
  rw [integral_congr_ae hae, integral_finsetSum]
  · simp_rw [hperm]
    rw [hF, h3 n t ht0 ht1 l hl, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    split_ifs <;> simp
  · intro σ _
    have hc : Continuous fun θ : Fin n → UnitAddCircle => θ ∘ ⇑σ :=
      continuous_pi fun i => continuous_apply (σ i)
    exact (hFc.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConj
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem rhoPair_dual {n : ℕ} (l : Fin n → ℤ) :
    rhoPair (fun i => -l (Fin.rev i)) = rhoPair l := by
  unfold rhoPair
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast
  ring

private theorem conj_vPoly (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (vPoly n (t : ℂ)) = vPoly n (t : ℂ) := by
  unfold vPoly
  simp [map_prod, map_div₀]

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.Gen.gammaConj_pf :
    UpperTheory.Gal.Gen.RConj → UpperTheory.Gal.Gen.GammaConj := by
  intro hR F _ _ _ _ n _ _ μ _
  show ∀ z, _
  intro z hinj hz g
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hl' : Antitone (fun i : Fin n => -l (Fin.rev i)) := by
    intro i j hij
    show -l (Fin.rev j) ≤ -l (Fin.rev i)
    exact neg_le_neg (hl (Fin.rev_le_rev.mpr hij))
  have hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹ := by
    rw [Iwasawa.torusPow_neg, ← htp]
    group
  have hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) =
      Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm) := rfl
  have hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i))) := by
    rw [hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂),
      hcomp, zonalSpherical_torusPow_comp]
  have hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      zonalSpherical μ z (Iwasawa.torusPow F n l) := by
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]
  rw [hZinv, hZ]
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹ := by simp
  have m1 := macdonald_formula_hlR (μ := μ) z hl'
  have m2 := macdonald_formula_hlR (μ := μ) z hl
  have hc := hR n ((qF F : ℝ))⁻¹ l z hinj hz
  rw [hcast] at hc
  have hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l := by
    rw [halfModulus_eq, halfModulus_eq, rhoPair_dual]
  have hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l := by
    rw [halfModulus_eq, map_zpow₀]
    simp [sqrtQ]
  have hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹ := by
    rw [← hcast]
    exact conj_vPoly n _
  apply mul_left_cancel₀ hv
  rw [m1, hhm, hc]
  have m2c := congrArg (starRingEnd ℂ) m2
  rw [map_mul, map_mul, hvr, hhmr] at m2c
  rw [m2c]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FixVec
namespace UpperTheory.Gal.Gen

theorem fixVec_pf : FixVec := by
  intro l _ H _ hH V _ _ _ ρ U hU hne
  classical
  let act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U) :=
    fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)
  have act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v) := fun h v => rfl
  letI : MulAction H (V ⧸ U) :=
    { smul := fun h x => act h x
      one_smul := by
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act 1 (U.mkQ v) = U.mkQ v
        rw [act_mk]
        simp
      mul_smul := by
        intro g h x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))
        rw [act_mk, act_mk, act_mk]
        simp }
  have smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x := fun h x => rfl
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : l ∣ Nat.card (V ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]
    exact dvd_pow_self l Module.finrank_pos.ne'
  have h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U) := by
    intro h
    rw [smul_def, map_zero]
  obtain ⟨x, hx, hx0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx0
    rw [eq_comm]
    simpa using hv
  · intro h
    have hfix := hx h
    rw [smul_def, act_mk] at hfix
    exact (Submodule.Quotient.eq U).1 hfix

end UpperTheory.Gal.Gen
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CodimPf
namespace UpperTheory.Gal.Gen

theorem codim_pf : Codim := by
  intro k V M _ _ _ _ _ _ Ψ A B _ h
  let f : V →ₗ[k] M ⧸ A := A.mkQ ∘ₗ Ψ
  have hker : LinearMap.ker f = A.comap Ψ := by
    ext v
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f ≤ B.map A.mkQ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h v)
    refine ⟨b, hb, ?_⟩
    have hz : A.mkQ a = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ha
    simp only [f, LinearMap.comp_apply, ← hab, map_add (f := _), hz, zero_add]
  haveI : FiniteDimensional k (B.map A.mkQ) :=
    Module.Finite.map B A.mkQ
  have h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B :=
    Submodule.finrank_map_le A.mkQ B
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h3
  omega

end UpperTheory.Gal.Gen
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDet
open UpperTheory.Gal.Gen

open Classical in
private noncomputable def rho0 (H : Type) [Group H] [Fintype H] : H →* Matrix H H ℤ where
  toFun u := Matrix.of fun h g => if h = u * g then 1 else 0
  map_one' := by
    ext h g
    simp [Matrix.one_apply]
  map_mul' u v := by
    ext h g
    have e : ∀ x, (if h = u * x then (1 : ℤ) else 0) * (if x = v * g then 1 else 0)
        = if x = v * g then (if h = u * x then 1 else 0) else 0 := by
      intro x
      split_ifs <;> simp
    simp only [Matrix.mul_apply, Matrix.of_apply, e, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_assoc]

theorem UpperTheory.Gal.Gen.groupDet_pf :
    UpperTheory.Gal.Gen.TriMat → UpperTheory.Gal.Gen.DetLow → UpperTheory.Gal.Gen.GroupDet := by
  classical
  intro hT hD k _ _ l _ H _ _ hp a ρ ha hrank
  obtain ⟨Q, P, hQP⟩ := hT l H hp H (rho0 H)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix H H k, A = Matrix.of fun h g : H => a (h * g⁻¹) := ⟨_, rfl⟩
  rw [← hAdef] at hrank
  obtain ⟨R, hR⟩ : ∃ R : H → Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) ℤ,
      R = fun u => Q * rho0 H u * P := ⟨_, rfl⟩
  have hm : ∀ u i j, ∃ m : ℤ, j ≤ i → R u i j - (if i = j then 1 else 0) = (l : ℤ) * m := by
    intro u i j
    by_cases h : j ≤ i
    · obtain ⟨m, hm⟩ := hQP u i j h
      exact ⟨m, fun _ => by rw [hR]; exact hm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hm
  have hAsum : A = ∑ u, a u • (rho0 H u).map (Int.castRingHom k) := by
    ext h g
    have e : ∀ u : H, h = u * g ↔ u = h * g⁻¹ := fun u => by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp [hAdef, Matrix.sum_apply, rho0, e]
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      A' = Q.map (Int.castRingHom k) * A * P.map (Int.castRingHom k) := ⟨_, rfl⟩
  have hA'sum : A' = ∑ u, a u • (R u).map (Int.castRingHom k) := by
    rw [hA'def, hAsum, hR]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]
  have hA' : ∀ i j, A' i j = ∑ u, a u * ((R u i j : ℤ) : k) := by
    intro i j
    rw [hA'sum]
    simp [Matrix.sum_apply]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      B = Matrix.of fun i j => - ∑ u, a u * ((m u i j : ℤ) : k) := ⟨_, rfl⟩
  have hTe : ∀ i j, j ≤ i → (A' + (l : k) • B) i j = (∑ u, a u) * (if i = j then 1 else 0) := by
    intro i j hij
    have e : ∀ u, ((R u i j : ℤ) : k) = (if i = j then 1 else 0) + (l : k) * ((m u i j : ℤ) : k) := by
      intro u
      have := hm u i j hij
      have h2 : R u i j = (if i = j then 1 else 0) + (l : ℤ) * m u i j := by linarith
      rw [h2]
      push_cast
      rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA', hB, Matrix.of_apply, e,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    have : ∀ u, a u * ((l : k) * ((m u i j : ℤ) : k)) = (l : k) * (a u * ((m u i j : ℤ) : k)) :=
      fun u => by ring
    simp only [this]
    simp
  have hdet : (A' + (l : k) • B).det = (∑ u, a u) ^ Fintype.card H := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hTe]
    · intro i j hij
      have hji : j < i := hij
      rw [hTe i j hji.le, if_neg hji.ne', mul_zero]
  have hnA : ∀ i j, ‖A' i j‖ ≤ 1 := by
    intro i j
    rw [hA']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnB : ∀ i j, ‖B i j‖ ≤ 1 := by
    intro i j
    rw [hB, Matrix.of_apply, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnl : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hr : A'.rank ≤ ρ := by
    rw [hA'def]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrank)
  have := hD k (Fintype.card H) A' B (l : k) ρ hnA hnB hnl hr
  rw [hdet, norm_pow] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgPf
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.alg_pf :
    UpperTheory.Gal.Gen.HB → UpperTheory.Gal.Gen.GroupDet → UpperTheory.Gal.Gen.Alg := by
  intro hHB hGD k _ _ l _ H _ _ hH P hP hN
  classical
  have hl0 : 0 ≤ ‖(l : k)‖ := norm_nonneg _
  have hl1 : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hdN : Module.finrank k P ≤ Fintype.card H := by
    have h := Submodule.finrank_le P
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have key : ∀ a : H → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) →
      ‖∑ i, a i * (fun _ => (1 : k)) i‖ ≤ Real.sqrt ‖(l : k)‖ := by
    intro a ha hperp
    have hker : P ≤ LinearMap.ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin := by
      intro c hc
      rw [LinearMap.mem_ker]
      funext g
      have h0 := hperp (fun h => c (h * g)) (hP c hc g)
      have h1 : ∑ h, a (h * g⁻¹) * c h = ∑ i, a i * c (i * g) :=
        Fintype.sum_equiv (Equiv.mulRight g⁻¹) _ _ (fun x => by simp)
      change ∑ h, a (h * g⁻¹) * c h = 0
      rw [h1]
      exact h0
    have hrank : (Matrix.of fun h g : H => a (h * g⁻¹)).rank ≤
        Fintype.card H - Module.finrank k P := by
      have h2 := LinearMap.finrank_range_add_finrank_ker
        (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h2
      have h3 := Submodule.finrank_mono hker
      rw [← Matrix.rank_transpose]
      have h4 : (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.rank =
          Module.finrank k (LinearMap.range
            (Matrix.of fun h g : H => a (h * g⁻¹)).transpose.mulVecLin) := rfl
      omega
    have h1 := hGD k l H hH a _ ha hrank
    rw [Nat.sub_sub_self hdN] at h1
    simp only [mul_one]
    rw [Real.le_sqrt (norm_nonneg _) hl0]
    have hne : Fintype.card H ≠ 0 := Fintype.card_ne_zero
    refine (pow_le_pow_iff_left₀ (by positivity) hl0 hne).mp ?_
    calc (‖∑ i, a i‖ ^ 2) ^ Fintype.card H
        = (‖∑ i, a i‖ ^ Fintype.card H) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (‖(l : k)‖ ^ Module.finrank k P) ^ 2 := by gcongr
      _ = ‖(l : k)‖ ^ (2 * Module.finrank k P) := by rw [← pow_mul, mul_comm]
      _ ≤ ‖(l : k)‖ ^ Fintype.card H := pow_le_pow_of_le_one hl0 hl1 hN
  obtain ⟨c, hc, hcv⟩ := hHB k H P (fun _ => 1) (Real.sqrt ‖(l : k)‖) key
  refine ⟨c, hc, fun h => ?_⟩
  have h5 : ‖(1 : k) - c h‖ ≤ Real.sqrt ‖(l : k)‖ := hcv h
  exact (Real.le_sqrt (norm_nonneg _) hl0).mp h5
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetLow
noncomputable section

namespace UpperTheory.Gal.Gen

private lemma det_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) k) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  classical
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)

private lemma det_zero_of_card {k : Type} [Field k] {N ρ : ℕ}
    (A M : Matrix (Fin N) (Fin N) k) (s : Finset (Fin N)) (hr : A.rank ≤ ρ) (hs : ρ < s.card)
    (hM : ∀ i ∈ s, M i = A i) : M.det = 0 := by
  classical
  by_contra hne
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hne
  have heq : (fun i : s => A i) = (fun i => M i) ∘ (fun i : s => (i : Fin N)) := by
    funext i
    exact (hM i i.2).symm
  have hli' : LinearIndependent k (fun i : s => A i) := by
    rw [heq]
    exact hli.comp _ Subtype.val_injective
  have hle : Module.finrank k (Submodule.span k (Set.range (fun i : s => A i))) ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  rw [finrank_span_eq_card hli', Fintype.card_coe] at hle
  omega

private theorem det_add_smul_eq_sum_powerset_pow_card_mul_det {k : Type} [Field k] {N : ℕ} (A B : Matrix (Fin N) (Fin N) k)
    (c : k) :
    (A + c • B).det = ∑ t ∈ (Finset.univ : Finset (Fin N)).powerset,
      c ^ t.card * (Matrix.of fun r j => if r ∈ t then B r j else A r j).det := by
  classical
  rw [← Matrix.det_transpose]
  simp_rw [← Matrix.det_transpose (Matrix.of _)]
  simp only [Matrix.det_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [add_comm (A _ _)]
  rw [Finset.prod_add, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter,
    Finset.prod_mul_distrib, Finset.prod_const, mul_assoc, mul_smul_comm]

theorem detLow_pf : DetLow := by
  intro k _ _ N A B c ρ hA hB hc hr
  classical
  rw [det_add_smul_eq_sum_powerset_pow_card_mul_det]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t _ => ?_
  rw [norm_mul, norm_pow]
  by_cases ht : N - ρ ≤ t.card
  · have h1 := det_norm_le_one (Matrix.of fun r j => if r ∈ t then B r j else A r j) (by
      intro i j
      simp only [Matrix.of_apply]
      split_ifs
      · exact hB i j
      · exact hA i j)
    calc ‖c‖ ^ t.card * ‖(Matrix.of fun r j => if r ∈ t then B r j else A r j).det‖
        ≤ ‖c‖ ^ t.card * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ‖c‖ ^ (N - ρ) := by
        rw [mul_one]
        exact pow_le_pow_of_le_one (norm_nonneg _) hc ht
  · have h0 : (Matrix.of fun r j => if r ∈ t then B r j else A r j).det = 0 := by
      refine det_zero_of_card A _ tᶜ hr ?_ ?_
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · intro i hi
        funext j
        simp only [Matrix.of_apply, if_neg (Finset.mem_compl.mp hi)]
    rw [h0, norm_zero, mul_zero]
    positivity

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HSPf
noncomputable section

namespace UpperTheory.Gal.Gen

theorem hS_pf : HS := by
  classical
  intro X _ B V hV
  let L := WithLp.linearEquiv 2 ℂ (X → ℂ)
  let V' : Submodule ℂ (EuclideanSpace ℂ X) := V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)
  have hfr : Module.finrank ℂ V' = Module.finrank ℂ V := LinearEquiv.finrank_map_eq L.symm V
  let e := stdOrthonormalBasis ℂ V'
  let f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X := fun i => (e i : EuclideanSpace ℂ X)
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ
  have hfix : ∀ i x, ∑ y, B x y * f i y = f i x := by
    intro i x
    obtain ⟨v, hv, hvf⟩ := (e i).2
    have h1 : ∀ y, f i y = v y := by
      intro y
      have : f i = L.symm v := hvf.symm
      rw [this]
      rfl
    have h2 := congrFun (hV v hv) x
    simp only [Matrix.mulVec, dotProduct] at h2
    simp only [h1]
    exact h2
  let r : X → EuclideanSpace ℂ X := fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))
  have hinner : ∀ i x, inner ℂ (r x) (f i) = f i x := by
    intro i x
    rw [← hfix i x, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [r, RCLike.inner_apply, mul_comm]
  have hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2 := by
    intro x
    have h := hf.sum_inner_products_le (x := r x) (s := Finset.univ)
    have h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [r]
    rw [h3] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm, hinner]
  have hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1 := by
    intro i
    rw [← EuclideanSpace.norm_sq_eq, hf.1 i]
    simp
  calc (Module.finrank ℂ V : ℝ) = ∑ i : Fin (Module.finrank ℂ V'), ∑ x, ‖f i x‖ ^ 2 := by
        simp [hone, hfr]
    _ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsInvariantFlagModL
open Module

namespace UpperTheory.Gal.Gen

private theorem exists_invariant_flag_mod_l (hF : FixVec) (l : ℕ) [Fact l.Prime] (H : Type) [Group H] (hH : IsPGroup l H)
    (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V] (ρ : Representation (ZMod l) H V)
    (m : ℕ) (hm : m ≤ finrank (ZMod l) V) :
    ∃ v : Fin m → V, LinearIndependent (ZMod l) v ∧
      ∀ h j, ρ h (v j) - v j ∈ Submodule.span (ZMod l) (v '' {i | i < j}) := by
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hs⟩ := ih (Nat.le_of_succ_le hm)
    set U := Submodule.span (ZMod l) (Set.range v) with hU
    have hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U := fun j =>
      Submodule.span_mono (Set.image_subset_range _ _)
    have hvU : ∀ j, v j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
      intro h u hu
      have hle : U ≤ U.comap (ρ h) := by
        rw [hU, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have h1 := hmono j (hs h j)
        have h2 := U.add_mem h1 (hvU j)
        simpa using h2
      exact hle hu
    have hne : U ≠ ⊤ := by
      intro htop
      have h1 : finrank (ZMod l) U = m := by
        rw [hU, finrank_span_eq_card hv]; simp
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨x, hx, hxs⟩ := hF l H hH V ρ U hst hne
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · exact (linearIndependent_finSnoc).2 ⟨hv, hx⟩
    · intro h j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · have himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v := by
          ext y
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hi' : i ≠ Fin.last m := ne_of_lt hi
            obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi'
            exact ⟨i', by simp⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
        simp only [Fin.snoc_last]
        rw [himg]
        exact hxs h
      · have himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc} := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i.castSucc, by simpa using hi, by simp⟩
        simp only [Fin.snoc_castSucc]
        exact Submodule.span_mono himg (hs h j)

theorem flag_pf : FixVec → Flag := by
  intro hF l _ H _ hH V _ _ _ ρ
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  obtain ⟨v, hv, hs⟩ := exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (by simp)).ge
  let b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V := Basis.mk hv hsp
  refine ⟨b, ?_⟩
  intro h i j hji
  have hb : ∀ j, b j = v j := fun j => Basis.mk_apply hv hsp j
  have hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j}) := by
    have : (b : _ → V) '' {i | i < j} = v '' {i | i < j} := by
      ext y; simp [hb]
    rw [this, hb]
    exact hs h j
  have hsupp := (Basis.mem_span_image b).1 hmem
  by_contra hne
  have hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _) := by
    simpa using hne
  have := hsupp hi
  exact absurd this (not_lt.2 hji)

end UpperTheory.Gal.Gen
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsCloseVectorUltrametric
noncomputable section

namespace UpperTheory.Gal.Gen

private theorem exists_close_vector_ultrametric (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (r : ℝ) :
    ∀ (n : ℕ) (P : Submodule k (X → k)) (v : X → k), Module.finrank k P = n →
      (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) →
      ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P v hn h
  by_cases hP : P = ⊥
  · subst hP
    refine ⟨0, Submodule.zero_mem _, fun i => ?_⟩
    have key := h (Pi.single i 1) ?_ ?_
    · simpa [Pi.single_apply] using key
    · intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · intro c hc
      have hc0 : c = 0 := by simpa using hc
      simp [hc0]
  · obtain ⟨p0, hp0, hp0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ i, p0 i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp0ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty X := ⟨j⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖p0 i‖)
    have hne : p0 i0 ≠ 0 := by
      intro h0
      have h1 := hi0 j
      rw [h0, norm_zero] at h1
      exact hj (norm_le_zero_iff.mp h1)
    obtain ⟨p, hp⟩ : ∃ p, p = (p0 i0)⁻¹ • p0 := ⟨_, rfl⟩
    have hpP : p ∈ P := hp ▸ P.smul_mem _ hp0
    have hpi0 : p i0 = 1 := by simp [hp, hne]
    have hple : ∀ i, ‖p i‖ ≤ 1 := by
      intro i
      simp only [hp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
      simpa using hi0 i
    obtain ⟨P', hP'⟩ : ∃ P', P' = P ⊓ LinearMap.ker (LinearMap.proj i0 : (X → k) →ₗ[k] k) := ⟨_, rfl⟩
    have hmem : ∀ c, c ∈ P' ↔ c ∈ P ∧ c i0 = 0 := by
      intro c
      simp [hP', Submodule.mem_inf, LinearMap.mem_ker]
    have hlt : P' < P := by
      refine lt_of_le_of_ne (fun c hc => ((hmem c).1 hc).1) ?_
      intro heq
      have h1 : p ∈ P' := heq ▸ hpP
      have h2 := ((hmem p).1 h1).2
      rw [hpi0] at h2
      exact one_ne_zero h2
    have hfr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨c', hc', hb⟩ := ih _ (hn ▸ hfr) P' (v - v i0 • p) rfl (by
      intro a ha hperp
      obtain ⟨s, hs⟩ : ∃ s, s = ∑ i, a i * p i := ⟨_, rfl⟩
      have hsn : ‖s‖ ≤ 1 := by
        rw [hs]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_one₀ (ha i) (norm_nonneg _) (hple i)
      have hsingle : ∀ w : X → k, ∑ i, (Pi.single i0 s : X → k) i * w i = s * w i0 := by
        intro w
        simp [Pi.single_apply, ite_mul]
      have key := h (a - Pi.single i0 s : X → k) ?_ ?_
      · have e : ∑ i, (a - Pi.single i0 s : X → k) i * v i = ∑ i, a i * (v - v i0 • p) i := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
            Finset.sum_sub_distrib, hsingle]
          congr 1
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rwa [e] at key
      · intro i
        by_cases hi : i = i0
        · subst hi
          simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha _) ?_)
          rwa [norm_neg]
        · simpa [Pi.single_apply, hi] using ha i
      · intro c hc
        have hd : c - c i0 • p ∈ P' := by
          refine (hmem _).2 ⟨P.sub_mem hc (P.smul_mem _ hpP), ?_⟩
          simp [hpi0]
        have h0 := hperp _ hd
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at h0
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hsingle]
        have h1 : ∑ i, a i * (c i0 * p i) = c i0 * s := by
          rw [hs, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [h1] at h0
        rw [mul_comm s]
        exact h0)
    refine ⟨v i0 • p + c', P.add_mem (P.smul_mem _ hpP) ((hmem _).1 hc').1, fun i => ?_⟩
    have e : v i - (v i0 • p + c') i = (v - v i0 • p) i - c' i := by
      simp [sub_sub]
    rw [e]
    exact hb i

theorem hB_pf : HB := by
  intro k _ _ X _ P v r h
  exact exists_close_vector_ultrametric k X r _ P v rfl h

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TriMat
open UpperTheory.Gal.Gen

private lemma repr_sum_mul {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X]
    (b : Module.Basis ι k (X → k)) (v : X → k) (i : ι) :
    ∑ x, b.repr (Pi.single x 1) i * v x = b.repr v i := by
  have hv : v = ∑ x, v x • (Pi.single x 1 : X → k) := by
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Finsupp.finsetSum_apply, mul_comm]

private lemma conj_apply {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X] [Fintype ι]
    (b : Module.Basis ι k (X → k)) (M : Matrix X X k) (i j : ι) :
    ((Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix ι X k) * M *
      (Matrix.of fun x j => b j x : Matrix X ι k)) i j = b.repr (M.mulVec (b j)) i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← repr_sum_mul b]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem UpperTheory.Gal.Gen.triMat_pf :
    UpperTheory.Gal.Gen.Flag → UpperTheory.Gal.Gen.TriMat := by
  intro hF l _ H _ hH X _ _ ρ
  let ρ' : Representation (ZMod l) H (X → ZMod l) :=
    ((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp
      (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)
  have hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v := by
    intro h v
    rfl
  obtain ⟨b₀, hb₀⟩ := hF l H hH (X → ZMod l) ρ'
  have hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X :=
    Module.finrank_fintype_fun_eq_card _
  let e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X) := finCongr hcard
  let b := b₀.reindex e
  have hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0 := by
    intro h i j hij
    have := hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)
    simpa [b] using this
  let Q : Matrix (Fin (Fintype.card X)) X ℤ := fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)
  let P : Matrix X (Fin (Fintype.card X)) ℤ := fun x j => ((b j x).val : ℤ)
  refine ⟨Q, P, fun h i j hij => ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1
  have hQ : Q.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix _ X (ZMod l)) := by
    ext i x
    change ((((b.repr (Pi.single x 1) i).val : ℤ)) : ZMod l) = b.repr (Pi.single x 1) i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hP : P.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun x j => b j x : Matrix X _ (ZMod l)) := by
    ext x j
    change ((((b j x).val : ℤ)) : ZMod l) = b j x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i := by
    have h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) =
        ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j := rfl
    rw [h1, Matrix.map_mul, Matrix.map_mul, hQ, hP, conj_apply, hρ']
  have hd := hb h i j hij
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply] at hd
  rw [Int.cast_sub, hc, hd]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij', Ne.symm hij']
end

namespace UpperTheory.Gal.Gen

theorem hB_holds : HB := hB_pf
theorem detLow_holds : DetLow := detLow_pf
theorem fixVec_holds : FixVec := fixVec_pf
theorem flag_holds : Flag := flag_pf fixVec_holds
theorem triMat_holds : TriMat := triMat_pf flag_holds
theorem groupDet_holds : GroupDet := groupDet_pf triMat_holds detLow_holds
theorem alg_holds : Alg := alg_pf hB_holds groupDet_holds
theorem codim_holds : Codim := codim_pf
theorem hS_holds : HS := hS_pf
theorem rFormula_holds : RFormula := rFormula_pf
theorem rConj_holds : RConj := rConj_pf rFormula_holds
theorem wtPos_holds : WtPos := wtPos_pf
theorem meanVal_holds : MeanVal := meanVal_pf
theorem densCont_holds : DensCont := densCont_pf
theorem halfInt_holds : HalfInt := halfInt_pf wtPos_holds meanVal_holds densCont_holds
theorem nullZero_holds : NullZero := nullZero_pf
theorem injAE_holds : InjAE := injAE_pf nullZero_holds
theorem densSymm_holds : DensSymm := densSymm
theorem rDens_holds : RDens := rDens_pf rFormula_holds densSymm_holds
theorem rInt_holds : RInt := rInt_pf injAE_holds rDens_holds halfInt_holds densCont_holds
theorem starEx_holds : StarEx := starEx_pf
theorem symEx_holds : SymEx := symEx_pf
theorem small_holds : Small := small_pf symEx_holds starEx_holds nullZero_holds densCont_holds
theorem gammaEig_holds : GammaEig := gammaEig_pf
theorem gammaInt_holds : GammaInt := gammaInt_pf rInt_holds densCont_holds
theorem gammaConj_holds : GammaConj := gammaConj_pf rConj_holds
theorem repsEx_holds : RepsEx := repsEx_pf
theorem planch_holds : Planch := planch_pf gammaInt_holds gammaConj_holds gammaEig_holds injAE_holds densCont_holds
theorem combine_holds : Combine := combine_pf
theorem restrict_holds : Restrict := restrict_pf
theorem algC_holds : AlgC := algC_pf alg_holds
theorem locOp_holds : LocOp := locOp_pf repsEx_holds planch_holds
theorem satEx_holds : SatEx := satEx_pf
theorem globOp_holds : GlobOp := globOp_pf locOp_holds
theorem neglAt_holds : NeglAt := neglAt_pf globOp_holds small_holds
theorem congSub_holds : CongSub := congSub_pf
theorem tower_holds : Tower := tower_pf congSub_holds
theorem levFacts_holds : LevFacts := levFacts_pf
theorem locComm_holds : LocComm := locComm_pf
theorem ratFin_holds : RatFin := ratFin_pf
theorem ellGrp_holds : EllGrp := ellGrp_pf
theorem ell_holds : Ell := ell_pf ellGrp_holds
theorem wBound_holds : WBound := wBound_pf
theorem countCore_holds : CountCore := countCore_pf hS_holds wBound_holds
theorem cover_holds : Cover := cover_pf levFacts_holds locComm_holds
theorem sep_holds : Sep := sep_pf levFacts_holds locComm_holds ratFin_holds
theorem partFacts_holds : PartFacts := partFacts_pf
theorem count_holds : Count := count_pf countCore_holds cover_holds sep_holds partFacts_holds
theorem countGen_holds : CountGen := countGen_pf count_holds neglAt_holds
theorem stepCore_holds : StepCore := stepCore_pf algC_holds codim_holds partFacts_holds
theorem smoothAt_holds : SmoothAt := smoothAt_pf
theorem step_holds : Step := step_pf smoothAt_holds tower_holds levFacts_holds ell_holds countGen_holds stepCore_holds partFacts_holds
theorem denseGen_holds : DenseGen := denseGen_pf step_holds partFacts_holds
theorem toPolyX_holds : ToPolyX := toPolyX_pf partFacts_holds
theorem kappa_holds : Kappa := kappa_pf
theorem denomBdd_holds : DenomBdd := denomBdd_pf
theorem degLe_holds : DegLe := degLe_pf
theorem blockBound_holds : BlockBound := blockBound_pf
theorem detBound_holds : DetBound := detBound_pf
theorem sizeLe_holds : SizeLe := sizeLe_pf
theorem rhoBound_holds : RhoBound := rhoBound_pf degLe_holds blockBound_holds detBound_holds sizeLe_holds
theorem latFacts_holds : LatFacts := latFacts_pf
theorem levelEx_holds : LevelEx := levelEx_pf
theorem frameW_holds : FrameW := frameW_pf kappa_holds denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds
theorem maxCpt_holds : MaxCpt := maxCpt_pf
theorem powNhds_holds : PowNhds := powNhds_pf
theorem kerOpen_holds : KerOpen := kerOpen_pf powNhds_holds
theorem charSum_holds : CharSum := charSum_pf
theorem twistPart_holds : TwistPart := twistPart_pf
theorem tyStep_holds : TyStep := tyStep_pf levFacts_holds ell_holds kerOpen_holds charSum_holds twistPart_holds

end UpperTheory.Gal.Gen
