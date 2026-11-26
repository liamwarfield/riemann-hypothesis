module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1Gamm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlash
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlash
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem dehH_mon (w : ℕ) (i : Fin (w + 1)) : deh (mon ℂ w i) = Polynomial.X ^ (i : ℕ) := by
  simp [deh, mon]

theorem dehH_slP_mon (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i : ℕ) :
    deh (slP m (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (w - i))) =
      (Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
        (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [deh, slP, Polynomial.smul_eq_C_mul]

theorem dehH_expand (w : ℕ) (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous w) :
    deh p = ∑ i ∈ Finset.range (w + 1),
      Polynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i := by
  have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
  conv_lhs => rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
    p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, dehH_mon]
  simp [deh]

theorem dehH_coeff (w : ℕ) (c : ℕ → ℂ) (j : ℕ) (hj : j < w + 1) :
    (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hj]

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

theorem dehH_slP_sum (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (c : ℕ → ℂ) :
    GlobalTheory.HeckeFamilyMatrices.slP w m (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i) =
      ∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  rw [GlobalTheory.HeckeFamilyMatrices.slP, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, Polynomial.lcoeff_apply,
    LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dehH_coeff w c i (Finset.mem_range.mp hi), Polynomial.smul_eq_C_mul]

theorem dehH_sum_eq (w : ℕ) (q : Polynomial ℂ) (hq : q ∈ Polynomial.degreeLT ℂ (w + 1)) :
    ∑ i ∈ Finset.range (w + 1), Polynomial.C (q.coeff i) * Polynomial.X ^ i = q := by
  ext j
  by_cases hj : j < w + 1
  · exact dehH_coeff w _ j hj
  · rw [Polynomial.finsetSum_coeff]
    rw [Polynomial.mem_degreeLT] at hq
    have h0 : q.coeff j = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hq (by exact_mod_cast not_lt.mp hj))
    rw [h0]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    have : j ≠ i := fun h => hj (h ▸ Finset.mem_range.mp hi)
    simp [this]

theorem deh_homog_iso : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m p hp
    have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
    rw [dehH_expand w p hp, dehH_slP_sum]
    conv_lhs => rw [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
      p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, MvPolynomial.algHom_C, mon, dehH_slP_mon]
    simp [deh]
  · intro p hp
    rw [dehH_expand w p hp]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Polynomial.mem_degreeLT]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  · intro q hq
    refine ⟨∑ i : Fin (w + 1), MvPolynomial.C (q.coeff i) * mon ℂ w i, ?_, ?_⟩
    · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
        ((GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.2.1 i).C_mul _
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      simp only [map_mul, dehH_mon]
      simp only [deh, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i)]
      exact dehH_sum_eq w q hq
  · intro p p' hp hp' he
    rw [(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp, (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p' hp']
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    have h2 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p' (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    rw [← dehH_expand w p hp, he, dehH_expand w p' hp', h2] at h1
    rw [h1]

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlashStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  first | exact @GlobalTheory.KZ.H3.deh_homog_iso | exact GlobalTheory.KZ.H3.deh_homog_iso | (intros; apply GlobalTheory.KZ.H3.deh_homog_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.CocPot

theorem I_mem : Complex.I ∈ Hs := by
  show (0 : ℝ) < Complex.I.im
  simp

theorem hom_inc {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    (γ : SL(2, ℤ)) (z : ℂ) :
    (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z).IsHomogeneous w :=
  (Betti.polySlash_isHomogeneous _ (hF.1 _)).sub (hF.1 z)

theorem inc_eq {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ Hs) :
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z =
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I := by
  obtain ⟨p, hp⟩ := hF.2 γ hγ
  rw [hp z hz, hp _ I_mem]

theorem inc_mul {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (δ : SL(2, ℤ)) :
    slP ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL (γ * δ)) Complex.I)) - F Complex.I =
      slP (δ : Matrix (Fin 2) (Fin 2) ℤ)
          (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I) +
        (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) Complex.I)) - F Complex.I) := by
  have hδI := mob_laws.1 (ofSL δ) _ I_mem
  have hm : mob (ofSL (γ * δ)) Complex.I = mob (ofSL γ) (mob (ofSL δ) Complex.I) := by
    rw [map_mul]
    exact mob_laws.2.1 _ _ _ I_mem
  rw [hm, Matrix.SpecialLinearGroup.coe_mul, ← Betti.polySlash_polySlash, ← inc_eq hF hγ hδI, map_sub]
  abel

end GlobalTheory.KZ.CocPot

namespace GlobalTheory.KZ


open CocPot in
theorem cocP_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro w N l _ _
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w
  refine ⟨fun F hF => ⟨⟨fun γ => ?_, fun γ δ => ?_⟩, fun γ τ hτ => ?_, fun hB => ?_⟩, fun F G => ?_, fun c F => ?_⟩
  · exact d2 _ (hom_inc hF _ _)
  · have hγ : (γ : SL(2, ℤ)) ∈ Gam N l := γ.2
    have key := inc_mul hF hγ (δ : SL(2, ℤ))
    have e1 := d1 ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ (hom_inc hF (γ : SL(2, ℤ)) Complex.I)
    show deh (slP (((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        (F (mob (ofSL ((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ))) Complex.I)) - F Complex.I) = _
    rw [Subgroup.coe_mul, key, map_add (f := _), e1]
    rfl
  · show _ = deh _
    rw [inc_eq hF (show (γ : SL(2, ℤ)) ∈ Gam N l from γ.2) hτ]
  · obtain ⟨⟨q, hq⟩, hqe⟩ := hB
    obtain ⟨p, hp, rfl⟩ := d3 q hq
    refine ⟨fun z => F z - p, p, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have e := congrFun hqe ⟨γ, hγ⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at e
    change _ = deh _ at e
    rw [← d1 _ _ hp, ← map_sub] at e
    have e2 := d4 _ _ ((Betti.polySlash_isHomogeneous _ hp).sub hp) (hom_inc hF _ _) e
    have e3 := inc_eq hF hγ hz
    simp only [map_sub]
    linear_combination e3 - e2
  · funext γ
    simp only [cocP, Pi.add_apply, map_add (f := _), map_sub]
    abel
  · funext γ
    simp only [cocP, Pi.smul_apply, map_smul, map_sub, smul_sub]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PotentialCocycleDehomogenisedLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialCocycleDehomogenised_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.cocP_laws | exact GlobalTheory.KZ.cocP_laws | (intros; apply GlobalTheory.KZ.cocP_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEq
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DictHk

theorem mat_mul {Γ : Subgroup SL(2, ℤ)} (a b : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat ((a * b : Γ) : SL(2, ℤ)) = GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat b := rfl

theorem mat_mul_inv {Γ : Subgroup SL(2, ℤ)} (a : Γ) :
    GlobalTheory.HeckeFamilyMatrices.mat a * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ)) = 1 := by
  rw [← mat_mul, mul_inv_cancel]; rfl

theorem mat_one {Γ : Subgroup SL(2, ℤ)} : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := rfl

theorem cancel_right {Γ : Subgroup SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (a : Γ)
    (h : A * GlobalTheory.HeckeFamilyMatrices.mat a = B * GlobalTheory.HeckeFamilyMatrices.mat a) : A = B := by
  have := congrArg (· * GlobalTheory.HeckeFamilyMatrices.mat ((a⁻¹ : Γ) : SL(2, ℤ))) h
  simpa only [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one] using this

theorem det_pos {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type}
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hα : 0 < α.det) (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (i : ι) :
    0 < (δ i).det := by
  obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
  rw [h, det_mul, det_mul]
  simpa using hα

theorem exists_perm {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} [Fintype ι]
    {δ : ι → Matrix (Fin 2) (Fin 2) ℤ} (hδ : GlobalTheory.HeckeFamilyMatrices.IsDCReps Γ α δ) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ (π i) := by
  classical
  have hf : ∀ i, ∃ j, ∃ γ' : Γ, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat γ' * δ j := by
    intro i
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨j, ⟨γ', h'⟩, -⟩ := hδ.2 γ₁ (γ₂ * γ)
    refine ⟨j, γ', ?_⟩
    rw [h, ← h', mat_mul, Matrix.mul_assoc]
  choose f g hfg using hf
  have hinj : Function.Injective f := by
    intro i i' hii
    obtain ⟨γ₁, γ₂, h⟩ := hδ.1 i
    obtain ⟨k, -, hk⟩ := hδ.2 γ₁ γ₂
    have e1 : i = k := hk i ⟨1, by rw [mat_one, Matrix.one_mul, h]⟩
    have e2 : i' = k := by
      refine hk i' ⟨g i * (g i')⁻¹, ?_⟩
      rw [← h]
      apply cancel_right γ
      rw [hfg i, Matrix.mul_assoc, hfg i', ← hii, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel_right]
    rw [e1, e2]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ⟨g i, hfg i⟩⟩

theorem incr {N l w : ℕ} {ι : Type} [Fintype ι] {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : ∀ i, 0 < (δ i).det) {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w (Gam N l))
    (γ : GlobalTheory.HeckeFamilyMatrices.Lev N l) (π : Equiv.Perm ι) (g : ι → GlobalTheory.HeckeFamilyMatrices.Lev N l)
    (hg : ∀ i, δ i * GlobalTheory.HeckeFamilyMatrices.mat γ = GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i)) (z : ℂ) (hz : z ∈ Hs) :
    slP (GlobalTheory.HeckeFamilyMatrices.mat γ) ((∑ i, opP ℂ (δ i) F) (mob (ofSL γ) z)) - (∑ i, opP ℂ (δ i) F) z =
      ∑ i, slP (δ (π i)) (slP (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (F (mob (ofSL (g i)) Complex.I)) - F Complex.I) := by
  obtain ⟨hmem, hmul, -, -, hSL, htoGQ⟩ := GlobalTheory.KZ.mob_laws
  obtain ⟨hslmul, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 : ∀ a : GlobalTheory.HeckeFamilyMatrices.Lev N l, 0 < (GlobalTheory.HeckeFamilyMatrices.mat a).det := fun a => by simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sum]
  rw [← Equiv.sum_comp π (fun i => opP ℂ (δ i) F z), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨p, hp⟩ := hF.2 (g i) (g i).2
  have hz' := hmem (toGQ (δ (π i))) z hz
  rw [hp _ hI, ← hp _ hz']
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [sub_left_inj]
  have hL : mob (toGQ (δ i)) (mob (ofSL γ) z) = mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z := by
    rw [htoGQ _ _ (hdet i) (h1 γ), hSL, hmul _ _ _ hz]
  have hR : mob (ofSL (g i)) (mob (toGQ (δ (π i))) z) =
      mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z := by
    rw [htoGQ _ _ (h1 (g i)) (hdet (π i)), hSL, hmul _ _ _ hz]
  have hs1 := hslmul (δ i) (GlobalTheory.HeckeFamilyMatrices.mat γ) (F (mob (toGQ (δ i * GlobalTheory.HeckeFamilyMatrices.mat γ)) z))
  have hs2 := hslmul (GlobalTheory.HeckeFamilyMatrices.mat (g i)) (δ (π i)) (F (mob (toGQ (GlobalTheory.HeckeFamilyMatrices.mat (g i) * δ (π i))) z))
  rw [hL, hR, ← hs1, ← hs2, hg i]

theorem dict_hk : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι]
    (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det →
    GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l),
    (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) =
        GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro N l w α ι _ δ _ _ hα hδ F hF
  have hdet := det_pos hα hδ
  obtain ⟨-, -, hslhom, -⟩ := GlobalTheory.KZ.polySlash_laws ℂ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  refine ⟨⟨fun z => ?_, fun γ hγ => ?_⟩, ?_⟩
  · simp only [Finset.sum_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => hslhom _ w _ (hF.1 _)
  · obtain ⟨π, hπ⟩ := exists_perm hδ (⟨γ, hγ⟩ : GlobalTheory.HeckeFamilyMatrices.Lev N l)
    choose g hg using hπ
    exact ⟨_, fun z hz => incr hdet hF ⟨γ, hγ⟩ π g hg z hz⟩
  · funext γ
    have hex := exists_perm hδ γ
    simp only [GlobalTheory.HeckeFamilyMatrices.hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, Finset.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cocP, incr hdet hF γ hex.choose (fun i => (hex.choose_spec i).choose)
      (fun i => (hex.choose_spec i).choose_spec) _ hI, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w).1 _ _ ((hslhom _ w _ (hF.1 _)).sub (hF.1 _))]
    rfl

end GlobalTheory.KZ.DictHk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEqStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSum_potentials_cocycle_eq : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det → GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l), (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧ cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) = GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.DictHk.dict_hk | exact GlobalTheory.KZ.DictHk.dict_hk | (intros; apply GlobalTheory.KZ.DictHk.dict_hk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChosenDiamondMatrixLetterOperatorsCosetSums
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChosenDiamondMatrixLetterOperatorsCosetSums
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DiamondOperatorFamilies

theorem isDiamondMatrixAtLevel_of_gamma1Gamma0 {N l d : ℕ} (hl : l.Prime) (hlN : ¬ l ∣ N) {γ : SL(2, ℤ)} (h : GlobalTheory.KZ.IsDiam N l d γ) :
    GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) γ := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hc : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have h0' : γ ∈ CongruenceSubgroup.Gamma0 N := h0
  have h1' : γ ∈ CongruenceSubgroup.Gamma0 l := h1
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem] at h0' h1' ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0' h1' ⊢
    push_cast
    exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hc) h0' h1'
  · simpa [en, GlobalTheory.HeckeFamilyMatrices.mat] using h2

theorem sgD_fams : ∀ (N l : ℕ), 0 < N → l.Prime → ¬ l ∣ N → (∀ d : ℕ, Nat.Coprime d N → GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) (sgD N l d)) ∧ (∀ q : ℕ, opL ℂ N l (Letter.T q) = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.tqFam q (sgD N l q) i)) ∧ opL ℂ N l Letter.U = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.ulFam l i) ∧ ∀ d : ℕ, opL ℂ N l (Letter.D d) = ∑ _i : Unit, opP ℂ (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) := by
  intro N l hN hl hlN
  refine ⟨fun d hd => isDiamondMatrixAtLevel_of_gamma1Gamma0 hl hlN (Betti.isDiam_sgD hN.ne' hl.ne_zero hd), fun q => ?_, ?_, fun d => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.tqFam, Fin.coe_castSucc, Fin.is_lt, if_true, Fin.val_last,
      lt_irrefl, if_false, GlobalTheory.HeckeFamilyMatrices.dg, GlobalTheory.HeckeFamilyMatrices.mat]
  · simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.ulFam]
  · simp [opL, GlobalTheory.HeckeFamilyMatrices.mat]

end GlobalTheory.KZ.DiamondOperatorFamilies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChosenDiamondMatrixLetterOperatorsCosetSumsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums : ∀ (N l : ℕ), 0 < N → l.Prime → ¬ l ∣ N → (∀ d : ℕ, Nat.Coprime d N → GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) (sgD N l d)) ∧ (∀ q : ℕ, opL ℂ N l (Letter.T q) = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.tqFam q (sgD N l q) i)) ∧ opL ℂ N l Letter.U = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.ulFam l i) ∧ ∀ d : ℕ, opL ℂ N l (Letter.D d) = ∑ _i : Unit, opP ℂ (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) := by
  first | exact @GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams | exact GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams | (intros; apply GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDim
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDim
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem polySlash_one_of_mem (w : ℕ) (p : Polynomial ℂ) (hp : p ∈ Polynomial.degreeLT ℂ (w + 1)) :
    GlobalTheory.HeckeFamilyMatrices.slP w (1 : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  simp [GlobalTheory.HeckeFamilyMatrices.slP]
  rw [Polynomial.mem_degreeLT] at hp
  have hn : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  conv_rhs => rw [p.as_sum_range' (w + 1) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_X_eq_monomial]

theorem eichlerShimuraCocycle_eq_zero_of_closure (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (hz : ∀ s ∈ S, (z : Γ → Polynomial ℂ) s = 0) :
    (z : Γ → Polynomial ℂ) = 0 := by
  obtain ⟨hdeg, hco⟩ := z.2
  have hone : (z : Γ → Polynomial ℂ) 1 = 0 := by
    have h := hco 1 1
    rw [mul_one] at h
    have hid : GlobalTheory.HeckeFamilyMatrices.slP w (GlobalTheory.HeckeFamilyMatrices.mat (1 : Γ)) ((z : Γ → Polynomial ℂ) 1) = (z : Γ → Polynomial ℂ) 1 := by
      have : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := by simp [GlobalTheory.HeckeFamilyMatrices.mat]
      rw [this]
      exact polySlash_one_of_mem w _ (hdeg 1)
    rw [hid] at h
    have : (z : Γ → Polynomial ℂ) 1 + (z : Γ → Polynomial ℂ) 1 - (z : Γ → Polynomial ℂ) 1 = 0 := by
      rw [← h]; ring
    simpa using this
  let K : Subgroup Γ :=
    { carrier := {γ | (z : Γ → Polynomial ℂ) γ = 0}
      mul_mem' := by
        intro a b ha hb
        show (z : Γ → Polynomial ℂ) (a * b) = 0
        rw [hco, ha.out, hb.out, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := by
        intro a ha
        show (z : Γ → Polynomial ℂ) a⁻¹ = 0
        have h := hco a a⁻¹
        rw [mul_inv_cancel, hone, ha.out, map_zero, zero_add] at h
        exact h.symm }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).2 hz
  rw [hS] at hle
  funext γ
  exact hle (Subgroup.mem_top γ)

theorem eichlerShimuraCocycles_finiteDimensional_of_fg (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ] (w : ℕ) :
    FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) := by
  obtain ⟨S, hS, hSfinite⟩ := (Group.fg_iff).1 (inferInstance : Group.FG Γ)
  letI := hSfinite.fintype
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ (w + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (w + 1)).symm
  let g : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w →ₗ[ℂ] (S → Polynomial.degreeLT ℂ (w + 1)) :=
    LinearMap.pi fun s => LinearMap.codRestrict (Polynomial.degreeLT ℂ (w + 1))
      ((LinearMap.proj (s : Γ)).comp (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w).subtype) (fun z => z.2.1 s)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 := eichlerShimuraCocycle_eq_zero_of_closure Γ w z (S : Set Γ) hS (fun s hs => by
      have := congrArg Subtype.val (congrFun hz ⟨s, hs⟩)
      exact this)
    exact Subtype.ext h0
  exact Module.Finite.of_injective g hg

theorem lev_fd : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  intro N l w hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (GlobalTheory.HeckeFamilyMatrices.Lev N l).FiniteIndex := by unfold GlobalTheory.HeckeFamilyMatrices.Lev; infer_instance
  haveI : Group.FG (GlobalTheory.HeckeFamilyMatrices.Lev N l) := Subgroup.fg_of_index_ne_zero _
  exact eichlerShimuraCocycles_finiteDimensional_of_fg _ w

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraCocyclesGammaOneGammaZeroFiniteDimStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  first | exact @GlobalTheory.KZ.H3.lev_fd | exact GlobalTheory.KZ.H3.lev_fd | (intros; apply GlobalTheory.KZ.H3.lev_fd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPoly
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPoly
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.GenEigIdem

open Polynomial Module

section SlopeTestRemainingChoices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def stabAlg (Z B : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {f | (∀ z ∈ Z, f z ∈ Z) ∧ ∀ z ∈ B, f z ∈ B}
  mul_mem' := fun {f g} hf hg =>
    ⟨fun z hz => hf.1 _ (hg.1 z hz), fun z hz => hf.2 _ (hg.2 z hz)⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun z hz => Z.add_mem (hf.1 z hz) (hg.1 z hz),
     fun z hz => B.add_mem (hf.2 z hz) (hg.2 z hz)⟩
  algebraMap_mem' := fun c =>
    ⟨fun z hz => by simpa [Module.algebraMap_end_apply] using Z.smul_mem c hz,
     fun z hz => by simpa [Module.algebraMap_end_apply] using B.smul_mem c hz⟩

def quotAlgHom (Z B : Submodule K V) :
    stabAlg Z B →ₐ[K] Module.End K (Z ⧸ B.comap Z.subtype) where
  toFun f := (B.comap Z.subtype).mapQ (B.comap Z.subtype)
    ((f : Module.End K V).restrict f.2.1) (fun z hz => f.2.2 _ hz)
  map_one' := by ext z; rfl
  map_mul' f g := by ext z; rfl
  map_zero' := by ext z; rfl
  map_add' f g := by ext z; rfl
  commutes' c := by ext z; rfl

theorem quotAlgHom_mk (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(f : Module.End K V) z, f.2.1 z z.2⟩ := rfl

theorem quotAlgHom_mk_eq_zero (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) = 0 ↔ (f : Module.End K V) z ∈ B := by
  rw [quotAlgHom_mk, Submodule.Quotient.mk_eq_zero]; rfl

theorem exists_poly_genEig (M : Type) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A : Module.End K M) (c : K) :
    ∃ p : K[X], p.eval c = 1 ∧
      ∀ w, aeval A ((X - C c) ^ finrank K M) (aeval A p w) = 0 := by
  set χ := A.charpoly with hχdef
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  set a := χ.rootMultiplicity c
  set r := χ /ₘ (X - C c) ^ a
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hχ
  have hfac : (X - C c) ^ a * r = χ := pow_mul_divByMonic_rootMultiplicity_eq χ c
  have ha : a ≤ finrank K M := by
    have h1 : (X - C c) ^ a ∣ χ := ⟨r, hfac.symm⟩
    have h2 := natDegree_le_of_dvd h1 hχ
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one, hχdef, LinearMap.charpoly_natDegree] at h2
  refine ⟨C (r.eval c)⁻¹ * r, by simp [hr], fun w => ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (X - C c) ^ finrank K M * (C (r.eval c)⁻¹ * r) =
      C (r.eval c)⁻¹ * (X - C c) ^ (finrank K M - a) * χ := by
    rw [← hfac]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_add]
    ring
  rw [this, map_mul, LinearMap.aeval_self_charpoly, mul_zero, LinearMap.zero_apply]

end SlopeTestRemainingChoices

end GlobalTheory.GenEigIdem

namespace GlobalTheory

open Polynomial Module GlobalTheory.GenEigIdem

theorem exists_genEig_idem_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  intro K _ V _ _ Z B ι S T lam _hBZ hfd hZ hB hcomm hgen
  let Tg : {t // S t} → stabAlg Z B := fun t => ⟨T t.1, hZ t.1 t.2, hB t.1 t.2⟩
  let φ := quotAlgHom Z B
  let d := finrank K (Z ⧸ B.comap Z.subtype)
  have hex : ∀ t : {t // S t}, ∃ p : K[X], p.eval (lam t.1) = 1 ∧
      ∀ w, aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d) (aeval (φ (Tg t)) p w) = 0 :=
    fun t => exists_poly_genEig _ _ _
  choose p hp1 hp2 using hex
  let N : {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun t =>
    LinearMap.ker (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d))
  let Ninf : Finset {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun F => ⨅ t ∈ F, N t
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset {t // S t} => finrank K (Ninf F)).wf.has_min
    Set.univ ⟨∅, trivial⟩
  classical
  have hFle : ∀ s, Ninf F ≤ N s := by
    intro s
    have hins : Ninf (insert s F) = N s ⊓ Ninf F := Finset.iInf_insert _ _ _
    have hmin : ¬ finrank K (Ninf (insert s F)) < finrank K (Ninf F) := hF (insert s F) trivial
    have heq : Ninf (insert s F) = Ninf F := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hins]; exact inf_le_right
      · exact not_lt.mp hmin
    rw [← heq, hins]; exact inf_le_left
  have hinv : ∀ (s t : {t // S t}) (q : K[X]) (w : Z ⧸ B.comap Z.subtype), w ∈ N t →
      aeval (φ (Tg s)) q w ∈ N t := by
    intro s t q w hw
    have hc : Commute (φ (Tg s)) (φ (Tg t)) := by
      refine LinearMap.ext fun w => Submodule.Quotient.induction_on _ w fun z => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, quotAlgHom_mk, quotAlgHom_mk, quotAlgHom_mk,
        quotAlgHom_mk, Submodule.Quotient.eq]
      exact hcomm s.1 t.1 s.2 t.2 z z.2
    have hc2 : Commute (aeval (φ (Tg s)) q) (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d)) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
        (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
          hc.symm).symm
    have hw' := LinearMap.mem_ker.mp hw
    refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hw', map_zero]
  have hprod : ∀ (l : List {t // S t}) (w : Z ⧸ B.comap Z.subtype) (t : {t // S t}), t ∈ l →
      φ (l.map fun s => aeval (Tg s) (p s)).prod w ∈ N t := by
    intro l
    induction l with
    | nil => intro w t ht; simp at ht
    | cons a l ih =>
      intro w t ht
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← aeval_algHom_apply]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact LinearMap.mem_ker.mpr (hp2 _ _)
      · exact hinv _ _ _ _ (ih _ _ ht')
  let P : FreeAlgebra K ι := (F.toList.map fun t => aeval (FreeAlgebra.ι K t.1) (p t)).prod
  let Q : stabAlg Z B := (F.toList.map fun t => aeval (Tg t) (p t)).prod
  have hPQ : FreeAlgebra.lift K T P = (Q : Module.End K V) := by
    rw [show (Q : Module.End K V) = (stabAlg Z B).val Q from rfl]
    simp only [P, Q, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
    rfl
  have hPmem : P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}) := by
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem (FreeAlgebra.ι K) (show t.1 ∈ {t | S t} from t.2)))
      (aeval_mem_adjoin_singleton K _)
  have hPlam : FreeAlgebra.lift K lam P = 1 := by
    simp only [P, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply, coe_aeval_eq_eval, hp1]
  refine ⟨P, hPmem, hPlam, fun z hz s hs => ?_⟩
  rw [hPQ]
  have hQz : (Q : Module.End K V) z ∈ Z := Q.2.1 z hz
  refine hgen _ hQz d (fun t ht => ?_) s hs
  let U : stabAlg Z B := (Tg ⟨t, ht⟩ - algebraMap K (stabAlg Z B) (lam t)) ^ d
  have hU : (U : Module.End K V) = (T t - lam t • 1) ^ d := by
    simp [U, Tg, Algebra.algebraMap_eq_smul_one]
  rw [← hU]
  have key : φ U (Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩) = 0 := by
    have h1 : φ Q (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩ := quotAlgHom_mk _ _ _ _
    rw [← h1]
    have hφU : φ U = aeval (φ (Tg ⟨t, ht⟩)) ((X - C (lam t)) ^ d) := by
      simp [U]
    rw [hφU]
    refine LinearMap.mem_ker.mp (hFle ⟨t, ht⟩ ?_)
    simp only [Ninf, Submodule.mem_iInf]
    intro s' hs'
    exact hprod _ _ _ (Finset.mem_toList.mpr hs')
  exact (quotAlgHom_mk_eq_zero Z B U _).mp key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPolyStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  first | exact @GlobalTheory.exists_genEig_idem_poly | exact GlobalTheory.exists_genEig_idem_poly | (intros; apply GlobalTheory.exists_genEig_idem_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystem
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.SSPotBr

def opZ (N l w : ℕ) : Letter → Module.End ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ)
  | Letter.T q => GlobalTheory.HeckeFamilyMatrices.TqZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w q (sgD N l q)
  | Letter.U => GlobalTheory.HeckeFamilyMatrices.UlZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w l
  | Letter.D d => GlobalTheory.HeckeFamilyMatrices.DdZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w (sgD N l d)

section
open GlobalTheory.HeckeFamilyMatrices Polynomial

theorem eichlerShimuraCoboundaries_le_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  rintro z ⟨⟨p, hp⟩, rfl⟩
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change GlobalTheory.HeckeFamilyMatrices.slP w (mat (γ * δ : Γ)) p - p = GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) (GlobalTheory.HeckeFamilyMatrices.slP w (mat γ) p - p) + (GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) p - p)
    have e : mat (γ * δ : Γ) = mat γ * mat δ := by
      simp only [mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [e, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

end

theorem letter_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) :
    ∀ F ∈ Pot ℂ w (Gam N l), opL ℂ N l T F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (opL ℂ N l T F) = opZ N l w T (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro F hF
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨hsg, hTq, hU, hD⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN hl hlN
  cases T with
  | T q =>
    obtain ⟨hq, hqN⟩ := hT
    have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)
    rw [hTq q, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 q) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q hcop)) F hF
  | U =>
    rw [hU, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 l) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU F hF
  | D d =>
    rw [hD d, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) _ _ hN0 hl0 (by simp) (rD _ _ (hsg d hT)) F hF

theorem lift_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) {P : FreeAlgebra ℂ Letter}
    (hP : P ∈ admissibleLettersSubalgebra ℂ N l) :
    ∀ F ∈ Pot ℂ w (Gam N l), FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (FreeAlgebra.lift ℂ (opL ℂ N l) P F) =
        FreeAlgebra.lift ℂ (opZ N l w) P (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  have hN0 : 0 < N := by omega
  obtain ⟨-, hadd, hsmul⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws w N l hN0 hl.pos
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro F hF
    simp only [FreeAlgebra.lift_ι_apply]
    exact letter_pot N l w hN hl hlN T hT F hF
  | algebraMap r =>
    intro F hF
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).smul_mem r hF, hsmul r F⟩
  | add x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hx F hF
    obtain ⟨h3, h4⟩ := hy F hF
    simp only [map_add (f := _), LinearMap.add_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).add_mem h1 h3, by rw [hadd, h2, h4]⟩
  | mul x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hy F hF
    obtain ⟨h3, h4⟩ := hx _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h3, by rw [h4, h2]⟩

end GlobalTheory.KZ.SSPotBr

namespace GlobalTheory.KZ.SSPotBr

theorem ssPotB_at_newform : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N →
    Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
    α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
    ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α →
    (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  intro k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 lam hlT hlU hlD
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hsg, -, -, -⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN5 hl hlN
  have hcopq : ∀ q, q.Prime → ¬ q ∣ N * l → Nat.Coprime q N := fun q hq hqN =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)

  obtain ⟨q0, hq0le, hq0⟩ := Nat.exists_infinite_primes (N * l + 1)
  have hq0N : ¬ q0 ∣ N * l := fun h => by
    have := Nat.le_of_dvd (Nat.mul_pos hN0 hl0) h; omega

  have hpres : ∀ t, admitted N l t →
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) := by
    intro t ht
    cases t with
    | T q =>
      obtain ⟨hq, hqN⟩ := ht
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q (hcopq q hq hqN)))
      exact ⟨a, b⟩
    | U =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU
      exact ⟨a, b⟩
    | D d =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _ (by simp) (rD _ _ (hsg d ht))
      exact ⟨a, b⟩

  have comm := fun (q q' d d' : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N * l)
      (hd : Nat.Coprime d N) (hd' : Nat.Coprime d' N) =>
    GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 N l k hN5 hl hlN hk3 hk q q' (sgD N l q) (sgD N l q') (sgD N l d) (sgD N l d') (d : ZMod N)
      (d' : ZMod N) hq hqN hq' hq'N (hsg q (hcopq q hq hqN)) (hsg q' (hcopq q' hq' hq'N)) (hsg d hd) (hsg d' hd')
  have h1N : Nat.Coprime 1 N := Nat.coprime_one_left N
  have hcomm : ∀ t t', admitted N l t → admitted N l t' → ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2),
      opZ N l (k - 2) t (opZ N l (k - 2) t' z) - opZ N l (k - 2) t' (opZ N l (k - 2) t z) ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro t t' ht ht' z hz
    cases t with
    | T q =>
      cases t' with
      | T q' => exact (comm q q' 1 1 ht.1 ht.2 ht'.1 ht'.2 h1N h1N z hz).1
      | U => exact (comm q q 1 1 ht.1 ht.2 ht.1 ht.2 h1N h1N z hz).2.1
      | D d => exact (comm q q d 1 ht.1 ht.2 ht.1 ht.2 ht' h1N z hz).2.2.1
    | U =>
      cases t' with
      | T q' =>
        have := (comm q' q' 1 1 ht'.1 ht'.2 ht'.1 ht'.2 h1N h1N z hz).2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U => rw [sub_self]; exact Submodule.zero_mem _
      | D d => exact (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht' h1N z hz).2.2.2.1
    | D d =>
      cases t' with
      | T q' =>
        have := (comm q' q' d 1 ht'.1 ht'.2 ht'.1 ht'.2 ht h1N z hz).2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U =>
        have := (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht h1N z hz).2.2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | D d' => exact (comm q0 q0 d d' hq0 hq0N hq0 hq0N ht ht' z hz).2.2.2.2

  have key : ∀ e : (ZMod N)ˣ → ℕ, (∀ u, Nat.Coprime (e u) N) → (∀ u, ((e u : ℕ) : ZMod N) = u) →
      ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      (∀ q, q.Prime → ¬ q ∣ N * l → (opZ N l (k - 2) (Letter.T q) - lam (Letter.T q) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (opZ N l (k - 2) Letter.U - lam Letter.U • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) ∧
      ∀ u d, e u = d → (opZ N l (k - 2) (Letter.D d) - lam (Letter.D d) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro e he1 he2 z hz n hgen
    have hσD : ∀ u : (ZMod N)ˣ, GlobalTheory.HeckeFamilyMatrices.IsDiam N l (u : ZMod N) (sgD N l (e u)) := fun u => by
      have := hsg (e u) (he1 u); rwa [he2 u] at this
    have hchi : ∀ u : (ZMod N)ˣ, lam (Letter.D (e u)) = g.χ (ZMod.castHom hN (ZMod g.M) (u : ZMod N)) := fun u => by
      rw [hlD _ (he1 u), ← he2 u, map_natCast (ZMod.castHom hN (ZMod g.M))]
    obtain ⟨cT, cU, cD⟩ := GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 (fun q => sgD N l q)
      (fun u => sgD N l (e u)) (fun q hq hqN => hsg q (hcopq q hq hqN)) hσD z hz n
      (fun q hq hqN => by have h := hgen (Letter.T q) ⟨hq, hqN⟩; rw [hlT q hq hqN] at h; exact h)
      (by have h := hgen Letter.U trivial; rw [hlU] at h; exact h)
      (fun u => by have h := hgen (Letter.D (e u)) (he1 u); rw [hchi u] at h; exact h)
    refine ⟨fun q hq hqN => ?_, ?_, ?_⟩
    · rw [hlT q hq hqN]; exact cT q hq hqN
    · rw [hlU]; exact cU
    · rintro u d rfl
      rw [hchi u]; exact cD u
  have hval1 : ∀ u : (ZMod N)ˣ, Nat.Coprime (u : ZMod N).val N := fun u => ZMod.val_coe_unit_coprime u
  have hval2 : ∀ u : (ZMod N)ˣ, (((u : ZMod N).val : ℕ) : ZMod N) = u := fun u => ZMod.natCast_zmod_val _
  have heig : ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      ∀ t, admitted N l t → (opZ N l (k - 2) t - lam t • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro z hz n hgen t ht
    cases t with
    | T q => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).1 q ht.1 ht.2
    | U => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).2.1
    | D d =>
      have hd : Nat.Coprime d N := ht
      refine (key (fun u => if (u : ZMod N) = (d : ZMod N) then d else (u : ZMod N).val) ?_ ?_ z hz n hgen).2.2
        (ZMod.unitOfCoprime d hd) d (if_pos (ZMod.coe_unitOfCoprime d hd))
      · intro u; split_ifs
        · exact hd
        · exact hval1 u
      · intro u; split_ifs with h
        · exact h.symm
        · exact hval2 u
  obtain ⟨P, hP, hP1, hPz⟩ := GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ) (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2))
    (GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) Letter (admitted N l) (opZ N l (k - 2)) lam (eichlerShimuraCoboundaries_le_eichlerShimuraCocycles _ _)
    (GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional N l (k - 2) hN0 hl0) (fun t ht => (hpres t ht).1) (fun t ht => (hpres t ht).2) hcomm heig
  refine ⟨P, hP, hP1, fun F hF T hT => ?_⟩
  obtain ⟨hD1, hD2, hD3⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws (k - 2) N l hN0 hl0
  obtain ⟨hPF, hcPF⟩ := lift_pot N l (k - 2) hN5 hl hlN hP F hF
  obtain ⟨hTF, hcTF⟩ := letter_pot N l (k - 2) hN5 hl hlN T hT _ hPF
  have hG : (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) = opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) +
        (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F := by
    simp [sub_eq_add_neg, neg_smul]
  have hGpot : opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) + (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈
      Pot ℂ (k - 2) (Gam N l) :=
    (Betti.potSub ℂ (k - 2) (Gam N l)).add_mem hTF ((Betti.potSub ℂ (k - 2) (Gam N l)).smul_mem _ hPF)
  rw [hG]
  refine (hD1 _ hGpot).2.2 ?_
  rw [hD2, hD3, hcTF, hcPF]
  have := hPz (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) (hD1 F hF).1 T hT
  simpa [sub_eq_add_neg, neg_smul] using this

end GlobalTheory.KZ.SSPotBr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystemStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_potentials_at_newform_eigensystem : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  first | exact @GlobalTheory.KZ.SSPotBr.ssPotB_at_newform | exact GlobalTheory.KZ.SSPotBr.ssPotB_at_newform | (intros; apply GlobalTheory.KZ.SSPotBr.ssPotB_at_newform <;> assumption)
end
