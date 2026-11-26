module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateModularFamilyAlongSeparatingFamily
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZMod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEq
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.WpSep

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → x = y ∨ x = -y := by
  intro N _ τ x y hx hy h1
  obtain ⟨hsub, hadd, hmem, -, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact Or.inl ((hsub x y).1 h)
  · right
    have h2 := (tauPair τ).lattice.add_mem (hadd x y) h
    rw [sub_add_cancel] at h2
    have h3 := (hmem (x + y)).1 h2
    exact eq_neg_of_add_eq_zero_left h3

end GlobalTheory.FN.WpSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEqStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → x = y ∨ x = -y := by
  first | exact @GlobalTheory.FN.WpSep.main | exact GlobalTheory.FN.WpSep.main | (intros; apply GlobalTheory.FN.WpSep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZMod
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNSep

theorem finite_nat_roots (a b c : ℂ) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {n : ℕ | a + (n : ℂ) * b + (n : ℂ) ^ 2 * c = 0}.Finite := by
  set P : Polynomial ℂ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have e0 := congrArg (fun q => q.coeff 0) h0
    have e1 := congrArg (fun q => q.coeff 1) h0
    have e2 := congrArg (fun q => q.coeff 2) h0
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hf := (Polynomial.finite_setOf_isRoot hP).preimage (f := (Nat.cast : ℕ → ℂ)) Nat.cast_injective.injOn
  refine hf.subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  rw [Polynomial.IsRoot.def]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination hn

theorem vmul_apply {N : ℕ} (a b : ZMod N) (α : GL (Fin 2) (ZMod N)) (j : Fin 2) :
    vmul ![a, b] α j = a * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j + b * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j := by
  simp [vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (hx : x ≠ 0) : vmul x α ≠ 0 := by
  intro h
  apply hx
  have : Matrix.vecMul (vmul x α) ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [vmul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [← this, h, Matrix.zero_vecMul]

end GlobalTheory.FNSep

namespace GlobalTheory.FNSep

theorem eq_or_eq_neg_of_rows {N : ℕ} (α β : GL (Fin 2) (ZMod N))
    (h0 : vmul ![1, 0] α = vmul ![1, 0] β ∨ vmul ![1, 0] α = -vmul ![1, 0] β)
    (h1 : vmul ![0, 1] α = vmul ![0, 1] β ∨ vmul ![0, 1] α = -vmul ![0, 1] β)
    (h2 : vmul ![1, 1] α = vmul ![1, 1] β ∨ vmul ![1, 1] α = -vmul ![1, 1] β) :
    α = β ∨ α = -β := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · have E0 : ∀ j, _ := fun j => congrFun h0 j
    have E1 : ∀ j, _ := fun j => congrFun h1 j
    have E2 : ∀ j, _ := fun j => congrFun h2 j
    simp only [Pi.neg_apply, vmul_apply] at E0 E1 E2
    first
    | (left; apply Units.ext; ext i j; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)
    | (right; apply Units.ext; ext i j; rw [Units.val_neg, Matrix.neg_apply]; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)

theorem sep_family : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  intro N _
  classical
  let u : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N) → (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun p e τ => wp N (vmul e p.1) τ - wp N (vmul e p.2) τ
  let S : Set ℕ := ⋃ p : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N),
    {n : ℕ | ¬ (∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0) ∧
      ∀ τ, u p ![1, 0] τ + (n : ℂ) * u p ![0, 1] τ + (n : ℂ) ^ 2 * u p ![1, 1] τ = 0}
  have hfin : Finite (GL (Fin 2) (ZMod N)) :=
    Finite.of_injective (fun a : GL (Fin 2) (ZMod N) => (a : Matrix (Fin 2) (Fin 2) (ZMod N))) fun a b h => Units.ext h
  have hS : S.Finite := by
    refine Set.finite_iUnion fun p => ?_
    by_cases hz : ∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0
    · exact Set.finite_empty.subset fun n hn => absurd hz hn.1
    · obtain ⟨τ, hτ⟩ := not_forall.mp hz
      exact (finite_nat_roots _ _ _ hτ).subset fun n hn => hn.2 τ
  obtain ⟨n, hn⟩ := hS.infinite_compl.nonempty
  refine ⟨n, n ^ 2, fun α β hfun => ?_⟩
  have hroot : ∀ τ, u (α, β) ![1, 0] τ + (n : ℂ) * u (α, β) ![0, 1] τ + (n : ℂ) ^ 2 * u (α, β) ![1, 1] τ = 0 := by
    intro τ
    have := congrFun hfun τ
    push_cast at this
    simp only [u]
    linear_combination this
  have hz : ∀ τ, u (α, β) ![1, 0] τ = 0 ∧ u (α, β) ![0, 1] τ = 0 ∧ u (α, β) ![1, 1] τ = 0 := by
    by_contra hz
    exact hn (Set.mem_iUnion.mpr ⟨(α, β), hz, hroot⟩)
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    obtain ⟨z0, z1, z2⟩ := hz UpperHalfPlane.I
    have ne0 : (![1, 0] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have ne1 : (![0, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 1; simp at this
    have ne2 : (![1, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    exact eq_or_eq_neg_of_rows α β
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne0) (vmul_ne_zero _ β ne0) (sub_eq_zero.mp z0))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne1) (vmul_ne_zero _ β ne1) (sub_eq_zero.mp z1))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne2) (vmul_ne_zero _ β ne2) (sub_eq_zero.mp z2))
  · have h1 : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    subst h1
    left
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _

end GlobalTheory.FNSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZModStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  first | exact @GlobalTheory.FNSep.sep_family | exact GlobalTheory.FNSep.sep_family | (intros; apply GlobalTheory.FNSep.sep_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNConj

theorem slash_neg_one_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = f := by
  ext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = (-1) * UpperHalfPlane.denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    simp [UpperHalfPlane.denom]
  rw [this, mul_zpow, (hk.neg).neg_one_zpow]
  simp [UpperHalfPlane.denom]

theorem redGL_neg_one (N : ℕ) : redGL N (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, Matrix.SpecialLinearGroup.coe_neg]

theorem redGL_gamma (N : ℕ) (γ : SL(2, ℤ)) (h : γ ∈ CongruenceSubgroup.Gamma N) : redGL N γ = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, h00, h01, h10, h11]

end GlobalTheory.FNConj

namespace GlobalTheory.FNConj

theorem main : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k →
    (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) →
    ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  intro g N _ d k f hg hk hinv hq
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hvact, hgact, hvass, -, -, -, -, -, -⟩ := GlobalTheory.WpFam.Act.rightActions N
  obtain ⟨c₁, c₂, hsep⟩ := GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod N
  obtain ⟨-, hadd, hsmul, -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N 1)
  obtain ⟨-, hadd', hsmul', -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N (dg d))
  obtain ⟨qc, qadd, -, qmul, -⟩ := GlobalTheory.QFam.qConj_ring g N hN

  set t : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ +
    (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ with ht
  set t' : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α => t (α * dg d) with ht'
  have hw : ∀ e : Fin 2 → ZMod N, IsFam (gact N 1) 2 (fun α => wp N (vmul e α)) := fun e => by
    have := (GlobalTheory.WpFamGL.main N 1 e).1
    simpa only [mul_one] using this
  have hw' : ∀ e : Fin 2 → ZMod N, IsFam (gact N (dg d)) 2 (fun α => wp N (vmul e (α * dg d))) := fun e =>
    (GlobalTheory.WpFamGL.main N (dg d) e).1
  have htF : IsFam (gact N 1) 2 t :=
    (hadd _ _ _ (hadd _ _ _ (hw _) (hsmul _ _ _ (hw _))).1 (hsmul _ _ _ (hw _))).1
  have htF' : IsFam (gact N (dg d)) 2 t' :=
    (hadd' _ _ _ (hadd' _ _ _ (hw' _) (hsmul' _ _ _ (hw' _))).1 (hsmul' _ _ _ (hw' _))).1
  have hqw : ∀ (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (wp N (vmul e α)) (wp N (vmul e (α * dg d))) := fun e α => by
    rw [← hvass]
    exact (GlobalTheory.WpFam.ConjExp.qConj_torsion N g d hg (vmul e α)).1
  have hqn : ∀ (c : ℕ) (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (fun τ => (c : ℂ) * wp N (vmul e α) τ) (fun τ => (c : ℂ) * wp N (vmul e (α * dg d)) τ) := by
    intro c e α
    have := qmul _ _ _ _ (qc (c : ℂ)) (hqw e α)
    simpa only [map_natCast] using this
  have htq : ∀ α, QConj g N (t α) (t' α) := fun α =>
    qadd _ _ _ _ (qadd _ _ _ _ (hqw _ α) (hqn c₁ _ α)) (hqn c₂ _ α)

  obtain ⟨F, hF, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N (k : ℤ) f hinv
  have hFneg : ∀ α, F (-α) = F α := fun α => by
    have h1 := hF α (-1)
    rw [slash_neg_one_even (by exact_mod_cast hk.natCast) (F α)] at h1
    rw [h1, gact_one, redGL_neg_one, mul_neg_one]
  have hsepF : ∀ i j, t i = t j → F i = F j := fun i j h => by
    rcases hsep i j h with rfl | rfl
    · rfl
    · exact hFneg j
  have hFq : ∀ i, ∃ a, HasQ N (F i) a := fun i => by
    rcases hF0 i with ⟨γ, rfl⟩ | h0
    · rw [hFγ]; exact hq γ
    · refine ⟨fun _ => 0, fun τ => ?_⟩
      rw [h0]; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  obtain ⟨F', hF', hFF'⟩ := GlobalTheory.T.conjugate_modularFamily_along_separatingFamily g (GL (Fin 2) (ZMod N)) (gact N 1) (gact N (dg d)) 2 k N t t' F hN
    (IsRAct.actBij (hgact 1)) (IsRAct.actBij (hgact (dg d))) htF htF' hF hsepF htq hFq
  have hslash : ∀ γ : SL(2, ℤ), F' 1 ∣[(k : ℤ)] γ = F' (dg d * redGL N γ * (dg d)⁻¹) := fun γ => by
    rw [hF' 1 γ, gact, one_mul]
  refine ⟨F' 1, fun γ hγ => ?_, fun γ γ' hγγ' => ?_⟩
  · rw [hslash, redGL_gamma N γ hγ, mul_one, mul_inv_cancel]
  · rw [hslash, hγγ', mul_inv_cancel_right, ← hFγ]
    exact hFF' _

end GlobalTheory.FNConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraReciprocity_conjugate_form_level : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k → (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) → ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  first | exact @GlobalTheory.FNConj.main | exact GlobalTheory.FNConj.main | (intros; apply GlobalTheory.FNConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelN_function_galois_conj_qExpansion : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ), (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  first | exact @GlobalTheory.FN.lv_galois_conj | exact GlobalTheory.FN.lv_galois_conj | (intros; apply GlobalTheory.FN.lv_galois_conj <;> assumption)
end
