module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardHomQZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.HomKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.AlgebraMapSignedInvolutionQuotientDetMemSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detint

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsPadicIntLiftOfIntegralAt
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_padicInt_lift_of_integralAt :
    ∀ {Γ : Type} [CommGroup Γ] [Finite Γ] (l : ℕ) [Fact l.Prime] (y : MonoidAlgebra ℚ Γ), IntAt l 0 y → ∃ Yp : MonoidAlgebra ℤ_[l] Γ, MonoidAlgebra.mapRingHom Γ (algebraMap ℤ_[l] ℚ_[l]) Yp = MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) y := by
  intro Γ _ _ l _ y hy
  have hle : ∀ g : Γ, ‖((y.coeff g : ℚ) : ℚ_[l])‖ ≤ 1 := by
    intro g
    have h := hy g
    rw [pow_zero, div_one, mem_Zl] at h
    exact Padic.norm_rat_le_one h
  let x : Γ → ℤ_[l] := fun g => ⟨((y.coeff g : ℚ) : ℚ_[l]), hle g⟩
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]
  change algebraMap ℤ_[l] ℚ_[l] ((Finsupp.equivFunOnFinite.symm x) g) = _
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.TwistedBernoulliValueCongrPowMulFirst
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerCarrySpecAndWeightOneCoeffOfOdd
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerCarry_spec_and_weightOne_coeff_of_odd :
    ∀ (M a : ℕ) [NeZero M], a.Coprime M → ∀ b : ZMod M,
      (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b ∧ (Odd a → Eva M 1 a b = (Eone M a b : ℚ)) := by
  intro M a _ hcop b
  have hM : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, yCl, ← mul_assoc,
      ZMod.coe_mul_inv_eq_one a hcop, one_mul, sub_self]
  have h1 : (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b := by
    rw [jv, Int.mul_ediv_cancel' hM]
    ring
  refine ⟨h1, fun hodd => ?_⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h1q : (a : ℚ) * ((yCl a b).val : ℚ) = (b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ) := by
    exact_mod_cast h1
  obtain ⟨t, ht⟩ := hodd
  have hE : (Eone M a b : ℚ) = (t : ℚ) - (jv M a b : ℚ) := by
    rw [Eone]
    have : (((a : ℤ) - 1) / 2) = t := by omega
    rw [this]
    push_cast
    rfl
  rw [hE, Eva, Ev, Ev, bcoef, bcoef, Polynomial.bernoulli_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_one, sub_self,
    zpow_zero, one_mul, div_one, pow_one]
  have ha : (a : ℚ) ≠ 0 := by
    rw [ht]
    push_cast
    positivity
  have hy : ((yCl a b).val : ℚ) = ((b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ)) / (a : ℚ) := by
    field_simp
    linarith [h1q]
  rw [hy]
  have hta : (a : ℚ) = 2 * t + 1 := by exact_mod_cast ht
  field_simp
  rw [hta]
  ring
end

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.twistedBernoulliValue_congr_pow_mul_first :
    ∀ (M a e : ℕ) [NeZero M], a.Coprime M → Odd a → ∀ b : ZMod M, ∃ z : ℤ,
      Eva M (e + 1) a b = (((b.val : ℤ) ^ e * Eone M a b : ℤ) : ℚ) + (M : ℚ) / (dk (e + 1) : ℚ) * z := by
  intro M a e _ ha ho b
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  have h1 := (stickelbergerCarry_spec_and_weightOne_coeff_of_odd M a ha b).1
  obtain ⟨z1, hz1⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e b.val hM0
  obtain ⟨z2, hz2⟩ := stickelbergerBernoulliCoeff_expansion_mod_denominator M e (yCl a b).val hM0
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := exists_binomial_expansion_mod_sq (b.val : ℤ) (jv M a b) M e
  rw [← h1, mul_pow] at hz3 hw
  obtain ⟨c, hc⟩ := ho
  have h2 : ((a : ℤ) - 1) / 2 = c := by omega
  have h4 : (a : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  have h6 : (c : ℚ) = ((a : ℚ) - 1) / 2 := by rw [h4]; ring
  have q3 : (a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1) =
      (b.val : ℚ) ^ (e + 1) + ((e : ℚ) + 1) * (b.val : ℚ) ^ e * ((M : ℚ) * (jv M a b : ℚ)) + (M : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e = (b.val : ℚ) ^ e + (M : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [dk]; push_cast; ring
  refine ⟨2 * z1 - 2 * (a : ℤ) ^ (e + 1) * z2 - 2 * (primorial (e + 1 + 1) : ℤ) * z3
    + ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * a * w, ?_⟩
  rw [Eva, Ev, Ev, hz1, hz2, Eone, h2, hdk]
  push_cast
  rw [h6]
  have e1 : ∀ R : ℚ, (a : ℚ) ^ (e + 1) * (((yCl a b).val : ℚ) ^ (e + 1) / (((e : ℚ) + 1) * M) -
      ((yCl a b).val : ℚ) ^ e / 2 + R) =
      ((a : ℚ) ^ (e + 1) * ((yCl a b).val : ℚ) ^ (e + 1)) / (((e : ℚ) + 1) * M) -
        a * ((a : ℚ) ^ e * ((yCl a b).val : ℚ) ^ e) / 2 + (a : ℚ) ^ (e + 1) * R := by
    intro R; ring
  rw [e1, q3, qw]
  field_simp
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.GroupRingIntAtDivSmulOfPadicValNatLe
open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.groupRing_intAt_div_smul_of_padicValNat_le :
    ∀ (l : ℕ) [Fact l.Prime] (M D t : ℕ), 0 < M → 0 < D → t + padicValNat l D ≤ padicValNat l M →
      ∀ (Γ : Type) [CommGroup Γ] (z : MonoidAlgebra ℤ Γ), B4.IntAt l t (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z) := by
  intro l _ M D t hM hD ht Γ _ z g
  have hp : l.Prime := Fact.out
  have hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ) := by
    simp [Stk.cf]
  rw [hcoef]
  have hdvdM : l ^ (padicValNat l D + t) ∣ M :=
    (pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hdvdD : l ^ padicValNat l D ∣ D := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  obtain ⟨k, hk⟩ := hdvdM
  obtain ⟨E, hE⟩ := hdvdD
  have hnd : ¬ l ∣ E := by
    intro hl
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    conv_rhs => rw [hE]
    rw [pow_succ]
    simpa only [Nat.padicValNat_def] using Nat.mul_dvd_mul_left (l ^ padicValNat l D) hl
  have hE0 : E ≠ 0 := by
    rintro rfl
    simp at hE
    omega
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE0
  have hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k := by exact_mod_cast hk
  have hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E := by exact_mod_cast hE
  have heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ) := by
    rw [hMq, hDq, pow_add]
    field_simp
  rw [heq]
  refine (B4.Zl l).mul_mem ?_ (intCast_mem _ _)
  rw [B4.mem_Zl]
  intro hden
  apply hnd
  have h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E := by
    rw [← Rat.divInt_eq_div]
    exact_mod_cast Rat.den_dvd (k : ℤ) (E : ℤ)
  push_cast at h1
  exact hden.trans h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bridge
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SingleInvMulGroupRingSumOverUnitsInv
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.single_inv_mul_groupRingSumOverUnitsInv :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (R Γ : Type) [CommRing R] [Group Γ] (φ : (ZMod M)ˣ →* Γ) (c : R)
      (f : ZMod M → R),
      MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ c * sumEl φ f = sumEl φ fun b => c * f (yCl a b) := by
  intro M a _ ha R Γ _ _ φ c f
  unfold sumEl yCl
  rw [Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M) := by
    rw [mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]
  rw [MonoidAlgebra.single_mul_single]
  simp only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]
end

open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.twistedStickelbergerElements_agree :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (Γ : Type) [CommGroup Γ] (φ : (ZMod M)ˣ →* Γ) (k : ℕ),
      B4.yEl k a ha φ = Stk.yForm k a φ ∧ B4.ytEl k a φ = Stk.ytEl k a φ ∧ B4.xEl a φ = Stk.xEl a φ ∧
      B4.coefMap ℚ Γ = Stk.cf ℚ Γ := by
  intro M a _ ha Γ _ φ k
  refine ⟨?_, rfl, rfl, ?_⟩
  · have e : B4.sumEl φ (B4.Ek M k) = Stk.sumEl φ (Stk.Ev M k) := rfl
    have hneg : ∀ f : ZMod M → ℚ, (Stk.sumEl φ fun b => -f b) = -Stk.sumEl φ f := by
      intro f
      simp [Stk.sumEl, Finset.sum_neg_distrib]
    have hE : Stk.Eva M k a =
        fun b => Stk.Ev M k b + -((a : ℚ) ^ k * Stk.Ev M k (Stk.yCl a b)) := by
      funext b
      simp [Stk.Eva, sub_eq_add_neg]
    simp only [B4.yEl, B4.thetaEl]
    rw [e, sub_mul, one_mul, mul_neg, Stk.single_inv_mul_groupRingSumOverUnitsInv, Stk.yForm, hE, Stk.sumEl_add, hneg]
    abel
  · apply MonoidAlgebra.ringHom_ext
    · intro n
      simp [B4.coefMap_single]
    · intro g
      simp [B4.coefMap_single]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZKill
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ResKill
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.resKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℕ) (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ a : ℕ, Odd a → a.Coprime (N * l) → ∀ x ∈ Sha D (e : ℤ), ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D (e : ℤ) ((actRep D (e : ℤ) ρ).asAlgebraHom (coefMap ℤ_[l] (Gq ρ) (ytEl e a ((piQ ρ)⁻¹.comp (ZMod.unitsMap h)))) x) u = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ ρ hρ a ha hac x hx
  obtain ⟨r, hr⟩ := (Z1_H1_qz_twist_l_power_torsion E Ω l D (e : ℤ)).2 x
  have hφ : resInf D (e : ℤ) x ∈ XDual l (cycU l (⊤ : Subgroup (G E Ω))) ℤ_[l] (QZ l) :=
    (Submodule.mem_inf.1 (resInfMem E Ω l D (e : ℤ) ⟨x, hx, rfl⟩)).1
  have hcl : IsClosed ((⊤ : Subgroup (G E Ω)) : Set (G E Ω)) := by
    rw [Subgroup.coe_top]
    exact isClosed_univ
  obtain ⟨n, ψ, hψ, hres⟩ := xdualExt E Ω l l ⊤ ℤ_[l] (QZ l) (Fact.out : l.Prime).ne_zero hcl _ hφ
  refine ⟨max n r + 2, fun m hm M _ h hM u hu => ?_⟩
  have key : ∀ b : (ZMod M)ˣ, (actRep D (↑e) ρ).asAlgebraHom (((MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ_[l] (Gq ρ)) (Gq ρ)) (MonoidAlgebra.of ℤ_[l] (Gq ρ))).toRingHom (MonoidAlgebra.single (((piQ ρ)⁻¹.comp (ZMod.unitsMap h)) b)⁻¹ (↑(↑b : ZMod M).val ^ e * Eone M a ↑b))) = (((↑(↑b : ZMod M).val ^ e * Eone M a ↑b : ℤ) : ℤ_[l])) • galoisActionOnCohomology D (↑e) (ρ (ZMod.unitsMap h b)).toRingEquiv := by
    intro b
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply, MonoidHom.inv_apply, inv_inv, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, map_zsmul]
    rw [Representation.asAlgebraHom_single, zsmul_eq_mul, mul_one]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ytEl, sumEl, map_neg, map_sum, coefMap, key]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.neg_apply, map_neg, Pi.neg_apply, neg_eq_zero, LinearMap.sum_apply, map_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply]
  have hm2 : 2 ≤ m := le_trans (Nat.le_add_left 2 _) hm
  have hnm : n ≤ m := le_trans (le_trans (le_max_left n r) (Nat.le_add_right _ 2)) hm
  have hrm : r ≤ m := le_trans (le_trans (le_max_right n r) (Nat.le_add_right _ 2)) hm
  choose σ hσ using (liftEx E Ω M).1
  have hcycM : IsCycAct Ω M (ρ.comp (ZMod.unitsMap h)) := (actFacts E Ω N ρ hρ).2.2.2.2 M h
  have hlift : ∀ b : (ZMod M)ˣ, IsLift (ρ (ZMod.unitsMap h b)).toRingEquiv (σ b) := fun b => hcycM b (σ b) (hσ b)
  have hfixM : u.1 ∈ fixMu E Ω M := by
    rw [hM]
    exact (fixLev E Ω l N m).2.1 (Subgroup.mem_inf.2 ⟨u.2, hu⟩)
  let w : (ZMod M)ˣ → G E Ω := fun b =>
    AlgEquiv.ofRingEquiv (f := ((σ b).trans (u.1 : Ω ≃ₐ[E] Ω).toRingEquiv).trans (σ b).symm) (by
      intro y
      have h1 := hlift b y
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv]
      rw [h1, AlgEquiv.commutes, ← h1, RingEquiv.symm_apply_apply])
  have hw : ∀ b y, w b y = (σ b).symm (u.1 (σ b y)) := fun _ _ => rfl
  have wInf : ∀ b, w b ∈ Uinf E Ω l := by
    intro b
    have hu1 : cycZ E Ω l u.1 = 1 := (Subgroup.mem_inf.1 u.2).2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    show cycZ E Ω l (w b) = 1
    have hra : MulSemiringAction.toRingAut (G E Ω) Ω (w b) = (σ b)⁻¹ * MulSemiringAction.toRingAut (G E Ω) Ω u.1 * σ b := by
      ext y
      rfl
    have hcz : ∀ g : G E Ω, cycZ E Ω l g = cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) := fun _ => rfl
    rw [hcz, hra, map_mul, map_mul, map_inv, ← hcz, hu1, mul_one, inv_mul_cancel]
  have wFix : ∀ b, w b ∈ fixMu E Ω M := by
    intro b y hy
    have hy' : (σ b y) ^ M = 1 := by rw [← map_pow, hy, map_one]
    rw [hw, hfixM _ hy', RingEquiv.symm_apply_apply]
  have hconj : ∀ b, resInf D (e : ℤ) (galoisActionOnCohomology D (e : ℤ) (ρ (ZMod.unitsMap h b)).toRingEquiv x) u = twScal l (σ b) (e : ℤ) • resInf D (e : ℤ) x ⟨w b, wInf b⟩ := fun b =>
    resInfConj E Ω l D (e : ℤ) _ (σ b) (hlift b) x ⟨w b, wInf b⟩ u (fun y => by
      show u.1 (σ b y) = σ b (w b y)
      rw [hw, RingEquiv.apply_symm_apply])
  have hle : fixMu E Ω M ≤ levU l ⊤ n := by
    intro g hg
    show g ∈ Un E Ω l n
    rw [← (fixLev E Ω l N n).1]
    intro y hy
    apply hg
    obtain ⟨k, hk⟩ : l ^ n ∣ M := by
      rw [hM]
      exact dvd_mul_of_dvd_right (pow_dvd_pow l hnm) N
    rw [hk, pow_mul, hy, one_pow]
  have hφ' : restr ℤ_[l] (QZ l) hle ψ ∈ XDual l (fixMu E Ω M) ℤ_[l] (QZ l) :=
    (restrMem E Ω l (fixMu E Ω M) (levU l ⊤ n) hle ℤ_[l] (QZ l) (qzG E Ω l (e : ℤ))).1 ⟨ψ, hψ, rfl⟩
  have h2M : 2 < M := by
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have h4 : 4 ≤ l ^ 2 := by nlinarith [pow_two l]
    have h4m : 4 ≤ l ^ m := le_trans h4 (Nat.pow_le_pow_right (by omega) hm2)
    have hN : 1 ≤ N := NeZero.one_le
    rw [hM]
    nlinarith
  have hacM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right hac.coprime_mul_right_right (Nat.Coprime.pow_right m hac.coprime_mul_left_right)
  have hK := homKill E Ω M (ρ.comp (ZMod.unitsMap h)) hcycM h2M a ha hacM ℤ_[l] (QZ l) l _ hφ' σ hσ ⟨u.1, hfixM⟩ (fun b => ⟨w b, wFix b⟩) (fun b y => by
    show u.1 (σ b y) = σ b (w b y)
    rw [hw, RingEquiv.apply_symm_apply])
  have hv : ∀ g, (l : ℤ_[l]) ^ m • resInf D (e : ℤ) x g = 0 := by
    intro g
    have h0 : (l : ℤ_[l]) ^ r • resInf D (e : ℤ) x = 0 := by rw [← map_smul, hr, map_zero]
    rw [← Nat.sub_add_cancel hrm, pow_add, mul_smul]
    have h1 := congrFun h0 g
    simp only [Pi.smul_apply, Pi.zero_apply] at h1
    rw [h1, smul_zero]
  have alg : ∀ (c E1 : ℤ) (B : ℤ_[l]) (X : ℤ_[l]ˣ) (v : QZ l), (c : ℤ_[l]) = B ^ e * (E1 : ℤ_[l]) → (l : ℤ_[l]) ^ m ∣ (X : ℤ_[l]) - B → (l : ℤ_[l]) ^ m • v = 0 → (c : ℤ_[l]) • (((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • v) = E1 • v := by
    intro c E1 B X v hc hX hv0
    obtain ⟨t, ht⟩ : (l : ℤ_[l]) ^ m ∣ B ^ e - (X : ℤ_[l]) ^ e := dvd_trans (dvd_sub_comm.1 hX) (sub_dvd_pow_sub_pow _ _ _)
    have hX' : ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (X : ℤ_[l]) ^ e = 1 := by
      rw [zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.inv_mul]
    have hB : B ^ e = (X : ℤ_[l]) ^ e + (l : ℤ_[l]) ^ m * t := by rw [← ht]; ring
    have h3 : B ^ e * (E1 : ℤ_[l]) * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) = (E1 : ℤ_[l]) + ((E1 : ℤ_[l]) * t * ((X ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) * (l : ℤ_[l]) ^ m := by
      rw [hB]
      linear_combination (E1 : ℤ_[l]) * hX'
    rw [smul_smul, hc, h3, add_smul, mul_smul, hv0, smul_zero, add_zero, Int.cast_smul_eq_zsmul]
  rw [← hK]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hφeq : restr ℤ_[l] (QZ l) hle ψ ⟨w b, wFix b⟩ = resInf D (e : ℤ) x ⟨w b, wInf b⟩ := by
    rw [← hres]
    rfl
  rw [hconj b, hφeq]
  exact alg _ _ _ _ _ (by push_cast; ring) ((fixLev E Ω l N m).2.2 M b (σ b) (by rw [hM]; exact dvd_mul_left _ _) (hσ b)) (hv _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.NearLevel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YNear
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.yNear :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a r : ℕ) (ha : a.Coprime N), Odd a → l ^ (r + ck l (e + 1) + 1) ∣ N → IntAt l r (yEl (e + 1) a ha φ - coefMap ℚ Γ (ytEl e a φ)) := by
  intro l _ Γ _ _ N _ φ e a r ha hodd hdvd
  have hy := (Stk.twistedStickelbergerElements_agree N a ha Γ φ (e + 1)).1
  have hyt := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.1
  have hcf := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.2.2
  choose z hz using Stk.twistedBernoulliValue_congr_pow_mul_first N a e ha hodd
  rw [hy, hyt, hcf]
  have key : Stk.yForm (e + 1) a φ - Stk.cf ℚ Γ (Stk.ytEl e a φ)
      = ((N : ℚ) / (Stk.dk (e + 1) : ℚ)) • Stk.cf ℚ Γ (Stk.sumEl φ (fun b => -z b)) := by
    rw [Stk.cf_sumEl]
    unfold Stk.yForm Stk.ytEl
    rw [map_neg, Stk.cf_sumEl]
    unfold Stk.sumEl
    rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hz _, MonoidAlgebra.smul_single]
    first
      | rw [← MonoidAlgebra.single_sub]
      | erw [← Finsupp.single_sub]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hN0 : N ≠ 0 := NeZero.ne N
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN0).mp hdvd
  apply Stk.groupRing_intAt_div_smul_of_padicValNat_le l N (Stk.dk (e + 1)) r (Nat.pos_of_ne_zero hN0) (Stk.dk_pos (Nat.succ_pos e))
  have hck : ck l (e + 1) = padicValNat l (Stk.dk (e + 1)) := rfl
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YLevel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem fib_iff {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (b' : (ZMod M)ˣ) (b : (ZMod N)ˣ) :
    ZMod.unitsMap h b' = b ↔ (b' : ZMod M).val % N = (b : ZMod N).val := by
  rw [Units.ext_iff, ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ← (ZMod.val_injective N).eq_iff, ZMod.val_natCast]

private theorem fib_sum {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (f : ℕ → ℚ) (b : (ZMod N)ˣ) :
    ∑ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b), f (b' : ZMod M).val
      = ∑ j ∈ Finset.range L, f ((b : ZMod N).val + j * N) := by
  have hN : 0 < N := NeZero.pos N
  have hbN : (b : ZMod N).val < N := ZMod.val_lt _
  have hcop : ∀ n : ℕ, ((b : ZMod N).val + n * N).Coprime M := fun n =>
    hc _ (by simpa using ZMod.val_coe_unit_coprime b)
  have hlt : ∀ n ∈ Finset.range L, (b : ZMod N).val + n * N < M := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [hM]
    nlinarith
  symm
  refine Finset.sum_nbij' (fun n => ZMod.unitOfCoprime _ (hcop n)) (fun b' => (b' : ZMod M).val / N)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [fib_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbN]
  · intro b' _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hN, mul_comm, ← hM]
    exact ZMod.val_lt _
  · intro n hn
    simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (hlt n hn), Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hbN, zero_add]
  · intro b' hb'
    rw [Finset.mem_filter, fib_iff] at hb'
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← hb'.2, Nat.mod_add_div', ZMod.natCast_zmod_val]
  · intro n hn
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt n hn)]

private theorem sum_single_eq_single_sum {Γ : Type} [CommGroup Γ] {ι : Type} (s : Finset ι) (g : Γ) (F : ι → ℚ) :
    ∑ x ∈ s, MonoidAlgebra.single g (F x) = MonoidAlgebra.single g (∑ x ∈ s, F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, Finset.sum_insert ha, MonoidAlgebra.single_add]

private theorem theta_level {Γ : Type} [CommGroup Γ] {N L M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (hM : M = N * L)
    (hc : ∀ n : ℕ, n.Coprime N → n.Coprime M) (φ : (ZMod N)ˣ →* Γ) (k : ℕ) :
    thetaEl k (φ.comp (ZMod.unitsMap h)) = thetaEl k φ := by
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · exact absurd (hM.trans (by rw [hL, mul_zero])) (NeZero.ne M)
    · exact hL
  unfold thetaEl sumEl
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ (ZMod.unitsMap h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfib : ∀ b' ∈ Finset.univ.filter (fun b' : (ZMod M)ˣ => ZMod.unitsMap h b' = b),
      MonoidAlgebra.single ((φ.comp (ZMod.unitsMap h)) b')⁻¹ (Ek M k (b' : ZMod M))
        = MonoidAlgebra.single (φ b)⁻¹ (Ek M k (b' : ZMod M)) := by
    intro b' hb'
    rw [Finset.mem_filter] at hb'
    rw [MonoidHom.comp_apply, hb'.2]
  rw [Finset.sum_congr rfl hfib, sum_single_eq_single_sum]
  congr 1
  unfold Ek
  rw [← Finset.sum_div, fib_sum h hM hc (fun n => bcoef M k n) b, hM,
    b_raabe N L k _ (NeZero.pos N) hLpos]

theorem UpperTheory.V.Odd.yLevel :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (k a : ℕ) (ha : a.Coprime N), 1 ≤ k → l ∣ N → ∀ (m M : ℕ) [NeZero M] (h : N ∣ M) (ha' : a.Coprime M), M = N * l ^ m → yEl k a ha' (φ.comp (ZMod.unitsMap h)) = yEl k a ha φ := by
  intro l _ Γ _ _ N _ φ k a ha hk hl m M _ h ha' hM
  have hc : ∀ n : ℕ, n.Coprime N → n.Coprime M := by
    intro n hn
    rw [hM]
    exact hn.mul_right ((Nat.Coprime.coprime_dvd_right hl hn).pow_right m)
  unfold yEl
  rw [theta_level h hM hc φ k]
  congr 4
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.coe_unitOfCoprime]
  exact ZMod.cast_natCast h a
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem near_level (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N]
    (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N) (ho : Odd a) (hl : l ∣ N) (r m : ℕ)
    (hm : r + ck l (e + 1) + 1 ≤ m) (M : ℕ) [NeZero M] (h : N ∣ M) (hM : M = N * l ^ m) (g : Γ) :
    InPow l r ((yEl (e + 1) a ha φ).coeff g - (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℚ)) := by
  have haN : a.Coprime l := Nat.Coprime.coprime_dvd_right hl ha
  have haM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right ha (Nat.Coprime.pow_right m haN)
  have hdiv : l ^ (r + ck l (e + 1) + 1) ∣ M := by
    rw [hM]
    exact Dvd.dvd.mul_left (pow_dvd_pow l hm) N
  have hI := yNear l Γ M (φ.comp (ZMod.unitsMap h)) e a r haM ho hdiv
  rw [yLevel l Γ N φ (e + 1) a ha (by omega) hl m M h haM hM] at hI
  have := (intAt_iff l r _).mp hI g
  simpa [coeff_coefMap] using this

theorem UpperTheory.V.Odd.congr :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Odd a → l ∣ N → ∃ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) ∧ ∀ r : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∃ w : MonoidAlgebra ℤ_[l] Γ, coefMap ℤ_[l] Γ (ytEl e a (φ.comp (ZMod.unitsMap h))) = z + (l : ℤ_[l]) ^ r • w := by
  intro l _ Γ _ _ N _ φ e a ha ho hl
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set y := yEl (e + 1) a ha φ with hy
  have hy0 : IntAt l 0 y := by
    rw [intAt_iff]
    intro g
    haveI : NeZero (N * l ^ (ck l (e + 1) + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)⟩
    have hn := near_level l Γ N φ e a ha ho hl 0 (ck l (e + 1) + 1) (by omega)
      (N * l ^ (ck l (e + 1) + 1)) (dvd_mul_right _ _) rfl g
    have h1 := hn.mem
    have h2 := add_mem h1 (intCast_mem (Zl l) ((ytEl e a (φ.comp (ZMod.unitsMap
      (dvd_mul_right N (l ^ (ck l (e + 1) + 1)))))).coeff g))
    rw [sub_add_cancel] at h2
    show y.coeff g / (l : ℚ) ^ 0 ∈ Zl l
    simpa using h2
  obtain ⟨Yp, hYp⟩ := exists_padicInt_lift_of_integralAt l y hy0
  have hYg : ∀ g, ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l]) := by
    intro g
    have := congrArg (fun x => x.coeff g) hYp
    simpa using this
  refine ⟨Yp, hYg, ?_⟩
  intro r
  refine ⟨r + ck l (e + 1) + 1, ?_⟩
  intro m hm M _ h hM
  have hc : ∀ g, ∃ c : ℤ_[l], (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℤ_[l]) =
      Yp.coeff g + (l : ℤ_[l]) ^ r * c := by
    intro g
    have hn := near_level l Γ N φ e a ha ho hl r m hm M h hM g
    set t : ℤ := (ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g
    set q : ℚ := (y.coeff g - (t : ℚ)) / (l : ℚ) ^ r with hqdef
    have hq : ‖(q : ℚ_[l])‖ ≤ 1 := Padic.norm_rat_le_one (mem_Zl.mp hn)
    have hqr : q * (l : ℚ) ^ r = y.coeff g - t := by
      rw [hqdef]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0))
    have hqr' : (q : ℚ_[l]) * (l : ℚ_[l]) ^ r = ((y.coeff g : ℚ) : ℚ_[l]) - (t : ℚ_[l]) := by
      have := congrArg (fun x : ℚ => (x : ℚ_[l])) hqr
      push_cast at this
      exact this
    let c : ℤ_[l] := ⟨(q : ℚ_[l]), hq⟩
    refine ⟨-c, ?_⟩
    apply Subtype.ext
    show (t : ℚ_[l]) = ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) + (l : ℚ_[l]) ^ r * -(q : ℚ_[l])
    rw [hYg g]
    linear_combination hqr'
  choose c hc using hc
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, coeff_coefMap, hc g]
  simp [smul_eq_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.TotKill
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_tot_mem (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : ℕ) [NeZero N] (g : G E Ω) : g ^ N.totient ∈ fixMu E Ω N := by
  obtain ⟨b, hb⟩ := (liftEx E Ω N).2 g.toRingEquiv
  intro x hx
  have h : ∀ k : ℕ, (g ^ k) x = x ^ ((b : ZMod N).val ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, pow_succ', pow_mul]
      congr 1
      exact hb x hx
  rw [h, pow_eq_pow_mod _ hx, (Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime b) : _ % N = 1 % N),
    ← pow_eq_pow_mod _ hx, pow_one]

theorem UpperTheory.V.Odd.totKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (N : ℕ) [NeZero N], e ≠ 0 → Procyc E Ω l → ∀ x : H1 (qzTw D e), (∀ u : Uinf E Ω l, u.1 ∈ fixMu E Ω N → resInf D e x u = 0) → N.totient • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ he hP x hx
  have hadd : ∀ a b : Uinf E Ω l, resInf D e x (a * b) = resInf D e x a + resInf D e x b := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hchi : ∀ g : G E Ω, D.chi (toGS Ω _ g) = cycZ E Ω l g := fun g => DFunLike.congr_fun D.hchi g
    have htriv : ∀ g : G E Ω, cycZ E Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
      rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
    have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
    intro a b
    rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  have hpow : ∀ (u : Uinf E Ω l) (k : ℕ), resInf D e x (u ^ k) = k • resInf D e x u := by
    intro u k
    induction k with
    | zero =>
      have := hadd 1 1
      rw [one_mul] at this
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 this
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  apply resInfInj E Ω l D e he hP
  rw [map_nsmul, map_zero]
  funext u
  rw [Pi.smul_apply, ← hpow]
  exact hx _ (by rw [Subgroup.coe_pow]; exact pow_tot_mem E Ω N u.1)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.zKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℕ) (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → 1 ≤ e → Procyc E Ω l → l ∣ N → ∀ (a : ℕ) (ha : a.Coprime N), Odd a → ∃ z : MonoidAlgebra ℤ_[l] (Gq ρ), IsInt l z (yEl (e + 1) a ha (piQ ρ)⁻¹) ∧ ∀ x ∈ Sha D (e : ℤ), (actRep D (e : ℤ) ρ).asAlgebraHom z (N.totient • x) = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ ρ hcyc he hpro hlN a ha hodd
  obtain ⟨z, hz, hcong⟩ := Odd.congr l (Gq ρ) N (piQ ρ)⁻¹ e a ha hodd hlN
  refine ⟨z, hz, fun x hx => ?_⟩
  obtain ⟨r, hr⟩ := (Z1_H1_qz_twist_l_power_torsion E Ω l D (e : ℤ)).2 x
  obtain ⟨m₁, hm₁⟩ := hcong r
  have hal : a.Coprime (N * l) := Nat.Coprime.mul_right ha (Nat.Coprime.coprime_dvd_right hlN ha)
  obtain ⟨m₂, hm₂⟩ := resKill E Ω l D e N ρ hcyc a hodd hal x hx
  set m := max m₁ m₂
  haveI : NeZero (N * l ^ m) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hNM : N ∣ N * l ^ m := Dvd.intro _ rfl
  obtain ⟨w, hw⟩ := hm₁ m (le_max_left _ _) (N * l ^ m) hNM rfl
  have hres := hm₂ m (le_max_right _ _) (N * l ^ m) hNM rfl
  rw [hw] at hres
  have hzero : ((actRep D (e : ℤ) ρ).asAlgebraHom ((l : ℤ_[l]) ^ r • w)) x = 0 := by
    rw [map_smul, LinearMap.smul_apply, ← LinearMap.map_smul, hr, map_zero]
  have he0 : (e : ℤ) ≠ 0 := by omega
  have htot := totKill E Ω l D (e : ℤ) N he0 hpro (((actRep D (e : ℤ) ρ).asAlgebraHom z) x) (fun u hu => by
    have h1 := hres u hu
    rwa [map_add, LinearMap.add_apply, hzero, add_zero] at h1)
  rw [map_nsmul]
  exact htot
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.BdxLog
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem bdX_mul_le (M a k T : ℕ) (hT : 2 ≤ T) (hM : M ≤ T) (ha : a ≤ T ^ 3) (hk : k ≤ T) (hk2 : 2 ≤ k) :
    bdX M a k * M ≤ T ^ (10 * k) := by
  have hk1 : k + 1 ≤ T ^ 2 := by nlinarith
  have f1 : (k + 1).factorial ≤ (T ^ 2) ^ (k + 1) :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk1 _)
  have f2 : k.factorial ≤ T ^ k := (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk _)
  calc bdX M a k * M = M * k * (k + 1).factorial * (2 * a ^ k * M ^ k * k.factorial) * M := rfl
    _ ≤ T * T * (T ^ 2) ^ (k + 1) * (T * (T ^ 3) ^ k * T ^ k * T ^ k) * T := by gcongr
    _ = T ^ (7 * k + 6) := by ring
    _ ≤ T ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)

theorem UpperTheory.V.Odd.bdxLog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N l e : ℕ, 1 ≤ N → 2 ≤ l → 1 ≤ e → Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log ((N : ℝ) * l) ≤ C * (e + 1) * Real.log ((e : ℝ) * l * N) := by
  refine ⟨30, by norm_num, ?_⟩
  intro N l e hN hl he
  have h2 : e * 2 ≤ e * l := Nat.mul_le_mul_left e hl
  have h3 : e * l ≤ e * l * N := Nat.le_mul_of_pos_right _ hN
  have h4 : 1 * l * N ≤ e * l * N := by gcongr
  have h5 : N * l ≤ e * l * N := by nlinarith
  have hX2 : 2 ≤ e * l * N := by nlinarith
  have hT : 2 ≤ 3 * (e * l * N) := by omega
  have hM : N * l ≤ 3 * (e * l * N) := by omega
  have ha : 2 * (N * l) + 1 ≤ (3 * (e * l * N)) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hk : e + 1 ≤ 3 * (e * l * N) := by nlinarith
  have key := bdX_mul_le (N * l) (2 * (N * l) + 1) (e + 1) (3 * (e * l * N)) hT hM ha hk (by omega)
  have hNl : 0 < N * l := by positivity
  have hb : 0 < bdX (N * l) (2 * (N * l) + 1) (e + 1) := by
    unfold bdX denY sizeY
    positivity
  have hbpos : (0 : ℝ) < (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) := by exact_mod_cast hb
  have hMpos : (0 : ℝ) < (N : ℝ) * l := by exact_mod_cast hNl
  rw [← Real.log_mul hbpos.ne' hMpos.ne']
  have hcast : (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) * ((N : ℝ) * l)
      = ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  have hXr : (2 : ℝ) ≤ (e : ℝ) * l * N := by exact_mod_cast hX2
  have hlog2 : Real.log 2 ≤ Real.log ((e : ℝ) * l * N) := Real.log_le_log (by norm_num) hXr
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log (((3 * (e * l * N) : ℕ) : ℝ)) ≤ 3 * Real.log ((e : ℝ) * l * N) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hpos : (0 : ℝ) < ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hb hNl
  calc Real.log ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ)
      ≤ Real.log (((3 * (e * l * N)) ^ (10 * (e + 1)) : ℕ) : ℝ) :=
        Real.log_le_log hpos (by exact_mod_cast key)
    _ = (10 * (e + 1) : ℕ) * Real.log (((3 * (e * l * N) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
    _ ≤ (10 * (e + 1) : ℕ) * (3 * Real.log ((e : ℝ) * l * N)) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
    _ = 30 * ((e : ℝ) + 1) * Real.log ((e : ℝ) * l * N) := by push_cast; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DetVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem int_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X.natAbs ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hn' (dvd_zero l)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
  · have hu : IsUnit ((n' : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).mp h
    rw [Int.cast_natCast] at hu
    have h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l]) :=
      map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)
    refine h1.trans ?_
    rw [he]
    push_cast
    exact hu.mul_right_dvd.mpr dvd_rfl

theorem UpperTheory.V.Odd.detVal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Function.Surjective φ → φ (-1) ≠ 1 → 1 ≤ e → 1 < a → ∀ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) ∧ detR (φ (-1)) ((-1) ^ (e + 1)) z ∣ (l : ℤ_[l]) ^ r := by
  intro l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz
  obtain ⟨X, hX0, hXb, hXe⟩ := higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ
  obtain ⟨r, hr1, hr2⟩ := int_dvd_pow l X hX0
  refine ⟨r, ?_, ?_⟩
  · have h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2) := by
      exact_mod_cast hr1.trans hXb
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    have h2 := Real.log_le_log hl0 h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    calc (r : ℝ) * Real.log l ≤ ((Nat.card Γ / 2 : ℕ) : ℝ) * Real.log (bdX N a (e + 1)) := h2
      _ ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) :=
        mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg _)
  · refine dvd_trans ?_ hr2
    have hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z =
        MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ) := by
      ext g
      have h := hz g
      simp
      exact h
    have hd := congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap
    rw [detR_map, detR_map] at hd
    have hq := congrArg (Rat.castHom ℚ_[l]) hXe
    rw [map_mul, map_pow, ← hd] at hq
    have hX'' : (X : ℤ_[l]) =
        (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z := by
      apply PadicInt.ext
      push_cast
      simp at hq
      exact hq
    rw [hX'']
    exact dvd_mul_left _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AdjKill
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.adjKill :
    ∀ (A Γ X : Type) [CommRing A] [CommGroup Γ] [Finite Γ] [AddCommGroup X] [Module A X] (π : Representation A Γ X) (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ (z : MonoidAlgebra A Γ) (x : X), π c x = (ε : A) • x → π.asAlgebraHom z x = 0 → detR c ε z • x = 0 := by
  intro A Γ X _ _ _ _ _ π c ε hc hc1 hε z x hx hz
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (algebraMap_signedInvolutionQuotientDet_mem_span (A := A) c ε hc hc1 hε z)
  have hrel : π.asAlgebraHom (rel A c ε) x = 0 := by
    simp [rel, hx, Int.cast_smul_eq_zsmul]
  have key := congrArg (fun w => π.asAlgebraHom w x) hab
  simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem nat_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℕ) (h0 : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  have hdvd : l ^ padicValNat l X ∣ X := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  refine ⟨padicValNat l X, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) h0
    exact ⟨k, by rw [pow_succ, mul_assoc]; simpa [Nat.padicValNat_def] using hm⟩
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm0 (by simpa using h))
  have hX : (X : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l X * m := by
    conv_lhs => rw [hm]
    push_cast
    rfl
  rw [hX]
  simpa using mul_dvd_mul_left ((l : ℤ_[l]) ^ padicValNat l X) (hu.dvd (a := 1))

theorem UpperTheory.V.Odd.killPow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N) ∧ ∀ x ∈ ShaMinus D e, (l : ℤ_[l]) ^ r • x = 0 := by
  obtain ⟨C, hC0, hC⟩ := bdxLog
  refine ⟨C, hC0, ?_⟩
  intro E Ω _ _ _ _ _ _ N hN hcyc l _ D hproc e he
  haveI : NeZero N := ⟨hN.ne'⟩
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hM0 : N * l ≠ 0 := Nat.mul_ne_zero hN.ne' (by omega)
  haveI : NeZero (N * l) := ⟨hM0⟩
  obtain ⟨ρ0, hρ0⟩ := actEx E Ω N hcyc
  have hNM : N ∣ N * l := dvd_mul_right N l
  have hρ := (actFacts E Ω N ρ0 hρ0).2.2.2.2 (N * l) hNM
  set ρ := ρ0.comp (ZMod.unitsMap hNM) with hρdef
  obtain ⟨_, _, hcard, _, _⟩ := actFacts E Ω (N * l) ρ hρ
  obtain ⟨hconj, hne⟩ := actConj E Ω (N * l) ρ hρ
  have hlM : l ∣ N * l := dvd_mul_left l N
  have hcop : (2 * (N * l) + 1).Coprime (N * l) := by
    simp [Nat.coprime_mul_left_add_left]
  have hodd : Odd (2 * (N * l) + 1) := odd_two_mul_add_one _
  obtain ⟨z, hzI, hzK⟩ := zKill E Ω l D e (N * l) ρ hρ he hproc hlM _ hcop hodd
  have hφs : Function.Surjective ⇑((piQ ρ)⁻¹) := by
    intro y
    obtain ⟨b, hb⟩ := piQ_surjective ρ y⁻¹
    exact ⟨b, by simp [hb]⟩
  have hφ1 : ((piQ ρ)⁻¹) (-1) ≠ 1 := by
    simpa using hne
  obtain ⟨r0, hr0, hdet⟩ := detVal l _ (N * l) _ e _ hcop hφs hφ1 he (by omega) z hzI
  have hT : Nat.totient (N * l) ≠ 0 := (Nat.totient_pos.mpr (NeZero.pos _)).ne'
  obtain ⟨r1, hr1le, hr1dvd⟩ := nat_dvd_pow l (Nat.totient (N * l)) hT
  refine ⟨r0 + r1, ?_, ?_⟩
  · have hb := hC N l e hN hl2 he
    have hr1 : (r1 : ℝ) * Real.log l ≤ Real.log ((N : ℝ) * l) := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hr1le.trans (Nat.totient_le _)
    rw [hcard] at hr0
    have hd : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
    have hB := Real.log_natCast_nonneg (bdX (N * l) (2 * (N * l) + 1) (e + 1))
    have hL : 0 ≤ Real.log ((N : ℝ) * l) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      nlinarith)
    have h1 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ Module.finrank ℚ E)
    have h2 := mul_nonneg (sub_nonneg.2 hd) hL
    push_cast
    nlinarith
  · intro x hx
    obtain ⟨hxS, hxE⟩ := Submodule.mem_inf.mp hx
    rw [Module.End.mem_eigenspace_iff] at hxE
    have hK := hzK x hxS
    have hcm : ((piQ ρ)⁻¹) (-1) = piQ ρ (-1) := by
      rw [MonoidHom.inv_apply, ← map_inv, inv_neg_one]
    have hc : (actRep D (e : ℤ) ρ (((piQ ρ)⁻¹) (-1))) (Nat.totient (N * l) • x)
        = (((-1) ^ (e + 1) : ℤ) : ℤ_[l]) • (Nat.totient (N * l) • x) := by
      rw [hcm, actRep_piQ, hconj, map_nsmul]
      change Nat.totient (N * l) • (cAct D (e : ℤ)) x = _
      rw [hxE, smul_comm]
      push_cast
      rfl
    have hcc : ((piQ ρ)⁻¹) (-1) * ((piQ ρ)⁻¹) (-1) = 1 := by
      rw [← map_mul]
      simp
    have hεε : ((-1) ^ (e + 1) : ℤ) * (-1) ^ (e + 1) = 1 := by
      rw [← mul_pow]
      simp
    have hkill := adjKill ℤ_[l] _ _ (actRep D (e : ℤ) ρ) _ _ hcc hφ1 hεε z _ hc hK
    obtain ⟨u, hu⟩ := hdet
    obtain ⟨v, hv⟩ := hr1dvd
    rw [pow_add, hu, hv]
    calc _ = (u * v) • (detR (((piQ ρ)⁻¹) (-1)) ((-1) ^ (e + 1)) z • (Nat.totient (N * l) • x)) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ_[l], smul_smul, smul_smul]
          congr 1
          ring
      _ = 0 := by rw [hkill, smul_zero]
