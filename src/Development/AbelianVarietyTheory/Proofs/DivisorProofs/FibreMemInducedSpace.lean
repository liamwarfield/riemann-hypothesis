module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_rfl' (a b : ℕ) : stdSum (rfl : a + b = a + b) = finSumFinEquiv := by
  ext x; simp [stdSum]

theorem X0_mul_invT_parab (a b : ℕ) (p : parab k (blocks a b)) :
    (X0 (k := k) (finSumFinEquiv (m := a) (n := b)) * (invT (p : GL (Fin (a + b)) k)).val :
      Matrix (Fin a) (Fin (a + b)) k) =
      ((invT (leviProj k (blocks a b) p false)).val : Matrix (Fin a) (Fin a) k) *
        X0 (k := k) (finSumFinEquiv (m := a) (n := b)) := by
  have hA : (invT (leviProj k (blocks a b) p false)).val
      = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ := by
    rw [invT_val, map_inv]; rfl
  refine Matrix.ext fun i j => ?_
  rw [frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with j | j
  · have := leviProj_apply k (blocks a b) p⁻¹ false j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this]
  · have hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j := fun i h => by
      have := congrArg Fin.val h; simp at this; omega
    have := (mem_parab_two k).1 (p⁻¹).2 j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this, hne]

variable [MeasurableSpace k] [BorelSpace k]

theorem fibre_mem_indSpace (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) :
    fibre ν β a b Φ ∈ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b)) := by
  intro p x
  rw [ofChar_apply]
  set A : GL (Fin a) k := leviProj k (blocks a b) p false with hAdef
  set D := leviProj k (blocks a b) p true with hDdef
  set Ψ := omA ν β 1 x Φ with hΨ
  set z : ℂ := ((a + b : ℕ) : ℂ) / 2 with hz
  let X : Matrix (Fin a) (Fin (a + b)) k := X0 (k := k) finSumFinEquiv
  set F : GL (Fin a) k → ℂ := fun g => Ψ (g.val * X) * (ν (gdet g) : ℂ) *
    apow (gdet g) z with hF
  set c : ℂ := (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
    ν (gdet A) * apow (gdet A) z with hc
  have h1 : omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ = omA ν β 1 ↑p Ψ := by rw [hΨ, ← omA_mul, one_mul]
  have h2 : ∀ Y, omA ν β 1 (↑p : GL (Fin (a + b)) k) Ψ Y =
      (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
        Ψ (Y * (invT (p : GL (Fin (a + b)) k)).val) := by
    intro Y
    simp [omA]
  have hm : ∀ g : GL (Fin a) k,
      (g.val * X) * (invT (p : GL (Fin (a + b)) k)).val = (g * invT A).val * X := by
    intro g
    rw [Matrix.mul_assoc, X0_mul_invT_parab, ← Matrix.mul_assoc, ← Units.val_mul]
  have key : ∀ g : GL (Fin a) k, omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) z = c * F (g * invT A) := by
    intro g
    rw [h1, h2, hm g]
    simp only [hF, hc, gdet_mul, gdet_invT, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, apow_mul,
      apow_inv, apow_neg]
    have n1 : (ν (gdet A) : ℂ) ≠ 0 := Units.ne_zero _
    have n2 : apow (gdet A) z ≠ 0 := apow_ne_zero _ _
    field_simp
  have hdet : gdet (p : GL (Fin (a + b)) k) = gdet A * gdet D := by
    have := det_parab k (blocks a b) p
    rw [Fintype.prod_bool] at this
    exact this.trans (mul_comm _ _)
  have hL : leviProj k (blocks a b) p = leviTwo k (Fin a) (Fin b) (A, D) := by
    funext t; cases t <;> rfl
  have hab : ∀ (s : ℂ) (y : kˣ), ((absPow k s y : ℂˣ) : ℂ) = apow y s := fun _ _ => rfl
  have hchar : ((parChar ν β a b p : ℂˣ) : ℂ) = c := by
    simp only [parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hL,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply, deltaHalf_two,
      MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, hab, Fintype.card_fin]
    have e : apow (gdet A) z * apow (gdet A) (-(a : ℂ) / 2) = apow (gdet A) ((b : ℂ) / 2) := by
      rw [← apow_add, hz]; congr 1; push_cast; ring
    rw [hc, hdet, map_mul, Units.val_mul, apow_mul]
    rw [← e]
    ring
  rw [hchar]
  have I1 : fibre ν β a b Φ ((p : GL (Fin (a + b)) k) * x) =
      ∫ g, c * F (g * invT A) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    integral_congr_ae (Filter.Eventually.of_forall key)
  have I2 : fibre ν β a b Φ x = ∫ g, F g ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := rfl
  rw [I1, I2, integral_const_mul, integral_mul_right_eq_self F (invT A)]

end GlobalTheory.RankFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpaceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_mem_induced_space : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)) := by
  first | exact @GlobalTheory.RankFibre.fibre_mem_indSpace | exact GlobalTheory.RankFibre.fibre_mem_indSpace | (intros; apply GlobalTheory.RankFibre.fibre_mem_indSpace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitWeil.FourierPi (box isCompact_box exists_box_subset)
open scoped Topology

noncomputable section

namespace GlobalTheory.KSp

theorem mem_box_of_forall_dot {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {d : Type} [Fintype d] [DecidableEq d] (ψ : AddChar F ℂ) {t₀ : Fˣ}
    (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F} (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) :
    v ∈ box d (t₀ * s⁻¹) := by
  intro i _
  by_contra h
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le] at h
  have hw : v i ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at h
    exact absurd h (not_lt_of_ge zero_le')
  apply ht
  have hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      have e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j := by
        push_cast
        field_simp
      have hpos : 0 < valuation F (v j) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hw
      rw [e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]
      exact mul_le_mul' h.le le_rfl
    · simp [Pi.single_eq_of_ne hj, GlobalTheory.SplitWeil.cball]
  have h2 := hv _ hu
  rwa [single_dotProduct, div_mul_cancel₀ _ hw] at h2

theorem isPair_addChar_form : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  intro F _ _ _ _ _ V _ _ _ _ _ ψ hψ hn h1 β hs hnd
  haveI := GlobalTheory.WeilM.nonarch_field F
  haveI := IsModuleTopology.toContinuousAdd F V
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ)
  let T : Fˣ := Units.mk0 t ht0
  have hT : ψ (T : F) ≠ 1 := ht
  let b := Module.finBasis F V
  let e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F) := LinearMap.pi fun i => β (b i)
  have hf₂ : Function.Injective f₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd y
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]
  have hbij : Function.Bijective f₂ :=
    ⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩
  let e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := LinearEquiv.ofBijective f₂ hbij
  have key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y := by
    intro u y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]
  have cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm := fun g =>
    ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap,
      IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩
  have ann : ∀ (s : Fˣ) y, (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) →
      e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹) := by
    intro s y h
    exact mem_box_of_forall_dot ψ hT s fun u hu => by rw [← key]; exact h u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    rw [map_add (f := _), LinearMap.add_apply, AddChar.map_add_eq_mul]
  · intro x y
    rw [hs]
  · intro x y
    exact hn _
  · exact (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · intro U hU
    have hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨r, hr⟩ := exists_box_subset hU'
    refine ⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹), (isCompact_box _).image (cont e₁).2,
      fun y hy => ?_⟩
    have h2 := ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩
    rw [show T * (T * r⁻¹)⁻¹ = r by rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]] at h2
    simpa using hr h2
  · intro U hU
    have hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨s, hs'⟩ := exists_box_subset hU'
    exact ⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2,
      fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩

end GlobalTheory.KSp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  first | exact @GlobalTheory.KSp.isPair_addChar_form | exact GlobalTheory.KSp.isPair_addChar_form | (intros; apply GlobalTheory.KSp.isPair_addChar_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWChain

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (X := (op (SimplexCategory.mk n), op (SimplexCategory.mk m)))
    (Y := (op (SimplexCategory.mk p), op (SimplexCategory.mk q)))
    (Z := (op (SimplexCategory.mk r), op (SimplexCategory.mk s))) (α.op, β.op) (α'.op, β'.op) 1 1
  simp only [mul_one] at this
  exact this

theorem comp_apply' {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (j : Fin (a+1)) :
    ((f ≫ g).toOrderHom j : ℕ) = (g.toOrderHom (f.toOrderHom j) : ℕ) := rfl

theorem hom_ext' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ j : Fin (a+1), (f.toOrderHom j : ℕ) = (g.toOrderHom j : ℕ)) : f = g := by
  apply SimplexCategory.Hom.ext
  ext j
  exact h j

theorem faceFun_lt {i j : ℕ} (h : j < i) : faceFun i j = j := if_pos h
theorem faceFun_ge {i j : ℕ} (h : i ≤ j) : faceFun i j = j + 1 := if_neg (by omega)

theorem backc_apply (n a b : ℕ) (j : Fin (b+1)) : ((backc n a b).toOrderHom j : ℕ) = min n (a + j) := rfl
theorem idc_apply (n m : ℕ) (j : Fin (m+1)) : ((idc n m).toOrderHom j : ℕ) = min n j := rfl
theorem fc_apply (n m i : ℕ) (j : Fin (m+1)) : ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

section
variable (a b : ℕ)

theorem front_face_low (i : ℕ) (hi : i ≤ a) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = fc (a+1) a i ≫ idc (a+b+1) (a+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (j:ℕ) i with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem back_face_low (i : ℕ) (hi : i ≤ a) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) i = idc b b ≫ backc (a+b+1) (a+1) b := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

theorem front_face_high (i : ℕ) (hi : a < i) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_high (j : ℕ) (hj : j ≤ b) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) (a+1+j) = fc (b+1) b (j+1) ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro k; have hk := k.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (k:ℕ) (j+1) with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem front_face_cancel : fc (a+1) a (a+1) ≫ idc (a+b+1) (a+1) = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_cancel : idc b b ≫ backc (a+b+1) (a+1) b = fc (b+1) b 0 ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

end

theorem dT_h (a b : ℕ) : dT (a+1) b a b = ∑ i ∈ Finset.range (a+1+1), ((-1 : ℤ) ^ i) • bop (fc (a+1) a i) (idc b b) := by
  simp [dT, dH, dV]

theorem dT_v (a b : ℕ) : dT a (b+1) a b = ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b+1+1), ((-1 : ℤ) ^ j) • bop (idc a a) (fc (b+1) b j) := by
  simp [dT, dH, dV]

theorem dT_zero (x y a b : ℕ) (h1 : ¬ (x = a + 1 ∧ y = b)) (h2 : ¬ (x = a ∧ y = b + 1)) : dT x y a b = 0 := by
  simp [dT, dH, dV, h1, h2]

end GlobalTheory.EZ.AWChain

namespace GlobalTheory.EZ
open GlobalTheory.EZ.AWChain

theorem awO_comm_d : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  intro n a b hab
  subst hab
  rw [Finset.sum_eq_add (a + 1, b) (a, b + 1) (by simp)]
  rotate_left
  · rintro c hc ⟨h1, h2⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  simp only [dT_h, dT_v]
  have e1 : awO (a + b + 1) (a + 1) b = bop (idc (a+b+1) (a+1)) (backc (a+b+1) (a+1) b) := if_pos (by omega)
  have e2 : awO (a + b + 1) a (b + 1) = bop (idc (a+b+1) a) (backc (a+b+1) a (b+1)) := if_pos (by omega)
  have e3 : awO (a + b) a b = bop (idc (a+b) a) (backc (a+b) a b) := if_pos rfl
  have e4 : dD (a + b + 1) (a + b) = ∑ i ∈ Finset.range (a+b+1+1),
      ((-1 : ℤ) ^ i) • bop (fc (a+b+1) (a+b) i) (fc (a+b+1) (a+b) i) := if_pos rfl
  rw [e1, e2, e3, e4]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    bop_comp]
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Finset.sum_range_add]
  conv_rhs => rw [Finset.sum_range_succ _ (a + 1), Finset.sum_range_succ' _ (b + 1), smul_add]
  have hA : ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) i) (backc (a+b) a b ≫ fc (a+b+1) (a+b) i) =
      ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (fc (a+1) a i ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [front_face_low a b i (by omega), back_face_low a b i (by omega)]
  have hB : ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (a + 1 + j)) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) (a + 1 + j)) (backc (a+b) a b ≫ fc (a+b+1) (a+b) (a + 1 + j)) =
      ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (j + 1)) •
      bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b (j + 1) ≫ backc (a+b+1) a (b+1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [front_face_high a b (a + 1 + j) (by omega), back_face_high a b j (by omega), smul_smul, ← pow_add, show a + (j + 1) = a + 1 + j by omega]
  have hC : ((-1 : ℤ) ^ (a + 1)) • bop (fc (a+1) a (a + 1) ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b)
      + ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ 0) • bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b 0 ≫ backc (a+b+1) a (b+1))) = 0 := by
    rw [front_face_cancel, back_face_cancel, smul_smul, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [hA, hB, add_add_add_comm, hC, add_zero]

end GlobalTheory.EZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommDStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  first | (exact @GlobalTheory.EZ.awO_comm_d) | (exact GlobalTheory.EZ.awO_comm_d) | (intros; apply GlobalTheory.EZ.awO_comm_d <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
open GlobalTheory.LGrp Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def upLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → Fin n → ℤ) :
    AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j h =>
    Valuation.map_add_le _ (hX.2 i j h) (hY.2 i j h)⟩
  neg_mem' := fun {X} hX => ⟨fun i j h => by simp [hX.1 i j h], fun i j h => by simpa using hX.2 i j h⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_upLat {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) :=
  Iff.rfl


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mul_mem_upLat {a b c : Fin n → Fin n → ℤ}
    (h : ∀ i j k, i < j → j < k → c i k ≤ a i j + b j k)
    {X Y : Matrix (Fin n) (Fin n) L} (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L a)
    (hY : Y ∈ _root_.GlobalTheory.BorelUMod.upLat L b) : X * Y ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  obtain ⟨hX0, hXv⟩ := hX
  obtain ⟨hY0, hYv⟩ := hY
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hX0 i k hki, zero_mul]
    · rw [hY0 k j (hji.trans hik.le), mul_zero]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · simp [hX0 i k hki]
    rcases le_or_gt j k with hjk | hkj
    · simp [hY0 k j hjk]
    rw [Valuation.map_mul]
    calc Valued.v (X i k) * Valued.v (Y k j)
        ≤ WithZero.exp (-a i k) * WithZero.exp (-b k j) := mul_le_mul' (hXv i k hik) (hYv k j hkj)
      _ = WithZero.exp (-a i k + -b k j) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-c i j) := WithZero.exp_le_exp.2 (by linarith [h i k j hik hkj])

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.upLat_mono {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c :=
  fun _ hX => ⟨hX.1, fun i j hij =>
    (hX.2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (h i j hij)))⟩

def adjJ (σ : L →+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := fun i j => σ (X j.rev i.rev)

def skewJ (σ : L →+* L) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | adjJ σ X = -X}
  zero_mem' := by ext i j; simp [adjJ]
  add_mem' := fun {X Y} hX hY => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hY i) j
    simp only [adjJ, Matrix.neg_apply] at h1 h2
    simp [adjJ, h1, h2, add_comm]
  neg_mem' := fun {X} hX => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    simp only [adjJ, Matrix.neg_apply] at h1
    simp [adjJ, h1]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_skewJ {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mul (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X * Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ Y * _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.mul_apply, map_sum, map_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_add (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X + Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X + _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_sub (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X - Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X - _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_smul (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_one (σ : L →+* L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [_root_.GlobalTheory.BorelUMod.adjJ]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.one_apply, h, h']

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_adjJ {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (_root_.GlobalTheory.BorelUMod.adjJ σ X) = X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ, hσ]


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_GU_iff_adjJ (σ : L →+* L) (g : GL (Fin n) L) :
    g ∈ _root_.Formalism.UG.GU σ n ↔ (g⁻¹).val = _root_.GlobalTheory.BorelUMod.adjJ σ g.val := by
  rw [_root_.GlobalTheory.LGrp.mem_GU_iff]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mem_upLat {σ : L →+* L}
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ}
    (hc : ∀ i j, c j.rev i.rev = c i j) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) :
    _root_.GlobalTheory.BorelUMod.adjJ σ X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · simp [_root_.GlobalTheory.BorelUMod.adjJ, hX.1 j.rev i.rev (Fin.rev_le_rev.2 hji)]
  · simp only [_root_.GlobalTheory.BorelUMod.adjJ]
    rw [hσ, ← hc i j]
    exact hX.2 j.rev i.rev (Fin.rev_lt_rev.2 hij)

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.smul_mem_upLat {c : Fin n → Fin n → ℤ} {a : L}
    (ha : Valued.v a ≤ 1) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) : a • X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => by simp [hX.1 i j hji], fun i j hij => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
  calc Valued.v a * Valued.v (X i j) ≤ 1 * WithZero.exp (-c i j) := mul_le_mul' ha (hX.2 i j hij)
    _ = WithZero.exp (-c i j) := one_mul _

def IsWeight (c : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, c j.rev i.rev = c i j) ∧ ∀ i j k, i < j → j < k → c i k ≤ c i j + c j k

def IsIdealWeight (c C : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, i < j → c i j ≤ C i j) ∧ (∀ i j k, i < j → j < k → C i k ≤ c i j + C j k) ∧
    ∀ i j k, i < j → j < k → C i k ≤ C i j + c j k

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.isWeight_zero :
    _root_.GlobalTheory.BorelUMod.IsWeight (fun _ _ : Fin n => (0 : ℤ)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => by simp⟩

def unipLat {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ} (hc : IsWeight c) :
    Subgroup (borelU σ n).U where
  carrier := {u | (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ upLat L c}
  one_mem' := by
    show ((1 : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L c
    simp
  mul_mem' := fun {u w} hu hw => by
    show u.1.1.val * w.1.1.val - 1 ∈ upLat L c
    have : u.1.1.val * w.1.1.val - 1 = (u.1.1.val - 1) * (w.1.1.val - 1) + (u.1.1.val - 1) + (w.1.1.val - 1) := by
      noncomm_ring
    rw [this]
    exact add_mem (add_mem (mul_mem_upLat hc.2 hu hw) hu) hw
  inv_mem' := fun {u} hu => by
    show (u.1.1⁻¹).val - 1 ∈ upLat L c
    rw [(mem_GU_iff_adjJ σ _).1 u.1.2, ← adjJ_one σ, ← adjJ_sub]
    exact adjJ_mem_upLat hσ hc.1 hu

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_unipLat {σ : L →+* L}
    {hσ : ∀ x, Valued.v (σ x) = Valued.v x} {c : Fin n → Fin n → ℤ}
    {hc : _root_.GlobalTheory.BorelUMod.IsWeight c} {u : (_root_.GlobalTheory.LGrp.borelU σ n).U} :
    u ∈ _root_.GlobalTheory.BorelUMod.unipLat hσ hc ↔
      (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ _root_.GlobalTheory.BorelUMod.upLat L c :=
  Iff.rfl


variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.exists_trace_one {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : _root_.Formalism.UG.IsUnramInv ϖ σ q) :
    (∃ θ : L, Valued.v θ ≤ 1 ∧ θ + σ θ = 1) ∧ ∃ d : L, Valued.v d = 1 ∧ σ d = -d := by
  obtain ⟨hinv, -, -, -, ⟨x, hx, hxu⟩, -⟩ := h
  have hx1 : Valued.v x ≤ 1 := hx
  refine ⟨?_, σ x - x, hxu, by rw [map_sub, hinv]; ring⟩
  have h2le : Valued.v (2 : L) ≤ 1 := by
    have h11 : Valued.v ((1 : L) + 1) ≤ 1 :=
      Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_eq (Valuation.map_one _))
    rwa [one_add_one_eq_two] at h11
  rcases h2le.lt_or_eq with h2 | h2
  · have hlt : Valued.v (2 * x) < Valued.v (σ x - x) := by
      rw [hxu, Valuation.map_mul]
      calc Valued.v (2 : L) * Valued.v x ≤ Valued.v (2 : L) * 1 := mul_le_mul' le_rfl hx1
        _ = Valued.v (2 : L) := mul_one _
        _ < 1 := h2
    have ht : Valued.v (x + σ x) = 1 := by
      have e : x + σ x = (σ x - x) + 2 * x := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hlt, hxu]
    have ht0 : x + σ x ≠ 0 := by
      intro e
      rw [e, Valuation.map_zero] at ht
      exact zero_ne_one ht
    refine ⟨x / (x + σ x), ?_, ?_⟩
    · rw [map_div₀, ht, div_one]
      exact hx1
    · rw [map_div₀, map_add (f := _), hinv, add_comm (σ x) x, ← add_div, div_self ht0]
  · refine ⟨1 / 2, ?_, ?_⟩
    · rw [map_div₀, Valuation.map_one, h2, div_one]
    · rw [map_div₀, map_one, map_ofNat]
      have h20 : (2 : L) ≠ 0 := by
        intro e
        rw [e, Valuation.map_zero] at h2
        exact zero_ne_one h2
      rw [← add_div, one_add_one_eq_two, div_self h20]

end GlobalTheory.BorelUMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem haar_UJ_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro n ε μ _
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by
    rw [Measure.map_smul, hR.map_mul_right_eq_self]
    exact (measurable_mul_const g).aemeasurable⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariantStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.haar_UJ_isMulRightInvariant | exact GlobalTheory.haar_UJ_isMulRightInvariant | (intros; apply GlobalTheory.haar_UJ_isMulRightInvariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open ReciprocityTheory.PGsh in
theorem isMF_eq_sum_monomials :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescale
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_comp_equiv (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y)
    (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ) (hμ : μ.map T = r • μ') (h : HasGauss μ' f γ) :
    HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hint⟩ := h (T '' K) (hK.image T.continuous)
  have hme : MeasurableEmbedding (T : X → Y) := T.toHomeomorph.measurableEmbedding
  have hset : ((L.comap (T.toAddEquiv.toAddMonoidHom) : AddSubgroup X) : Set X) = (T : X → Y) ⁻¹' (L : Set Y) := rfl
  refine ⟨L.comap T.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact T.toHomeomorph.isCompact_preimage.2 hLc
  · rw [hset]
    exact hLo.preimage T.continuous
  · rw [hset]
    intro x hx
    exact hKL ⟨x, hx, rfl⟩
  · rw [hset, ← hme.setIntegral_map f (L : Set Y), hμ, Measure.restrict_smul, integral_smul_nnreal_measure, hint]
    simp [NNReal.smul_def]

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale : ∀ (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y) (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ), μ.map T = r • μ' → HasGauss μ' f γ → HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  first | exact @GlobalTheory.KSp.hasGauss_comp_equiv | exact GlobalTheory.KSp.hasGauss_comp_equiv | (intros; apply GlobalTheory.KSp.hasGauss_comp_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntries
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem pcLieEntry : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  intro n ε Z
  have key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b := by
    intro a b
    simp [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  unfold inG
  constructor
  · intro h a b
    have hb := congrFun (congrFun h b) a
    rw [key] at hb
    simp only [Matrix.zero_apply] at hb
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb
  · intro h
    ext a b
    rw [key]
    simp only [Matrix.zero_apply]
    have hb := h b a
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntriesStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  first | exact @GlobalTheory.pcLieEntry | exact GlobalTheory.pcLieEntry | (intros; apply GlobalTheory.pcLieEntry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphism
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem cochain_fromTriv_eq (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    {k : K.K} (T : K.Obj) (hle : K.le l T.k k) (ρ : Hol (K.W k) →+* T.C)
    (hρ : Close T.J (T.ρ.comp (K.sh hle)) ρ) :
    ∀ hc : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) T.C f,
      h _ _ (fromTriv T hle ρ hc hρ) = h _ _ (ptHom T hle) := by
  induction hρ with
  | refl => intro hc; rfl
  | @tail ρ₁ ρ₂ hab s ih =>
    intro hc₂
    obtain ⟨n, h1, h2, h3⟩ := s
    have hc₁ : ∀ f, ρ₁ (K.cst k f) = algebraMap (Hol F.V) T.C f := fun f ↦ by
      rw [← hc₂ f, h3]
      simp [dw_cst]
    rw [← ih hc₁]
    obtain ⟨χ, hdeg, e0, e1, -⟩ := GlobalTheory.AnPer.Charts.exists_jet_factor K (fromTriv T hle ρ₁ hc₁ hab)
      (fromTriv T hle ρ₂ hc₂ (Relation.ReflTransGen.tail hab ⟨n, h1, h2, h3⟩)) n rfl h1 h2 (fun x ↦ h3 x)
    rw [← e0, ← e1]
    exact (H k T χ hdeg).symm

theorem cochain_eq_ptHom {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T) (hf : f.deg = l) :
    h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  subst hf
  letI := (K.triv k).alg
  exact cochain_fromTriv_eq K h f.deg H T (Charts.Hom.le f) f.φ.toRingHom (Charts.Hom.close f)
    (fun x ↦ f.φ.commutes x)

end GlobalTheory.AnPer.Charts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphismStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc) (l : Λ), (∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ)) → ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = l → h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  first | exact @GlobalTheory.AnPer.Charts.cochain_eq_ptHom | exact GlobalTheory.AnPer.Charts.cochain_eq_ptHom | (intros; apply GlobalTheory.AnPer.Charts.cochain_eq_ptHom <;> assumption)
end
end
