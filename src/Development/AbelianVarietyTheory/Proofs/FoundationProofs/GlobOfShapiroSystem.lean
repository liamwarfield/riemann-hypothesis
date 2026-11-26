module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTail
theorem UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have hi : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have hm : minpoly ℚ_[l] x = (minpoly ℤ_[l] x).map (algebraMap ℤ_[l] ℚ_[l]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hm,
    spectralValue_le_one_iff ((minpoly.monic hi).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l where
  toFun s := Units.map (algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l))).toMonoidHom (θ s)⁻¹ * W s
  map_one' := by simp
  map_mul' s t := by
    apply Units.ext
    simp only [map_mul, mul_inv, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      ← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Algebra.algebraMap_eq_smul_one, one_mul, mul_comm]

theorem mat_untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    mat (untwist W θ) s = (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) • mat W s := by
  show algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l)) (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s = _
  rw [← Algebra.smul_def]

theorem continuous_untwist {W : R2 Ω l} {θ : G ℚ Ω →* (Qbar l)ˣ} (hW : Continuous W) (hθ : Continuous θ) :
    Continuous (untwist W θ) := by
  have h1 : Continuous fun s => mat (untwist W θ) s := by
    simp only [mat_untwist]
    exact (Units.continuous_coe_inv.comp hθ).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun s => (((untwist W θ s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => (θ s : Qbar l) • (((W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    funext s
    rw [← map_inv, ← map_inv]
    have := mat_untwist W θ s⁻¹
    rw [map_inv θ, inv_inv] at this
    exact this
  rw [h2]
  exact (Units.continuous_val.comp hθ).smul (Units.continuous_coe_inv.comp hW)

theorem unr_of_twisted_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  intro l _ Ω _ _ _ W c θ ρ Y η y hW hθ _ hWρ hρ hYc hYi hSh hpush hη _ hy hlim q hq
  have hρ' : mat (untwist W θ) = ρ := by
    funext s
    rw [mat_untwist, hWρ, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨B, hB, v, hv⟩ := GlobalTheory.T.shifted_cocycle_limit_integral l Ω (untwist W θ) c Y η y (continuous_untwist hW hθ)
    (by rw [hρ']; exact hρ) hYc hYi (by rw [hρ']; exact hSh) hpush hη hlim q hq
  refine ⟨B, hB, ?_⟩
  by_cases h : ∀ s ∈ Ine (F := ℚ) B, θ s = 1
  · refine ⟨v, fun s hs => ?_⟩
    rw [hv s hs, mat_untwist, h s hs]
    simp
  · push Not at h
    obtain ⟨s, hs, hne⟩ := h
    refine ⟨0, fun t ht => ?_⟩
    have hc : y (s * t) = y s + mat W s *ᵥ y t := by
      rw [hy.2 s t]
      rfl
    have hm : mat (untwist W θ) (s * t) = mat (untwist W θ) s * mat (untwist W θ) t := by
      simp only [mat, map_mul, Units.val_mul]
    have hc' : y (s * t) = y s + mat (untwist W θ) s *ᵥ y t := by
      rw [hv _ (mul_mem hs ht), hv s hs, hv t ht, hm, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    rw [hc, mat_untwist, Matrix.smul_mulVec, add_right_inj] at hc'
    have h0 : mat W s *ᵥ y t = 0 := by
      have h1 : (1 - (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • (mat W s *ᵥ y t) = 0 := by
        rw [sub_smul, one_smul, ← hc', sub_self]
      refine (smul_eq_zero.1 h1).resolve_left fun h2 => hne ?_
      have h3 : (θ s)⁻¹ = 1 := Units.ext (sub_eq_zero.1 h2).symm
      exact inv_eq_one.1 h3
    have h4 : y t = 0 := by
      have h5 : mat W s⁻¹ *ᵥ (mat W s *ᵥ y t) = y t := by
        rw [Matrix.mulVec_mulVec]
        have : mat W s⁻¹ * mat W s = 1 := by
          simp only [mat]
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        rw [this, Matrix.one_mulVec]
      rw [← h5, h0, Matrix.mulVec_zero]
    rw [h4]
    simp

end GlobalTheory.KA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimitStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_away_from_l_of_twisted_shapiro_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  first | exact @GlobalTheory.KA.unr_of_twisted_limit | exact GlobalTheory.KA.unr_of_twisted_limit | (intros; apply GlobalTheory.KA.unr_of_twisted_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationAppr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationAppr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem spLink_of_spec_approx (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l)
    (h : ∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
      ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤
        ‖((l : ℕ) : Qbar l) ^ r‖) :
    SpLink A e χ (fun r s x => Y r s x 1) y := by
  intro n
  refine ⟨n, fun r hr s hs hc => ?_⟩
  have h1 := h r s hs hc
  have heq : spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1 =
      sp (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Y r s x 1) s := by
    simp only [spec, sp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at h1
  unfold Cg
  refine h1.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) hr

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationApprStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), (∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → SpLink A e χ (fun r s x => Y r s x 1) y := by
  first | exact @GlobalTheory.KZ.spLink_of_spec_approx | exact GlobalTheory.KZ.spLink_of_spec_approx | (intros; apply GlobalTheory.KZ.spLink_of_spec_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastOfCoprime
noncomputable section

namespace GlobalTheory.PadicNormCastBounds

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_le_one_of_isIntegral {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hz : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  let v := NormedField.valuation (K := PadicAlgCl l)
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast hz a
  have h1 : IsIntegral v.integer x := hx.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl)
  have h2 := (Valuation.integer.integers v).mem_of_integral h1
  rw [Valuation.mem_integer_iff] at h2
  exact_mod_cast h2

theorem norm_natCast_of_coprime {a : ℕ} (ha : a.Coprime l) : ‖(a : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ha.symm

theorem norm_inv_pow_val_le (r e : ℕ) (u : (ZMod (l ^ r))ˣ) :
    ‖((((u : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (u : ZMod (l ^ 0)).val = 0 := by
      have := ZMod.val_lt (u : ZMod (l ^ 0))
      simpa using this
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · simp [he.ne']
  · have hc : (u : ZMod (l ^ r)).val.Coprime l :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_pow_self l hr.ne')
    rw [norm_inv, norm_pow, norm_natCast_of_coprime hc]
    simp

theorem norm_inv_pow_sub_le {a b r : ℕ} (e : ℕ) (ha : a.Coprime l) (hb : b.Coprime l) (h : a ≡ b [MOD l ^ r]) :
    ‖((a : PadicAlgCl l) ^ e)⁻¹ - ((b : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
  have na := norm_natCast_of_coprime ha
  have nb := norm_natCast_of_coprime hb
  have a0 : (a : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero))
  have b0 : (b : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero))
  obtain ⟨k, hk⟩ := (h.pow e).dvd
  have hk' : (b : PadicAlgCl l) ^ e - (a : PadicAlgCl l) ^ e = (l : PadicAlgCl l) ^ r * (k : PadicAlgCl l) := by
    exact_mod_cast congrArg (Int.cast : ℤ → PadicAlgCl l) hk
  rw [inv_sub_inv a0 b0, hk', norm_div, norm_mul, norm_mul, norm_pow (a : PadicAlgCl l), norm_pow (b : PadicAlgCl l),
    na, nb, one_pow, one_mul, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ k)

theorem twist_compat (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e : ℕ)
    (χ : (r : ℕ) → (ZMod (l ^ r))ˣ → Formalism.ConjugateSelfDual.Qbar l)
    (hO : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), χ r x ∈ c.O)
    (hχ : ∀ (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r
      (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) : ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤
        ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => (((ZMod.val (x : ZMod (l ^ (r + 1))) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => (((ZMod.val (x : ZMod (l ^ r)) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ r x)
        (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
          ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤ ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖ := by
  have h1 := hχ r x
  generalize hy : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
    ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x = y at h1 ⊢
  have hint : ‖χ r y‖ ≤ 1 :=
    norm_le_one_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨χ r y, hO r y⟩ : c.O)).map c.O.val)
  have hA := norm_inv_pow_val_le (r + 1) e x
  have hB := norm_inv_pow_val_le r e y
  have hAB : ‖((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹ -
      ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero (l : PadicAlgCl l), norm_one, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
      rwa [norm_neg]
    · refine norm_inv_pow_sub_le e
        ((ZMod.val_coe_unit_coprime x).coprime_dvd_right (dvd_pow_self l r.succ_ne_zero))
        ((ZMod.val_coe_unit_coprime y).coprime_dvd_right (dvd_pow_self l hr.ne')) ?_
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val, ← hy]
      rfl
  dsimp only
  set A := ((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  set B := ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  have hsplit : A * χ (r + 1) x - B * χ r y = A * (χ (r + 1) x - χ r y) + (A - B) * χ r y := by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans h1
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hint).trans hAB

end GlobalTheory.PadicNormCastBounds

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCocycleOfPadicLimitOfApproxCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCocycleOfPadicLimitOfApproxCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.LimCoc

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  rw [h]
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [this, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem ultra3 {K : Type*} [NormedField K] [IsUltrametricDist K] (a b c e : K) (ε : ℝ)
    (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) (hc : ‖c‖ ≤ ε) (he : ‖e‖ ≤ ε) :
    ‖a + b - c - e‖ ≤ ε := by
  have hsub : ∀ u v : K, ‖u‖ ≤ ε → ‖v‖ ≤ ε → ‖u - v‖ ≤ ε := fun u v hu hv => by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by rwa [norm_neg]))
  exact hsub _ _ (hsub _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)) hc) he

theorem mulVec_small {K : Type*} [NormedField K] [IsUltrametricDist K]
    (A : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) (ε : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ ε) (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hw 0)
  have key : ∀ j, ‖A i j * w j‖ ≤ ε := fun j => by
    rw [norm_mul]
    calc ‖A i j‖ * ‖w j‖ ≤ 1 * ε := mul_le_mul (hA i j) (hw j) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key 0) (key 1))

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  intro l _ Γ _ M z y hM _ hz hy s t
  funext i
  rw [← sub_eq_zero, ← norm_eq_zero]
  have hbound : ∀ r : ℕ, ‖y (s * t) i - (y s + M s *ᵥ y t) i‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ r := by
    intro r
    rw [← norm_pow]
    have hdecomp : y (s * t) i - (y s + M s *ᵥ y t) i =
        (y (s * t) i - z r (s * t) i) + (z r (s * t) i - (z r s + M s *ᵥ z r t) i)
          - (y s i - z r s i) - (M s *ᵥ (y t - z r t)) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
      ring
    rw [hdecomp]
    exact ultra3 _ _ _ _ _ (hy r (s * t) i) (hz r s t i) (hy r s i)
      (mulVec_small (M s) (y t - z r t) _ (hM s) (fun j => by simpa using hy r t j) i)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)
  exact le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _)

end GlobalTheory.LimCoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCocycleOfPadicLimitOfApproxCocyclesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCocycle_of_padic_limit_of_approx_cocycles : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  first | exact @GlobalTheory.LimCoc.limit_cocycle | exact GlobalTheory.LimCoc.limit_cocycle | (intros; apply GlobalTheory.LimCoc.limit_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecApproxCocycle
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_approx_cocycle (l : ℕ) [Fact l.Prime] {Γ X : Type} [Group Γ] [CommGroup X] [Fintype X] (r : ℕ)
    (ρ : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (κ : Γ →* X) (Y : Γ → X → Fin 2 → Qbar l) (η : X → Qbar l)
    (τ : Γ → Qbar l) (hY : ShCoc ρ κ Y) (hρ : ∀ s i j, ‖ρ s i j‖ ≤ 1) (hYi : ∀ s x i, ‖Y s x i‖ ≤ 1)
    (hη : ∀ x, ‖η x‖ ≤ 1) (happ : ∀ s x, ‖η (x * (κ s)⁻¹) - η x * τ s‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∀ s t i, ‖spec η Y (s * t) i - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro s t i
  have hre : (∑ x, η x • Y t (x * κ s)) = ∑ x, η (x * (κ s)⁻¹) • Y t x := by
    exact Fintype.sum_equiv (Equiv.mulRight (κ s)) _ _ (fun x => by simp)
  have key : spec η Y (s * t) - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t))
      = ρ s *ᵥ ∑ x, (η (x * (κ s)⁻¹) - η x * τ s) • Y t x := by
    have h1 : spec η Y (s * t) = spec η Y s + ρ s *ᵥ ∑ x, η x • Y t (x * κ s) := by
      simp only [spec, hY s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [h1, hre, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
    congr 1
    simp only [spec, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (τ s)]
  have hC : (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := norm_nonneg _
  rw [← Pi.sub_apply, key]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro j _
  rw [norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρ s i j)) ?_
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro x _
  rw [norm_mul]
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (hYi t x j)) (happ s x)

end GlobalTheory.KA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastIsUnitPadicInt
namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (((x : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      exact Nat.lt_one_iff.mp (by simpa only [pow_zero] using ZMod.val_lt (x : ZMod (l ^ 0)))
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · let n := (x : ZMod (l ^ r)).val
    have hcop : l.Coprime n :=
      (ZMod.val_coe_unit_coprime x).symm.of_dvd_left (dvd_pow_self l hr.ne')
    have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
    obtain ⟨u, hu⟩ := (natCast_isUnit_padicInt l n hnd).pow e
    have key : ((n : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ↑u⁻¹ := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZGlobAsm

theorem norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem c hx

theorem inv_pow_val_mem (l : ℕ) [Fact l.Prime] (c : Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O :=
  _root_.GlobalTheory.PadicInversePower.inv_pow_mem l c e r x

theorem eta_compat (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (hχ : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => ((((x : ZMod (l ^ (r + 1))).val : ℕ) : Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x)
        ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
  _root_.GlobalTheory.PadicNormCastBounds.twist_compat l c e χ hχ hχc r x

end GlobalTheory.KZGlobAsm

namespace GlobalTheory.KZ

end GlobalTheory.KZ
