module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.liftEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], (∀ b : (ZMod N)ˣ, ∃ σ : Ω ≃+* Ω, CycLift N b σ) ∧ ∀ σ : Ω ≃+* Ω, ∃ b : (ZMod N)ˣ, CycLift N b σ := by
  intro E Ω _ _ _ _ _ N _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hpos : 0 < N := NeZero.pos N
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N Ω) (Polynomial.degree_cyclotomic_pos N Ω hpos).ne'
  have hζp : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  constructor
  · intro b
    have hx : IsPrimitiveRoot (ζ ^ (b : ZMod N).val) N := hζp.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)
    have hmin : minpoly ℚ ζ = Polynomial.cyclotomic N ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζp hpos).symm
    have hev : Polynomial.aeval (ζ ^ (b : ZMod N).val) (minpoly ℚ ζ) = 0 := by
      rw [hmin, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact Polynomial.isRoot_cyclotomic_iff.mpr hx
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic ζ) hev
    refine ⟨σ.toRingEquiv, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    show σ (ζ ^ k) = (ζ ^ k) ^ (b : ZMod N).val
    rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]
  · intro σ
    have h1 : IsPrimitiveRoot (σ ζ) N := hζp.map_of_injective σ.injective
    obtain ⟨i, hi, hiζ⟩ := hζp.eq_pow_of_pow_eq_one h1.pow_eq_one
    have hcop : i.Coprime N := (hζp.pow_iff_coprime hpos i).mp (hiζ ▸ h1)
    refine ⟨ZMod.unitOfCoprime i hcop, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    rw [map_pow, ← hiζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi, ← pow_mul, ← pow_mul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_cyc_char_iff_toZModPow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)]
    (g : Ω ≃+* Ω) (k : ℕ) (c : ZMod (l ^ k)) :
    (∀ t : Ω, t ^ (l ^ k) = 1 → g t = t ^ c.val) ↔
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = c := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
    have h1 := cyclotomicCharacter.spec l g ζ hζ.pow_eq_one
    rw [h ζ hζ.pow_eq_one] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact (ZMod.val_injective _ h2).symm
  · rintro h t ht
    rw [cyclotomicCharacter.spec l g t ht, h]

private theorem pow_mod_eq_pow_of_pow_eq_one {Ω : Type} [Field Ω] (t : Ω) (n a : ℕ) (ht : t ^ n = 1) :
    t ^ (a % n) = t ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem UpperTheory.V.Odd.fixLev :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (N m : ℕ) [NeZero N], fixMu E Ω (l ^ m) = Un E Ω l m ∧ Uinf E Ω l ⊓ fixMu E Ω N ≤ fixMu E Ω (N * l ^ m) ∧ ∀ (M : ℕ) [NeZero M] (b : (ZMod M)ˣ) (σ : Ω ≃+* Ω), l ^ m ∣ M → CycLift M b σ → (l : ℤ_[l]) ^ m ∣ ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) := by
  intro E Ω _ _ _ _ _ l _ N m _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have key : ∀ (g : G E Ω) (k : ℕ),
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1 ↔
        ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := by
    intro g k
    rw [← pow_cyc_char_iff_toZModPow_eq l _ k 1]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    rw [ZMod.val_one_eq_one_mod, pow_mod_eq_pow_of_pow_eq_one t _ 1 ht, pow_one]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · ext g
    simp only [Un, levU, Subgroup.mem_inf, Subgroup.mem_top, true_and, Subgroup.mem_comap, KStar.TotallyRealRoots.princ,
      cycZ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_coe, Units.val_one]
    change _ ↔ PadicInt.toZModPow m _ = 1
    rw [key]
    rfl
  · intro g hg
    rcases Subgroup.mem_inf.1 hg with ⟨h1, h2⟩
    have hχ : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) = 1 := by
      simpa only [Uinf, cycU, Subgroup.mem_inf, Subgroup.mem_top, true_and, MonoidHom.mem_ker, cycZ,
        MonoidHom.comp_apply] using h1
    have hl : ∀ k, ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := fun k => (key g k).1 (by rw [hχ, Units.val_one, map_one])
    have hN : ∀ t : Ω, t ^ N = 1 → g t = t := h2
    obtain ⟨e, N', hndvd, hNe⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) l (Fact.out : l.Prime).one_lt.ne'
    have hcop : Nat.Coprime (l ^ (e + m)) N' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hndvd)
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))] at hx
      exact zero_ne_one hx
    have hxA : x ^ (l ^ (e + m) * N') = 1 := by
      rw [← hx, hNe, pow_add]
      congr 1
      ring
    have h3 : g (x ^ N') = x ^ N' := hl (e + m) _ (by rw [← pow_mul, mul_comm, hxA])
    have h4 : g (x ^ (l ^ (e + m))) = x ^ (l ^ (e + m)) := by
      apply hN
      rw [hNe, ← pow_mul, show l ^ (e + m) * (l ^ e * N') = (l ^ (e + m) * N') * l ^ e by ring, pow_mul, hxA,
        one_pow]
    have hyA : (g x * x⁻¹) ^ (l ^ (e + m)) = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h4, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hyB : (g x * x⁻¹) ^ N' = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h3, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hy : (g x * x⁻¹) ^ (Nat.gcd (l ^ (e + m)) N') = 1 := pow_gcd_eq_one.2 ⟨hyA, hyB⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hy
    exact (mul_inv_eq_one₀ hx0).1 hy
  · intro M _ b σ hdvd hσ
    have hc := (pow_cyc_char_iff_toZModPow_eq l σ m (((b : ZMod M).val : ℕ) : ZMod (l ^ m))).1 (by
      intro t ht
      rw [ZMod.val_natCast, pow_mod_eq_pow_of_pow_eq_one t _ _ ht]
      apply hσ
      obtain ⟨q, rfl⟩ := hdvd
      rw [pow_mul, ht, one_pow])
    have hmem : ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) ∈
        RingHom.ker (PadicInt.toZModPow m) := by
      rw [RingHom.mem_ker, map_sub, hc, map_natCast, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ContinuousToTorsionBounded
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem continuous_to_torsion_bounded {G : Type} [TopologicalSpace G] [CompactSpace G] (l : ℕ) [Fact l.Prime]
    (f : G → QZ l) (hf : Continuous f) : ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • f g = 0 := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  choose k hk using (UpperTheory.V.Kum.qzBasic l).2.1
  obtain ⟨r, hr⟩ := (hfin.image k).bddAbove
  refine ⟨r, fun g => ?_⟩
  have h1 : k (f g) ≤ r := hr ⟨f g, ⟨g, rfl⟩, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have h2 : (l : ℤ_[l]) ^ k (f g) • f g = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hk _
  rw [pow_add, mul_smul, h2, smul_zero]

theorem UpperTheory.V.Odd.Z1_H1_qz_twist_l_power_torsion :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), (∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ x : H1 (qzTw D e), ∃ r : ℕ, (l : ℤ_[l]) ^ r • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e
  have h : ∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0 := fun z =>
    continuous_to_torsion_bounded l z.1 z.2.1
  refine ⟨h, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨r, hr⟩ := h z
  refine ⟨r, ?_⟩
  have hz : (l : ℤ_[l]) ^ r • z = 0 := Subtype.ext (funext hr)
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.actEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E), IsCycAct Ω N ρ := by
  intro E Ω _ _ _ _ _ N _ hf
  obtain ⟨f⟩ := hf
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra E (CyclotomicField N ℚ) := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ E (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E (CyclotomicField N ℚ)
  haveI : Algebra.IsAlgebraic E (CyclotomicField N ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let g : CyclotomicField N ℚ →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(AlgEquiv.restrictNormalHom E).comp
    (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom, ?_⟩
  intro b σ hσ x
  set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm b with hτ
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  have key : ∀ y : CyclotomicField N ℚ, σ (g y) = g (τ y) := by
    have hcomp : (σ.toRingHom.comp (g : CyclotomicField N ℚ →+* Ω)).toRatAlgHom =
        ((g : CyclotomicField N ℚ →+* Ω).comp (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ)).toRatAlgHom := by
      apply (hζ.powerBasis ℚ).algHom_ext
      simp only [IsPrimitiveRoot.powerBasis_gen, RingHom.toRatAlgHom_apply, RingHom.coe_comp,
        Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgHom.coe_toRingHom]
      have h1 : (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) ^ N = 1 := by
        rw [← map_pow, hζ.pow_eq_one, map_one]
      change σ (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) =
        g (τ (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)))
      rw [hσ _ h1, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, map_pow, hτ,
        MulEquiv.apply_symm_apply]
    intro y
    exact congrArg (fun φ => φ y) hcomp
  change σ (algebraMap E Ω x) = algebraMap E Ω ((AlgEquiv.restrictNormal τ E) x)
  rw [← g.commutes x, ← g.commutes, AlgEquiv.restrictNormal_commutes, key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem conj_cycLift {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] {σ : Ω ≃+* Ω} (h : IsConjOm σ) :
    CycLift N (-1) σ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  obtain ⟨j, hj⟩ := h
  intro x hx
  apply j.injective
  rw [hj, map_pow, Units.val_neg, Units.val_one, ZMod.val_neg_one]
  have hz : (j x) ^ (n + 1) = 1 := by rw [← map_pow, hx, map_one]
  have hnorm : ‖j x‖ = 1 := by
    have : ‖j x‖ ^ (n + 1) = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 this
  have hne : j x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 : j x * (starRingEnd ℂ) (j x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have h2 : j x * (j x) ^ n = 1 := by rw [← pow_succ', hz]
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem UpperTheory.V.Odd.actConj :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → (ρ (-1)).toRingEquiv = cE E ∧ piQ ρ (-1) ≠ 1 := by
  intro E Ω _ _ _ _ _ _ N _ ρ hρ
  obtain ⟨σ, hσ⟩ := exists_isConjOm (E := E) (Ω := Ω)
  have hL1 : IsLift (cE E) σ := hσ.isLift
  have hL2 : IsLift (ρ (-1)).toRingEquiv σ := hρ (-1) σ (conj_cycLift N hσ)
  have heq : (ρ (-1)).toRingEquiv = cE E := by
    ext x
    apply (algebraMap E Ω).injective
    rw [← hL2 x, hL1 x]
  refine ⟨heq, ?_⟩
  intro hone
  have hker : ρ (-1) = 1 := by
    have := (QuotientGroup.eq_one_iff (N := ρ.ker) (-1 : (ZMod N)ˣ)).1 hone
    exact this
  apply IsCMField.complexConj_ne_one (K := E)
  ext x
  have := congrArg (fun f : E ≃+* E => f x) heq
  simp only [hker] at this
  exact this.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FnOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.fnOne :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], Module.finrank E (Fn E Ω l 1) ∣ l - 1 ∧ (∃ ζ : Fn E Ω l 1, IsPrimitiveRoot ζ l) ∧ ∀ N : ℕ, 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Nonempty (Fn E Ω l 1 →ₐ[ℚ] CyclotomicField (l * N) ℚ) := by
  intro E Ω _ _ _ _ _ l hl
  have hl0 : NeZero l := ⟨hl.out.ne_zero⟩
  have hc0 := (UpperTheory.V.Kum.fnCyc E Ω l 1).1
  rw [pow_one] at hc0
  have hc : IsCyclotomicExtension {l} E (Fn E Ω l 1) := hc0
  refine ⟨?_, ⟨_, IsCyclotomicExtension.zeta_spec l E (Fn E Ω l 1)⟩, ?_⟩
  · have hfd : FiniteDimensional E (Fn E Ω l 1) :=
      IsCyclotomicExtension.finiteDimensional {l} E _
    have hg : IsGalois E (Fn E Ω l 1) := IsCyclotomicExtension.isGalois {l} E _
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.totient_prime hl.out, ← ZMod.card_units_eq_totient,
      ← Nat.card_eq_fintype_card]
    exact Subgroup.card_dvd_of_injective _
      (IsPrimitiveRoot.autToPow_injective E (IsCyclotomicExtension.zeta_spec l E (Fn E Ω l 1)))
  · intro N hN ⟨φ⟩
    have hN0 : NeZero N := ⟨hN.ne'⟩
    have hlN0 : NeZero (l * N) := ⟨Nat.mul_ne_zero hl.out.ne_zero hN.ne'⟩
    have hlNq : NeZero ((l * N : ℕ) : ℚ) := ⟨by exact_mod_cast hlN0.out⟩
    have hNq : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN0.out⟩
    letI hcyc : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    letI hcycN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
      CyclotomicField.isCyclotomicExtension N ℚ
    obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField (l * N) ℚ, IsPrimitiveRoot ζ (l * N) :=
      ⟨_, IsCyclotomicExtension.zeta_spec (l * N) ℚ (CyclotomicField (l * N) ℚ)⟩
    have hζN : IsPrimitiveRoot (ζ ^ l) N := hζ.pow (Nat.pos_of_ne_zero hlN0.out) rfl
    have hζl : IsPrimitiveRoot (ζ ^ N) l := hζ.pow (Nat.pos_of_ne_zero hlN0.out) (mul_comm l N)
    have hsN : Polynomial.IsSplittingField ℚ (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ _
    have hsl : Polynomial.IsSplittingField E (Fn E Ω l 1) (Polynomial.X ^ l - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one l E _
    have hsplitN : (Polynomial.map (algebraMap ℚ (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ N - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      have h := Polynomial.X_pow_sub_one_splits hζN
      rwa [Polynomial.C_1] at h
    let ψ := Polynomial.IsSplittingField.lift (CyclotomicField N ℚ)
      (Polynomial.X ^ N - 1 : Polynomial ℚ) hsplitN
    letI : Algebra E (CyclotomicField (l * N) ℚ) := ((ψ.comp φ) : E →+* _).toAlgebra
    have hsplitl : (Polynomial.map (algebraMap E (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ l - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      have h := Polynomial.X_pow_sub_one_splits hζl
      rwa [Polynomial.C_1] at h
    exact ⟨((Polynomial.IsSplittingField.lift (Fn E Ω l 1) (Polynomial.X ^ l - 1 : Polynomial E)
      hsplitl : Fn E Ω l 1 →ₐ[E] _) : Fn E Ω l 1 →+* _).toRatAlgHom⟩
end
