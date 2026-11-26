module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem


open Polynomial in
theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : GlobalTheory.Sieg.admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : GlobalTheory.Sieg.admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  first | exact @GlobalTheory.KZ.SiegelMem.an_siegel_eq | exact GlobalTheory.KZ.SiegelMem.an_siegel_eq | (intros; apply GlobalTheory.KZ.SiegelMem.an_siegel_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_props :
    (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧
      (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧
        ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  obtain ⟨hH, hmul, hone, hsl, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hup : ∀ (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im), up f z = f ⟨z, hz⟩ := by
    intro f z hz
    simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hupH : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp only [up, UpperHalfPlane.ofComplex_apply]
  have h4 : ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
    intro g f z hz
    rw [hup _ z hz]
    rfl
  refine ⟨?_, ?_, ?_, h4⟩
  · intro f
    funext τ
    simp only [cmp, hone, hupH]
  · intro g h f
    funext τ
    have hτ : (τ : ℂ) ∈ Hs := τ.im_pos
    show up f (mob (g * h) τ) = up (cmp g f) (mob h τ)
    rw [h4 g f _ (hH h _ hτ), hmul g h _ hτ]
  · intro γ f
    funext τ
    simp only [cmp, hsl, hupH]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob : (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧ (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧ ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  first | exact @GlobalTheory.FN.cmp_props | exact GlobalTheory.FN.cmp_props | (intros; apply GlobalTheory.FN.cmp_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmul
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_mod (m v : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (m : ℂ)) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  conv_rhs => rw [← Nat.mod_add_div v m]
  push_cast
  have : 2 * Real.pi * Complex.I * ((v % m : ℕ) + (m : ℂ) * (v / m : ℕ)) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((v % m : ℕ) : ℂ) / (m : ℂ) + ((v / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_smul (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) (h : Kum X l n x χ) :
    Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hrel⟩ := h
  set k := (PadicInt.toZModPow n c).val with hk
  refine ⟨f ^ k, fun z => a z ^ k, fun z => b z ^ k, M, hM, ?_, ⟨ha.pow k, hb.pow k, ?_, ?_⟩, ?_⟩
  · rw [map_smul, hx, ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.1 c f)]
  · intro h0
    apply hb0
    have e1 := ((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 (fun z => b z ^ k) (fun _ => 0) (hb.pow k) (differentiableOn_const 0)).1 h0
    have e2 : ∀ z ∈ Hs, b z = 0 := fun z hz => (pow_eq_zero_iff' (M₀ := ℂ)).1 (e1 z hz) |>.1
    exact ((GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties).1 b (fun _ => 0) hb (differentiableOn_const 0)).2 e2
  · have e : ∀ (g : ℂ → ℂ), ((fun z => g z ^ k : ℂ → ℂ) : Mero) = (g : Mero) ^ k := fun g => rfl
    rw [e, e, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, mul_comm k, pow_mul, ← mul_pow, hr, ← pow_mul, ← pow_mul,
      mul_comm k]
  · intro δ hδ z hz
    have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    haveI : NeZero (l ^ n) := ⟨hl.ne'⟩
    simp only
    rw [← mul_pow, hrel δ hδ z hz, mul_pow, mul_pow, ZMod.val_mul]
    push_cast
    have em := exp_val_mod (l ^ n) (k * (χ δ).val) hl
    push_cast at em
    rw [em, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  first | exact @GlobalTheory.KZ.H3.kum_smul | exact GlobalTheory.KZ.H3.kum_smul | (intros; apply GlobalTheory.KZ.H3.kum_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongr
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumAdd

theorem gamma_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem exp_val_add {m : ℕ} [NeZero m] (x y : ZMod m) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / (m : ℂ)) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hs := Nat.mod_add_div (x.val + y.val) m
  rw [ZMod.val_add, ← Complex.exp_add]
  have key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (m : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * (((x.val + y.val) % m : ℕ) : ℂ) / (m : ℂ) +
        (((x.val + y.val) / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hc : (((x.val + y.val) % m : ℕ) : ℂ) + (m : ℂ) * (((x.val + y.val) / m : ℕ) : ℂ) = (x.val : ℂ) + (y.val : ℂ) := by
      exact_mod_cast hs
    calc 2 * Real.pi * Complex.I * (x.val : ℂ) / (m : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) / (m : ℂ)
        = 2 * Real.pi * Complex.I * ((x.val : ℂ) + (y.val : ℂ)) / (m : ℂ) := by ring
      _ = 2 * Real.pi * Complex.I * ((((x.val + y.val) % m : ℕ) : ℂ) + (m : ℂ) * (((x.val + y.val) / m : ℕ) : ℂ)) /
            (m : ℂ) := by rw [hc]
      _ = _ := by field_simp <;> ring
  rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

instance neZero_pow (l n : ℕ) [Fact l.Prime] : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩

end GlobalTheory.KZ.H3.KumAdd

namespace GlobalTheory.KZ.H3.KumAdd

theorem exp_val_add_pow (l n : ℕ) [Fact l.Prime] (x y : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  have := exp_val_add (m := l ^ n) x y
  push_cast at this
  exact this

theorem germ_mul_ne_zero {b b' : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (h : (b : Mero) ≠ 0) (h' : (b' : Mero) ≠ 0) : ((b * b' : ℂ → ℂ) : Mero) ≠ 0 := by
  intro H
  have h0 : DifferentiableOn ℂ (fun _ => (0 : ℂ)) Hs := differentiableOn_const 0
  have e := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (b * b') (fun _ => 0) (hb.mul hb') h0).1 (by rw [H]; rfl)
  rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 b b' hb hb' (fun z hz => by simpa using e z hz) with h1 | h1
  · exact h (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb h0).2 h1]; rfl)
  · exact h' (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b' (fun _ => 0) hb' h0).2 h1]; rfl)

theorem kum_add_zero_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, (∀ (x x' : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x' χ' →
      Kum X l n (x + x') (χ + χ')) ∧ Kum X l n 0 0 ∧
      (∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ χ' → Kum X l n x χ') := by
  intro Ω _ _ ε X l _ n
  have C := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  refine ⟨?_, ?_, ?_⟩
  · rintro x x' χ χ' ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩
    refine ⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_,
      ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩
    · rw [map_add (f := _), hx, hx', C.2.2.1]
    · rw [Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']
      ring
    · intro δ hδM z hz
      have e1 := hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz
      have e2 := hδ' δ (gamma_of_dvd (dvd_mul_left M' M) hδM) z hz
      simp only [Pi.mul_apply, Pi.add_apply]
      rw [exp_val_add_pow]
      linear_combination (a' (mob (ofSL δ) z) * b' z) * e1 +
        (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
          (a z * b (mob (ofSL δ) z))) * e2
  · refine ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, isRoot_one X _ ?_, ?_⟩
    · rw [map_zero, C.2.2.2.1]
    · intro H
      have := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (fun _ => (1 : ℂ)) (fun _ => 0) (differentiableOn_const 1)
        (differentiableOn_const 0)).1 (by rw [H]; rfl) Complex.I (by simp [Hs])
      simp at this
    · intro δ _ z _
      simp
  · rintro x χ χ' ⟨f, a, b, M, hM, hx, hr, hδ⟩ ⟨M', hM', hN⟩
    refine ⟨f, a, b, M * M', Nat.mul_pos hM hM', hx, hr, fun δ hδM z hz => ?_⟩
    rw [← hN δ (gamma_of_dvd (dvd_mul_left M' M) hδM)]
    exact hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz

end GlobalTheory.KZ.H3.KumAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ (x x' : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x' χ' → Kum X l n (x + x') (χ + χ')) ∧ Kum X l n 0 0 ∧ (∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ χ' → Kum X l n x χ') := by
  first | exact @GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near | exact GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near | (intros; apply GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQ
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQ
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ ε N f a hN hf
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set h := Φ (PowerSeries.mk a) with hh
  have hc : ∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k := fun k => by
    rw [hh, hΦ1]; simp
  have h0 : ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := fun r hr => hΦ0 _ r hr
  refine ⟨h, ⟨⟨N, hN, fun r hr => ?_⟩, 0, fun z hz => ?_⟩, hc, h0⟩
  · by_contra hne
    push_neg at hne
    exact hr (h0 r fun k hk => hne k (by rw [hk]; push_cast; rfl))
  · have hc' : ∀ k : ℕ, h.coeff (((0 + k : ℤ) : ℚ) / N) = a k := fun k => by
      simpa using hc k
    have h0' : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((0 + k : ℤ) : ℚ) / N) → h.coeff r = 0 := fun r hr =>
      h0 r fun k hk => hr k (by simpa using hk)
    rw [fn_hasSum_reindex_nat Ω ε h N 0 a z (up f z) hN hc' h0']
    have hq := (hasQ_iff N f _).mp hf ⟨z, hz⟩
    simpa [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  first | exact @GlobalTheory.fn_hahnSeries_of_hasQ | exact GlobalTheory.fn_hahnSeries_of_hasQ | (intros; apply GlobalTheory.fn_hahnSeries_of_hasQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue

section Calc

variable {Ω : Type} [Field Ω]

def DvA (A : ValuationSubring Ω) (l n : ℕ) (D : HahnSeries ℚ Ω) : Prop :=
  ∀ r, ∃ z ∈ A, D.coeff r = (l : Ω) ^ n * z

theorem coeffA_mul (A : ValuationSubring Ω) (P Q : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hQ : ∀ r, Q.coeff r ∈ A) (r : ℚ) : (P * Q).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => x ∈ A) (fun x y hx hy => add_mem hx hy) (zero_mem A)
    (fun ij _ => mul_mem (hP _) (hQ _))

theorem dvA_mul (A : ValuationSubring Ω) (l n : ℕ) (P D : HahnSeries ℚ Ω) (hP : ∀ r, P.coeff r ∈ A)
    (hD : DvA A l n D) : DvA A l n (P * D) := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = (l : Ω) ^ n * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, add_mem hz hw, by ring⟩
  · exact ⟨0, (zero_mem A), by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hD ij.2
    exact ⟨P.coeff ij.1 * z, mul_mem (hP _) hz, by rw [e]; ring⟩

theorem dvA_add (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω) (hD : DvA A l n D)
    (hE : DvA A l n E) : DvA A l n (D + E) := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  exact ⟨z + w, add_mem hz hw, by rw [HahnSeries.coeff_add, e, e']; ring⟩

theorem cgA_iff (A : ValuationSubring Ω) (l n : ℕ) (P Q : HahnSeries ℚ Ω) :
    (∀ r, CgA A l n (P.coeff r) (Q.coeff r)) ↔ DvA A l n (P - Q) := by
  simp only [CgA, DvA, HahnSeries.coeff_sub]

end Calc

theorem isDl_calc : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  intro Ω _ _ _ ε X _ l _ A _ n s f g φ ψ
  have lei := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ ⟨hψ, a2, b2, κ2, hκ2, hgb, hpa2, hpb2, hc2⟩
    refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hψ r),
      a * a2, b * b2, κ * κ2, mul_ne_zero hκ hκ2, ?_, ?_, ?_, ?_⟩
    · calc f * g * (b * b2) = (f * b) * (g * b2) := by ring
        _ = _ := by rw [hfb, hgb, map_mul]; ring
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpa hpa2
    · rw [map_mul]; exact GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hpb hpb2
    · rw [cgA_iff] at hc hc2 ⊢
      rw [map_mul, map_mul, lei, lei]
      have key : (φ + ψ) * (X.exp a * X.exp a2) * (X.exp b * X.exp b2) -
          ((theta s (X.exp a) * X.exp a2 + X.exp a * theta s (X.exp a2)) * (X.exp b * X.exp b2) -
            X.exp a * X.exp a2 * (theta s (X.exp b) * X.exp b2 + X.exp b * theta s (X.exp b2))) =
          (X.exp a2 * X.exp b2) * (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
          (X.exp a * X.exp b) * (ψ * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) := by
        ring
      rw [key]
      exact dvA_add A l n _ _ (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa2.1 hpb2.1) hc)
        (dvA_mul A l n _ _ (coeffA_mul A _ _ hpa.1 hpb.1) hc2)
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    have hf : f ≠ 0 := by
      rintro rfl
      have ha : a = 0 := by
        have : algebraMap Ω X.K κ * a = 0 := by rw [← hfb, zero_mul]
        rcases mul_eq_zero.mp this with h | h
        · exact absurd ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).mp h) hκ
        · exact h
      obtain ⟨r, hr, _⟩ := hpa.2
      exact hr (by rw [ha, map_zero, HahnSeries.coeff_zero])
    refine ⟨fun r => by rw [HahnSeries.coeff_neg]; exact neg_mem (hφ r), b, a, κ⁻¹, inv_ne_zero hκ, ?_, hpb, hpa, ?_⟩
    · have hk : algebraMap Ω X.K κ ≠ 0 := (map_ne_zero _).mpr hκ
      rw [map_inv₀]
      field_simp
      rw [mul_comm, hfb]
    · rw [cgA_iff] at hc ⊢
      have key : -φ * X.exp b * X.exp a - (theta s (X.exp b) * X.exp a - X.exp b * theta s (X.exp a)) =
          -(φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by ring
      rw [key]
      intro r
      obtain ⟨z, hz, e⟩ := hc r
      exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_neg, e]; ring⟩
  · rintro ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩ hψ hcg
    refine ⟨hψ, a, b, κ, hκ, hfb, hpa, hpb, ?_⟩
    rw [cgA_iff] at hc hcg ⊢
    have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
        (-(X.exp a * X.exp b)) * (φ - ψ) + (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) := by
      ring
    rw [key]
    refine dvA_add A l n _ _ (dvA_mul A l n _ _ ?_ hcg) hc
    intro r
    rw [HahnSeries.coeff_neg]
    exact neg_mem (coeffA_mul A _ _ hpa.1 hpb.1 r)
  · intro κ hκ
    have hp1 : Prim A (X.exp 1) := by
      rw [map_one]
      refine ⟨fun r => ?_, 0, ?_, ?_⟩
      · rw [HahnSeries.coeff_one]; split_ifs <;> simp
      · simp [HahnSeries.coeff_one]
      · simp [HahnSeries.coeff_one]
    refine ⟨fun r => by simp, 1, 1, κ, hκ, by simp, hp1, hp1, fun r => ⟨0, (zero_mem A), ?_⟩⟩
    simp
  · rintro n' hn ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, hc⟩
    refine ⟨hφ, a, b, κ, hκ, hfb, hpa, hpb, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨(l : Ω) ^ (n - n') * z, mul_mem (pow_mem (natCast_mem A l) _) hz, ?_⟩
    rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hn]

end GlobalTheory.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculusStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  first | exact @GlobalTheory.Glue.isDl_calc | exact GlobalTheory.Glue.isDl_calc | (intros; apply GlobalTheory.Glue.isDl_calc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.JInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

lemma den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have hz' : 0 < z.im := hz
  simp at him hre
  have hc : ent g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hre
  simp at hre
  have := det_pos g
  rw [hc, hre] at this
  simp at this

lemma mob_im (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hd := den_ne g hz
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := Complex.normSq_pos.2 hd
  have key : (mob g z).im = ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
    simp only [mob]
    rw [Complex.div_im]
    simp
    field_simp
    ring
  show 0 < (mob g z).im
  rw [key]
  have := det_pos g
  have : (0 : ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast this
  positivity

lemma mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

def holR (X : Tower Ω ε) : Subring X.K where
  carrier := {h | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ * ψ, hφ.mul hψ, by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ + ψ, hφ.add hψ, by rw [map_add (f := _), ha, hb]; rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, by rw [map_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    exact ⟨-φ, hφ.neg, by rw [map_neg, ha]; rfl⟩

end GlobalTheory.KZ.JInt

namespace GlobalTheory.KZ.JInt


open Polynomial in
theorem jK_sl_isIntegral : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  intro Ω _ _ _ ε Tw hε hj g
  set f := Tw.sl g Tw.jK with hf
  obtain ⟨M, hM, hlev⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

  have hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f := by
    intro γ γ' h
    have hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem']
      show red (γ' * γ⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have e : γ' = (γ' * γ⁻¹) * γ := by group
    rw [e, map_mul, Tw.sl_mul, hlev _ hmem]
  let S : Set Tw.K := Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f
  have hSfin : S.Finite := by
    classical
    let F : SL(2, ZMod M) → Tw.K := fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0
    apply (Set.finite_range F).subset
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact hred _ _ h.choose_spec
  let T := hSfin.toFinset
  have hT : ∀ y, y ∈ T ↔ y ∈ S := fun y => Set.Finite.mem_toFinset hSfin
  let P : Tw.K[X] := ∏ y ∈ T, (X - C y)
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hfT : f ∈ T := by
    rw [hT]; exact ⟨1, by simp [Tw.sl_one]⟩
  have hPf : P.eval f = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hfT (by simp)

  have hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]
      · intro y _
        rfl
    have := congrArg (fun p => p.coeff n) hmap
    simpa [coeff_map] using this

  obtain ⟨φ, hφ, hjφ⟩ := hj
  have hmemS : ∀ y ∈ T, y ∈ holR Tw := by
    intro y hy
    rw [hT] at hy
    obtain ⟨γ, rfl⟩ := hy
    have e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK := by rw [Tw.sl_mul]
    show Tw.sl (ofSL γ) f ∈ holR Tw
    rw [e]
    exact ⟨fun z => φ (mob (g * ofSL γ) z),
      hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩
  let Q : (holR Tw)[X] := ∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)
  have hQ : Q.map (holR Tw).subtype = P := by
    simp only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]
    exact Finset.prod_attach T (fun y => X - C y)
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    intro n
    rw [← hQ, coeff_map]
    exact (Q.coeff n).2

  have hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)
  have hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hA n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hPmon
  exact ⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩

end GlobalTheory.KZ.JInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRatStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  first | exact @GlobalTheory.KZ.JInt.jK_sl_isIntegral | exact GlobalTheory.KZ.JInt.jK_sl_isIntegral | (intros; apply GlobalTheory.KZ.JInt.jK_sl_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithin
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithin
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isOpen_Hs_mobt : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem tendsto_mob_codiscreteWithin :
    ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  intro g
  obtain ⟨hmaps, hmul, hone, -, hdiff, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hinj : ∀ x y : ℂ, x ∈ Hs → y ∈ Hs → mob g x = mob g y → x = y := by
    intro x y hx hy hxy
    have ex : mob (g⁻¹ * g) x = x := by rw [inv_mul_cancel, hone]
    have ey : mob (g⁻¹ * g) y = y := by rw [inv_mul_cancel, hone]
    rw [← ex, ← ey, hmul _ _ _ hx, hmul _ _ _ hy, hxy]
  intro S hS
  rw [Filter.mem_map, mem_codiscreteWithin]
  rw [mem_codiscreteWithin] at hS
  intro z hz
  have hw := hS (mob g z) (hmaps g z hz)
  have hHs : Hs ∈ nhds z := isOpen_Hs_mobt.mem_nhds hz
  have hcont : ContinuousAt (mob g) z := (hdiff g).continuousOn.continuousAt hHs
  have htend : Filter.Tendsto (mob g) (nhdsWithin z {z}ᶜ) (nhdsWithin (mob g z) {mob g z}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hHs, self_mem_nhdsWithin] with x hx hxz
    exact fun h => hxz (hinj x z hx hz h)
  rw [Filter.disjoint_principal_right] at hw ⊢
  filter_upwards [htend hw, nhdsWithin_le_nhds hHs] with x hx hxH
  rintro ⟨hx1, hx2⟩
  exact hx ⟨hmaps g x hx1, hx2⟩

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithinStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin : ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  first | exact @GlobalTheory.FN.tendsto_mob_codiscreteWithin | exact GlobalTheory.FN.tendsto_mob_codiscreteWithin | (intros; apply GlobalTheory.FN.tendsto_mob_codiscreteWithin <;> assumption)
end
end
