module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.HolomorphicIntegrality.SgU
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.HolomorphicIntegrality.HolInt
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

open Polynomial GlobalTheory.KZ.JInt in
private theorem hol_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (Tw : Tower Ω ε) (f : Tw.K)
    (hf : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ Tw.an f = (φ : Mero)) : IsIntegral (Algebra.adjoin Ω {Tw.jK}) f := by
  classical
  obtain ⟨M, hM, hfix⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨φ, hφ, hφd⟩ := hf
  let orb : SL(2, ℤ) → Tw.K := fun γ => Tw.sl (ofSL γ) f
  have hfac : ∀ γ γ' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ → orb γ' = orb γ := by
    intro γ γ' h
    have hk : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have he : γ' = (γ' * γ⁻¹) * γ := by group
    show Tw.sl (ofSL γ') f = Tw.sl (ofSL γ) f
    conv_lhs => rw [he]
    rw [map_mul, Tw.sl_mul, hfix _ hk]
  have hfin : (Set.range orb).Finite := by
    let g' : SL(2, ZMod M) → Tw.K := fun x =>
      if h : ∃ γ, Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = x then orb h.choose else 0
    refine (Set.finite_range g').subset ?_
    rintro _ ⟨γ, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ, ?_⟩
    have h : ∃ γ', Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'
        = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ := ⟨γ, rfl⟩
    simp only [g', dif_pos h]
    exact hfac γ h.choose h.choose_spec
  set S := hfin.toFinset with hSdef
  have hmemS : ∀ s, s ∈ S ↔ ∃ γ, orb γ = s := by
    intro s
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_range]
  set P : Polynomial Tw.K := ∏ s ∈ S, (X - C s) with hPdef
  have hPmon : P.Monic := monic_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)
  have hroot : P.eval f = 0 := by
    rw [hPdef, eval_prod]
    refine Finset.prod_eq_zero ((hmemS f).2 ⟨1, ?_⟩) ?_
    · show Tw.sl (ofSL 1) f = f
      rw [map_one, Tw.sl_one]
    · simp
  have hinv : ∀ δ : SL(2, ℤ), ∀ n, Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hσS : S.image (Tw.sl (ofSL δ)) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        obtain ⟨γ, rfl⟩ := (hmemS s).1 hs
        refine (hmemS _).2 ⟨γ * δ, ?_⟩
        show Tw.sl (ofSL (γ * δ)) f = Tw.sl (ofSL δ) (Tw.sl (ofSL γ) f)
        rw [map_mul, Tw.sl_mul]
      · rw [Finset.card_image_of_injective _ (Tw.sl (ofSL δ)).injective]
    have hmap : P.map ((Tw.sl (ofSL δ)).toRingEquiv : Tw.K →+* Tw.K) = P := by
      rw [hPdef, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hσS]
      rw [Finset.prod_image (fun x _ y _ h => (Tw.sl (ofSL δ)).injective h)]
      rfl
    have h2 := congrArg (fun p => p.coeff n) hmap
    simp only [Polynomial.coeff_map] at h2
    exact h2
  have hS : ∀ s ∈ S, s ∈ holR Tw := by
    intro s hs
    obtain ⟨γ, rfl⟩ := (hmemS s).1 hs
    exact ⟨fun z => φ (mob (ofSL γ) z), hφ.comp (mob_diff _) (fun z hz => mob_im _ hz),
      Tw.an_sl _ _ _ hφd⟩
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    have hl : P ∈ lifts (holR Tw).subtype := by
      rw [hPdef]
      refine Subsemiring.prod_mem _ (fun s hs => ?_)
      exact ⟨X - C ⟨s, hS s hs⟩, by simp⟩
    intro n
    obtain ⟨c, hc⟩ := (lifts_iff_coeff_lifts P).1 hl n
    rw [← hc]
    exact c.2
  have hadj : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw ε.injective
      (by obtain ⟨ψ, h1, h2⟩ := Tw.j_hol; exact ⟨ψ, h2, h1⟩) _ (fun γ => hinv γ n) (hhol n)
  have hl2 : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hadj n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl2 hPmon
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hroot]

theorem UpperTheory.V.Z.Kato.Sym.KU.hol :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)) → ∀ W, X.OverY W → f ∈ W := by
  intro Ω _ _ _ ε X f hf W hW
  apply vs_mem_of_isIntegral
  obtain ⟨q, hqm, hq⟩ := hol_int ε X f hf
  let ι : Algebra.adjoin Ω {X.jK} →+* W :=
    { toFun := fun a => ⟨a.1, X.adjoin_le_of_overY W hW a.1 a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨q.map ι, hqm.map ι, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hq
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.KU.sgU :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → IsU X (siegel X c x) := by
  intro Ω _ _ _ ε X c x hx
  have hne := siegel_ne_zero Ω ε X c x hx
  obtain ⟨h1, h2⟩ := TopUnits.siegel_hol X hx
  refine ⟨hne, fun W hW => ?_⟩
  have a1 := (W.valuation_le_one_iff _).mpr (KU.hol Ω ε X _ h1 W hW)
  have a2 := (W.valuation_le_one_iff _).mpr (KU.hol Ω ε X _ h2 W hW)
  have a3 : W.valuation (siegel X c x) * W.valuation (siegel X c x)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  refine le_antisymm a1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_one_of_lt_of_le hlt a2
  rw [a3] at this
  exact lt_irrefl _ this
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem sieg_per {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x x' : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (h : ∀ i, ∃ j : ℤ, x' i = x i + j) : siegel X c x' = siegel X c x := by
  choose n hn using h
  have e : sgC c x' = sgC c x := by
    funext z
    rw [show x' = fun i => x i + n i from funext hn]
    exact GlobalTheory.Sieg.Per.sg_add_int c x n _ hx
  unfold siegel
  rw [e]

private theorem siegel_admissible_periodic {c : ℕ} {x x' : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (h : ∀ i, ∃ j : ℤ, x' i = x i + j) : GlobalTheory.Sieg.admitted c x' := by
  choose n hn using h
  rw [show x' = fun i => x i + n i from funext hn]
  exact GlobalTheory.Sieg.Per.isAdmissibleSmoothingFactor_add_intVector hx n

private theorem near {M : ℕ} (hM : 0 < M) (a : ℤ) (y : ZMod M) (h : (a : ZMod M) = y) :
    ∃ j : ℤ, (a : ℚ) / M = (y.val : ℚ) / M + j := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have h1 : ((y.val : ℤ) : ZMod M) = (a : ZMod M) := by rw [h]; simp
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨j, ?_⟩
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have h2 : (a : ℚ) - (y.val : ℚ) = M * j := by exact_mod_cast hj
  field_simp
  linear_combination h2

private theorem siegel_admissible_to_rat {c M : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hM : 0 < M) (hcM : Nat.Coprime c M) {x : Row M}
    (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i, (c : ℚ) * toQ M x i ∈ Set.range ((↑) : ℤ → ℚ) → x i = 0 := by
    rintro i ⟨j, hj⟩
    have h1 : (j : ℚ) * M = c * ((x i).val : ℚ) := by
      rw [hj]; unfold toQ; field_simp
    have h2 : j * (M : ℤ) = (c : ℤ) * ((x i).val : ℤ) := by exact_mod_cast h1
    have h3 : (c : ZMod M) * x i = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod M) h2
      simpa using this.symm
    exact ((ZMod.isUnit_iff_coprime c M).2 hcM).mul_right_eq_zero.1 h3
  refine ⟨hc, h6, fun h => hx ?_⟩
  funext i
  fin_cases i
  · exact key 0 h.1
  · exact key 1 h.2

theorem UpperTheory.V.Z.Kato.Sym.sgB :
    UpperTheory.V.Z.Kato.Sym.SgB := by
  intro Ω _ _ _ ε X c M hc h6 hM hcM x hx
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hA := siegel_admissible_to_rat hc h6 hM hcM hx
  refine ⟨KU.sgU Ω ε X c _ hA, fun γ => ?_, fun s => ?_, fun x' h => sieg_per X hA h⟩
  · unfold sg
    rw [SiegelSL.sl_siegel Ω ε X c _ γ hA]
    have hn : ∀ i, ∃ j : ℤ, GlobalTheory.Sieg.act (toQ M x) γ i = toQ M (rt x γ) i + j := by
      intro i
      obtain ⟨j, hj⟩ := near hM (∑ k, ((x k).val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) k i) (rt x γ i)
        (by simp [rt, Matrix.vecMul, dotProduct])
      refine ⟨j, ?_⟩
      unfold toQ
      rw [← hj]
      simp only [GlobalTheory.Sieg.act, Fin.sum_univ_two]
      push_cast
      ring
    have hne : rt x γ ≠ 0 := by
      intro h0
      apply hx
      have : rt (rt x γ) γ⁻¹ = x := by
        unfold rt
        rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul]
        simp
      rw [← this, h0]
      simp [rt]
    exact sieg_per X (siegel_admissible_to_rat hc h6 hM hcM hne) hn
  · obtain ⟨-, -, -, -, -, -, hL⟩ := lgB Ω ε X M hM
    have h0 : IsPrimitiveRoot (eOm ε (1 / (M : ℚ))) M := isPrimitiveRoot_eOm ε hM.ne'
    have hs : s (eOm ε (1 / M)) = eOm ε (((cyc M s).val : ℕ) / M) := by
      rw [(hL s s).2.2 _ h0.pow_eq_one]
      apply ε.injective
      rw [map_pow, GalUnits.eps_eOm, GalUnits.eps_eOm]
      unfold GlobalTheory.Sieg.ee
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hu : cyc M s⁻¹ * cyc M s = 1 := by
      rw [← (hL s⁻¹ s).1, inv_mul_cancel, (hL s s).2.1]
    have hne : gr M s x ≠ 0 := by
      intro h
      apply hx
      have a0 : x 0 = 0 := by simpa [gr] using congrFun h 0
      have a1 : cyc M s * x 1 = 0 := by simpa only [gr, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] using congrFun h 1
      have a2 : x 1 = 0 := by rw [← one_mul (x 1), ← hu, mul_assoc, a1, mul_zero]
      funext i
      fin_cases i
      · exact a0
      · exact a2
    have hB := siegel_admissible_to_rat hc h6 hM hcM hne
    have e1 : toQ M x = ![((x 0).val : ℚ) / M, ((x 1).val : ℚ) / M] := by
      funext i; fin_cases i <;> rfl
    have hn : ∀ i, ∃ j : ℤ, (![((x 0).val : ℚ) / M, (((cyc M s).val * (x 1).val : ℕ) : ℚ) / M] : Fin 2 → ℚ) i =
        toQ M (gr M s x) i + j := by
      intro i
      fin_cases i
      · exact ⟨0, by simp [toQ, gr]⟩
      · obtain ⟨j, hj⟩ := near hM (((cyc M s).val * (x 1).val : ℕ) : ℤ) (cyc M s * x 1) (by simp)
        exact ⟨j, by simpa [toQ, gr] using hj⟩
    unfold sg
    rw [← sieg_per X hB hn, e1]
    exact gal_siegel Ω ε X c M _ _ _ s hM (ZMod.val_lt _) hs (e1 ▸ hA) (siegel_admissible_periodic hB hn)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ComapLtOne
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem valuation_lt_one_iff_inv_not_mem {K : Type} [Field K] (A : ValuationSubring K) (x : K) (hx : x ≠ 0) :
    A.valuation x < 1 ↔ x⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le]
  have h0 : A.valuation x ≠ 0 := by simpa using hx
  constructor
  · intro h
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h⟩
  · intro h
    exact (one_lt_inv_iff₀.mp h).2

private theorem comap_lt_one {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (f : K →+* L) (x : K) :
    (B.comap f).valuation x < 1 ↔ B.valuation (f x) < 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hfx : f x ≠ 0 := (map_ne_zero f).mpr hx
  rw [valuation_lt_one_iff_inv_not_mem _ x hx, valuation_lt_one_iff_inv_not_mem _ (f x) hfx, ← map_inv₀]
  exact Iff.rfl

theorem UpperTheory.V.Z.Kato.Sym.mvPt :
    UpperTheory.V.Z.Kato.Sym.MvPt := by
  classical
  intro Ω _ _ _ ε X m hm τ s hA σ hσ u v P hP
  obtain ⟨-, -, -, -, -, hU, -, -⟩ := admB Ω ε X
  have ka1 := (kaB Ω ε X m hm P.a u hP.hu.1 hP.ha).2.2.2.2.1 σ τ s hA hσ
  have ka2 := (kaB Ω ε X m hm P.b v hP.hv.1 hP.hb).2.2.2.2.1 σ τ s hA hσ
  refine ⟨(hU τ s hA).1 u hP.hu, (hU τ s hA).1 v hP.hv, ?_, ?_, ?_, ?_, ?_⟩
  · show σ P.a ^ m = _
    rw [← map_pow, hP.ha, hσ]
  · show σ P.b ^ m = _
    rw [← map_pow, hP.hb, hσ]
  · intro g h hg hh
    show ka X m (σ P.a) g * ka X m (σ P.b) h =
      cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) - cyc m s ^ 2 * P.η (σ⁻¹ * (g * h) * σ) + cyc m s ^ 2 * P.η (σ⁻¹ * g * σ)
    have e : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) := by group
    have c := hP.cob _ _ (ka1 g hg).1 (ka1 h hh).1
    rw [(ka1 g hg).2, (ka2 h hh).2, e]
    linear_combination (cyc m s) ^ 2 * c
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B.image σ, fun h h' hh hh' e => ?_⟩
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = cyc m s ^ 2 * P.η (σ⁻¹ * h' * σ)
    rw [hB _ _ (ka1 h hh).1 (ka1 h' hh').1]
    intro b hb
    show σ⁻¹ (h (σ b)) = σ⁻¹ (h' (σ b))
    rw [e _ (Finset.mem_image_of_mem _ hb)]
  · intro B h hB hh hz
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = 0
    rw [hP.unr (B.comap (σ : Kb X →+* Kb X)) _ ?_ (ka1 h hh).1 ?_, mul_zero]
    · have e : (B.comap (σ : Kb X →+* Kb X)).comap (io X) = (B.comap (io X)).comap (τ : X.K →+* X.K) := by
        ext f
        simp only [ValuationSubring.mem_comap, RingHom.coe_coe]
        rw [hσ]
      rw [e]
      exact (hA.2 _).1 hB
    · intro z h1
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff] at h1
      rw [comap_lt_one]
      have := hz _ h1
      have e : (σ : Kb X →+* Kb X) ((σ⁻¹ * h * σ) z - z) = h ((σ : Kb X →+* Kb X) z) - (σ : Kb X →+* Kb X) z := by
        rw [map_sub]
        congr 1
        exact σ.apply_symm_apply _
      rw [e]
      exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvNear
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem semi_aeval {K L : Type} [Field K] [Field L] [Algebra K L] (σ : RingAut L) (τ : K ≃+* K)
    (hσ : ∀ f, σ (algebraMap K L f) = algebraMap K L (τ f)) (p : Polynomial K) (hp : ∀ c ∈ p.coeffs, τ c = c) (x : L) :
    σ (Polynomial.aeval x p) = Polynomial.aeval (σ x) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, hσ]
  by_cases h : p.coeff i = 0
  · simp [h]
  · rw [hp _ (Polynomial.coeff_mem_coeffs h)]

private theorem fix_lift {K : Type} [Field K] [CharZero K] (B : Finset (AlgebraicClosure K)) :
    ∃ S : Finset K, ∀ (τ : K ≃+* K) (σ₀ : RingAut (AlgebraicClosure K)),
      (∀ f, σ₀ (algebraMap K _ f) = algebraMap K _ (τ f)) → (∀ f ∈ S, τ f = f) →
      ∃ σ : RingAut (AlgebraicClosure K), (∀ f, σ (algebraMap K _ f) = algebraMap K _ (τ f)) ∧ ∀ b ∈ B, σ b = b := by
  classical
  set E := IntermediateField.adjoin K (B : Set (AlgebraicClosure K)) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hβ : IntermediateField.adjoin K {(α : AlgebraicClosure K)} = E := by
    have := congrArg (IntermediateField.map E.val) hα
    rw [IntermediateField.adjoin_map] at this
    simpa [← AlgHom.fieldRange_eq_map] using this
  generalize (α : AlgebraicClosure K) = β at hβ
  have hi : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hp : ∀ b : AlgebraicClosure K, ∃ p : Polynomial K, b ∈ B → Polynomial.aeval β p = b := by
    intro b
    by_cases hb : b ∈ B
    · have h1 : b ∈ IntermediateField.adjoin K {β} := by
        rw [hβ]; exact IntermediateField.subset_adjoin _ _ hb
      have h2 : b ∈ (IntermediateField.adjoin K {β}).toSubalgebra := h1
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval] at h2
      obtain ⟨p, hp⟩ := h2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose p hp using hp
  refine ⟨(minpoly K β).coeffs ∪ B.biUnion fun b => (p b).coeffs, fun τ σ₀ h0 hS => ?_⟩
  have hr : Polynomial.aeval (σ₀ β) (minpoly K β) = 0 := by
    rw [← semi_aeval σ₀ τ h0 _ fun c hc => hS c (Finset.mem_union_left _ hc), minpoly.aeval, map_zero]
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root hi.isAlgebraic hr
  have hl : ∀ f, (σ₀.trans g.toRingEquiv) (algebraMap K _ f) = algebraMap K _ (τ f) := fun f => by
    rw [RingEquiv.trans_apply, h0]; exact g.commutes _
  refine ⟨σ₀.trans g.toRingEquiv, hl, fun b hb => ?_⟩
  have := semi_aeval _ τ hl (p b) (fun c hc => hS c (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb, hc⟩))) β
  rw [hp b hb] at this
  rw [this]
  have e : (σ₀.trans g.toRingEquiv) β = β := hg
  rw [e, hp b hb]

theorem UpperTheory.V.Z.Kato.Sym.mvNear :
    UpperTheory.V.Z.Kato.Sym.MvNear := by
  classical
  intro Ω _ _ _ ε X m hm u v P hP
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  obtain ⟨hz, -, l3, -, -, l6, -⟩ := lgB Ω ε X m hm
  obtain ⟨B, hB⟩ := hP.lc
  obtain ⟨S, hS⟩ := fix_lift (K := X.K) ({P.a, P.b, zt X m} ∪ B.biUnion fun b => ((minpoly X.K b).aroots (Kb X)).toFinset)
  refine ⟨S, fun τ s hτ hfix => ?_⟩
  obtain ⟨σ₀, h0⟩ := (admB Ω ε X).2.2.2.2.2.2.1 τ
  obtain ⟨σ, hσ, hb⟩ := hS τ σ₀ h0 hfix
  have ea : σ P.a = P.a := hb _ (by simp)
  have eb : σ P.b = P.b := hb _ (by simp)
  have ez : σ (zt X m) = zt X m := hb _ (by simp)
  have ec : ∀ h, InD X h → ∀ b ∈ B, σ (h b) = h b := by
    intro h hh b hbB
    refine hb _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hbB, ?_⟩))
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral b), ?_⟩
    rw [← semi_aeval h (RingEquiv.refl _) hh _ (fun _ _ => rfl), minpoly.aeval, map_zero]
  have l0 : ∀ b : Kb X, b ≠ 0 → lg X m b b = 0 := fun b h => l3 b b 0 h (by simp)
  have hc : cyc m s = 1 := by
    have h1 := l3 (zt X m ^ (1 : ZMod m).val) 1 1 one_ne_zero (by simp)
    have h2 := l6 σ τ s hτ hσ (zt X m ^ (1 : ZMod m).val) 1 one_ne_zero
      (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow, one_pow])
    rw [map_pow, ez, map_one, h1, mul_one] at h2
    exact h2.symm
  have a0 : P.a ≠ 0 := fun h => hP.hu.1 ((io X).injective (by rw [← hP.ha, h, zero_pow hm.ne', map_zero]))
  have b0 : P.b ≠ 0 := fun h => hP.hv.1 ((io X).injective (by rw [← hP.hb, h, zero_pow hm.ne', map_zero]))
  refine ⟨σ, hσ, 1, by simp, fun h hh => ?_⟩
  have inv : ∀ x, σ⁻¹ (σ x) = x := fun x => σ.symm_apply_apply x
  have e : P.η (σ⁻¹ * h * σ) = P.η h := by
    refine hB _ _ (fun f => ?_) hh fun b hbB => ?_
    · show σ⁻¹ (h (σ (io X f))) = io X f
      rw [hσ, hh, ← hσ, inv]
    · show σ⁻¹ (h (σ b)) = h b
      have : σ b = b := ec 1 (fun _ => rfl) b hbB
      rw [this, ← ec h hh b hbB, inv, ec h hh b hbB]
  simp only [dif, Pt.mv, ka, hc, ea, eb, e, l0 _ a0, l0 _ b0, map_one, l0 1 one_ne_zero]
  ring
end
