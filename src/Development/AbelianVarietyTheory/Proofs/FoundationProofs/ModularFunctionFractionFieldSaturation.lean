module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelation
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hring := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SaturationLevelFunctionsIntegralRelationStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturation_levelFunctions_integralRelation : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  first | exact @GlobalTheory.FN.Sat.sat | exact GlobalTheory.FN.Sat.sat | (intros; apply GlobalTheory.FN.Sat.sat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldClearDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldClearDenominators
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧
      ∀ i, T.io (p i) = u * P.coeff i := by
  intro Ω _ _ _ ε T P hP
  classical
  choose a b hb hab using T.io_surj
  set S := Finset.range (P.natDegree + 1) with hS
  have hbne : ∀ f, T.io (b f) ≠ 0 := fun f h => hb f (T.io_inj (by rw [h, map_zero]))
  refine ⟨fun i => if i ∈ S then a (P.coeff i) * ∏ j ∈ S.erase i, b (P.coeff j) else 0,
    T.io (∏ j ∈ S, b (P.coeff j)), ?_, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hbne _
  · have hmem : P.natDegree ∈ S := by simp [hS]
    intro h
    simp only [hmem, if_true] at h
    have h2 := congrArg T.io h
    rw [map_zero, map_mul, ← hab, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hmem] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hP (Polynomial.leadingCoeff_eq_zero.mp h3)
    · exact (Finset.prod_ne_zero_iff.mpr fun j _ => hbne _) h3
  · intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [map_mul, ← hab, map_prod, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hi, mul_comm]
    · simp only [hi, if_false, map_zero]
      have : P.natDegree < i := by simp [hS] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, mul_zero]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldClearDenominatorsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧ ∀ i, T.io (p i) = u * P.coeff i := by
  first | exact @GlobalTheory.FN.clear_denominators | exact GlobalTheory.FN.clear_denominators | (intros; apply GlobalTheory.FN.clear_denominators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨p, u, hu, hpn, hp⟩ := GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturationStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_saturation : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  first | exact @GlobalTheory.fn_sat | exact GlobalTheory.fn_sat | (intros; apply GlobalTheory.fn_sat <;> assumption)
end
