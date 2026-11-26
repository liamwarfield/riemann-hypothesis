module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneTau
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y) → ∃ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ := by
  intro Ω _ _ _ M F n a _ hFn ζ hζ δ hδ y hy hfix hz
  have hM : M ≠ 0 := NeZero.ne M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hM)
  have hcomm := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 y hfix
  have hroot : ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ∃ k : ℕ, k < M ∧ ζ ^ k = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro g _ z hz'
    apply hζ.eq_pow_of_pow_eq_one
    have hgy : g y ≠ 0 := by simpa using hy
    have hdy : δ y ≠ 0 := by simpa using hy
    have hdgy : δ (g y) ≠ 0 := by simpa using hgy
    unfold opP
    calc (g (δ Y / Y ^ a) / (δ Y / Y ^ a) / (δ z / z ^ a)) ^ M
        = g (δ (Y ^ M)) / (g (Y ^ M)) ^ a / (δ (Y ^ M) / (Y ^ M) ^ a) / (δ (z ^ M) / (z ^ M) ^ a) := by
          simp only [map_div₀, map_pow, div_pow]
          ring
      _ = 1 := by
          rw [hY, hz', map_div₀ δ, hcomm g δ]
          field_simp
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero a hy)]
  classical
  choose! zf hzf using hz
  have hk := fun g hg => hroot g hg (zf g) (hzf g hg).2
  choose! kf hkf using hk
  refine ⟨fun g => (kf g : ZMod M), Y, hY, fun g hg => ⟨zf g, (hzf g hg).1, (hzf g hg).2, ?_⟩⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hkf g hg).1]
  exact (hkf g hg).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.SysOfLax
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω]

private def Cg (A : ValuationSubring Ω) (u v : Ω) : Prop :=
  A.valuation u = 1 ∧ A.valuation v = 1 ∧ A.valuation (u - v) < 1

private theorem cg_of (A : ValuationSubring Ω) {u v : Ω} (hu : A.valuation u = 1) (h : A.valuation (u - v) < 1) :
    Cg A u v := by
  refine ⟨hu, ?_, h⟩
  have h1 : A.valuation (-(u - v)) < A.valuation u := by rw [Valuation.map_neg, hu]; exact h
  have h2 := A.valuation.map_add_eq_of_lt_left h1
  have h3 : u + -(u - v) = v := by ring
  rw [h3, hu] at h2
  exact h2

private theorem cg_mul {A : ValuationSubring Ω} {u v u' v' : Ω} (h : Cg A u v) (h' : Cg A u' v') :
    Cg A (u * u') (v * v') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], by rw [map_mul, h.2.1, h'.2.1, one_mul], ?_⟩
  have : u * u' - v * v' = u * (u' - v') + (u - v) * v' := by ring
  rw [this]
  refine A.valuation.map_add_lt ?_ ?_
  · rw [map_mul, h.1, one_mul]; exact h'.2.2
  · rw [map_mul, h'.2.1, mul_one]; exact h.2.2

private theorem cg_pow {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) (n : ℕ) : Cg A (u ^ n) (v ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ]; exact cg_mul ih h

private theorem cg_inv {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) : Cg A u⁻¹ v⁻¹ := by
  have hu : u ≠ 0 := fun h0 => by have := h.1; rw [h0, map_zero] at this; exact zero_ne_one this
  have hv : v ≠ 0 := fun h0 => by have := h.2.1; rw [h0, map_zero] at this; exact zero_ne_one this
  refine ⟨by rw [map_inv₀, h.1, inv_one], by rw [map_inv₀, h.2.1, inv_one], ?_⟩
  have : u⁻¹ - v⁻¹ = -((u - v) * u⁻¹ * v⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, h.1, h.2.1, inv_one, mul_one, mul_one]
  exact h.2.2

variable [Algebra ℚ Ω]

private theorem opP_mul (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u * v) = opP δ a u * opP δ a v := by
  simp only [opP, map_mul, mul_pow, mul_div_mul_comm]

private theorem opP_div (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u / v) = opP δ a u / opP δ a v := by
  simp only [opP, map_div₀, div_pow]
  rw [div_div_div_comm]

private theorem opP_pow (δ : G ℚ Ω) (a : ℕ) (u : Ω) (n : ℕ) : opP δ a (u ^ n) = opP δ a u ^ n := by
  simp only [opP, map_pow, div_pow]
  rw [← pow_mul, ← pow_mul, mul_comm]

private theorem map_opP (δ g : G ℚ Ω) (a : ℕ) (u : Ω) (h : g (δ u) = δ (g u)) :
    g (opP δ a u) = opP δ a (g u) := by
  simp only [opP, map_div₀, map_pow, h]

private theorem opP_root (δ : G ℚ Ω) (a N : ℕ) (hN : N ≠ 0) (hδ : Pows N a δ) (ζ : Ω) (h : ζ ^ N = 1) :
    opP δ a ζ = 1 := by
  have h0 : ζ ≠ 0 := fun h0 => by rw [h0, zero_pow hN] at h; exact zero_ne_one h
  rw [opP, hδ ζ h, div_self (pow_ne_zero _ h0)]

private theorem nrm_opP (δ τ : G ℚ Ω) (a q n : ℕ) (u : Ω) (h : ∀ g : G ℚ Ω, g (δ u) = δ (g u)) :
    nrm q τ (opP δ a u ^ n) = opP δ a (nrm q τ u) ^ n := by
  simp only [nrm, map_pow, opP, map_div₀, h, map_prod]
  rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_pow]

end SlopeTestRemainingChoices

private theorem admissible_of_integral_conj_le {l F r q d : ℕ} (h : ML.admitted l F r (q * d)) : ML.admitted l F r d :=
  ⟨h.1.squarefree_of_dvd (Dvd.intro_left q rfl), fun p hp hd => h.2 p hp (hd.mul_left q)⟩

private theorem admissible_prime_coprime {l F r q : ℕ} (h : AdmP l F r q) : q.Coprime r := by
  have hq := h.1
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  haveI : Fact q.Prime := ⟨hq⟩
  apply h.2.2.2
  have : (r : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff r q).2 hd
  rw [this, orderOf_zero]
  exact dvd_zero l

theorem UpperTheory.V.ML.sysOfLax :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l N₀ m F r a : ℕ), l.Prime → l ≠ 2 → N₀.Coprime l → 1 ≤ m → F = N₀ * l ^ m → ∀ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s →
    ∀ δ : G ℚ Ω, Pows (l ^ m) a δ → Sys l F r (fun d => opP δ a (X d) ^ (2 * N₀ * d)) fun d q => q * s d q := by
  intro Ω _ _ _ l N₀ m F r a hl _ hN hm hF X s hX δ hδ
  have hN0 : N₀ ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hN
    exact hl.one_lt.ne' hN
  have hlm : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hF0 : F ≠ 0 := hF ▸ mul_ne_zero hN0 hlm
  have hFd : ∀ d, ML.admitted l F r d → F * d ≠ 0 := fun d hd => mul_ne_zero hF0 hd.1.ne_zero
  have hcomm : ∀ d, ML.admitted l F r d → ∀ g h : G ℚ Ω, g (h (X d)) = h (g (X d)) := fun d hd =>
    (galBasic Ω (F * d) (hFd d hd)).2.2.2.2.2.1 (X d) (hX.fix d hd)
  obtain ⟨-, -, -, hcop, -, -, -, -, -, hact⟩ := placeBasic Ω
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) < 1 ↔ (δ⁻¹ • A).valuation y < 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.1 y
    rwa [smul_inv_smul] at this
  have heq : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) = 1 ↔ (δ⁻¹ • A).valuation y = 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.2 y
    rwa [smul_inv_smul] at this
  have hov : ∀ (A : ValuationSubring Ω) (n : ℕ), Over (δ⁻¹ • A) n ↔ Over A n := fun A n => by
    have := hlt A (n : Ω)
    rw [map_natCast] at this
    exact this.symm
  have hδu : ∀ d, ML.admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (δ (X d)) = 1 :=
    fun d hd A hA => (heq A _).2 (hX.unit d hd _ fun h => hA ((hov A r).1 h))
  have hζ : ∀ (n : ℕ) (ζ : Ω), ζ ^ (2 * F * n) = 1 → opP δ a ζ ^ (2 * N₀ * n) = 1 := fun n ζ h => by
    rw [← opP_pow]
    refine opP_root δ a (l ^ m) hlm hδ _ ?_
    rw [← pow_mul, ← h, hF]
    congr 1
    ring
  refine ⟨fun d hd => ?_, fun d hd g hg => ?_, fun d hd A hA => ?_, fun d q hq hd => ?_,
    fun d q hq hd τ hτ hgen φ hφ => ?_, fun d q hq hd φ hφ A hA => ?_⟩
  · refine pow_ne_zero _ (div_ne_zero ?_ (pow_ne_zero _ (hX.ne d hd)))
    exact (map_ne_zero δ).2 (hX.ne d hd)
  · rw [map_pow, map_opP δ g a _ (hcomm d hd g δ), hX.fix d hd g hg]
  · rw [map_pow, opP, map_div₀, map_pow, hδu d hd A hA, hX.unit d hd A hA]
    simp
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · have h1 := (hd.2 q hq (Dvd.intro d rfl)).2.1
      have hlF : l ∣ F := hF ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N₀
      have h2 : l ∣ 1 := ((h1.of_dvd hlF).dvd_iff dvd_rfl).1 h
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
    · exact hX.cop d q hq hd h
  · obtain ⟨ζ, h1, h2⟩ := hX.norm d q hq hd τ hτ hgen φ hφ
    rw [nrm_opP δ τ a q _ _ (fun g => hcomm _ hd g δ), h2, opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, opP_div,
      map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← div_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · obtain ⟨ζ, h1, h2⟩ := hX.cong d q hq hd φ hφ
    have hr : ¬ Over A r := hcop A q r (admissible_prime_coprime (hd.2 q hq (Dvd.intro d rfl))) hA
    have c1 := cg_of A (hX.unit _ hd A hr) (h2 A hA)
    have h3 := (hlt A _).2 (h2 _ ((hov A q).2 hA))
    rw [map_sub] at h3
    have c2 := cg_of A (hδu _ hd A hr) h3
    have c3 := cg_pow (cg_mul c2 (cg_inv (cg_pow c1 a))) (2 * N₀ * (q * d))
    rw [← div_eq_mul_inv, ← div_eq_mul_inv] at c3
    have c4 : A.valuation (opP δ a (X (q * d)) ^ (2 * N₀ * (q * d)) -
      opP δ a (ζ * φ⁻¹ (X d) ^ s d q) ^ (2 * N₀ * (q * d))) < 1 := c3.2.2
    rw [opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, ← pow_mul] at c4
    rw [map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← pow_mul]
    have e : 2 * N₀ * d * (q * s d q) = s d q * (2 * N₀ * (q * d)) := by ring
    rw [e]
    exact c4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValAddSmul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_add_smul {W : Type} [AddCommGroup W] {M : ℕ} [NeZero M] (x : W) (hx : M • x = 0) (a b : ZMod M) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← add_smul]
  conv_rhs => rw [← Nat.mod_add_div' (a.val + b.val) M]
  rw [add_smul, mul_smul, hx, smul_zero, add_zero]

private theorem lc_sum {X ι W : Type} [TopologicalSpace X] [AddCommGroup W] (s : Finset ι) (f : ι → X → W)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const (0 : W)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

theorem UpperTheory.V.ML.nuIs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ) [NeZero M] [NeZero F], F ∣ n → ∀ (β : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, (M : O) ∣ (β g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ w : W, M • w = 0 → ∀ κ : G ℚ Ω → ZMod M, (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) → IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) →
    (∀ A : ValuationSubring Ω, ¬ Over A n → ∀ g ∈ Ine (F := ℚ) A, κ g = 0) → IsNu M F n β (nu β σ w κ) := by
  intro Ω _ _ _ O W _ _ _ M F n _ _ hFn β hβ σ hσ w hw κ hκ hlc hunr
  have hF0 : F ≠ 0 := NeZero.ne F
  obtain ⟨hN, -, -, -, hlift, -, -, -, -, hmul⟩ := galBasic Ω F hF0
  have pb := (placeBasic Ω).2.2.2.2.2.2.2.2.2
  have hcm : ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, g⁻¹ * u * g ∈ fixMu ℚ Ω F := by
    intro g u hu
    have := hN.conj_mem u hu g⁻¹
    rwa [inv_inv] at this
  have hfix : ∀ k ∈ fixMu ℚ Ω F, ∀ x : W, M • x = 0 → (β k : O) • x = x := by
    intro k hk x hx
    obtain ⟨c, hc⟩ := hβ k hk
    have e : (β k : O) = 1 + c * M := by
      rw [mul_comm, ← hc]
      ring
    rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero, add_zero]
  have hx : ∀ g : G ℚ Ω, M • ((β g : O) • w) = 0 := by
    intro g
    rw [smul_comm, hw, smul_zero]
  have h1 : κ 1 = 0 := by
    have := hκ 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hinv : ∀ k ∈ fixMu ℚ Ω F, κ k⁻¹ + κ k = 0 := by
    intro k hk
    rw [← hκ _ (inv_mem hk) _ hk, inv_mul_cancel, h1]
  have hconj : ∀ k ∈ fixMu ℚ Ω F, ∀ y ∈ fixMu ℚ Ω F, κ (k⁻¹ * y * k) = κ y := by
    intro k hk y hy
    rw [hκ _ (mul_mem (inv_mem hk) hy) _ hk, hκ _ (inv_mem hk) _ hy]
    linear_combination hinv k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    simp only [nu]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e : (σ t)⁻¹ * (u * v) * σ t = ((σ t)⁻¹ * u * σ t) * ((σ t)⁻¹ * v * σ t) := by group
    rw [e, hκ _ (hcm _ u hu) _ (hcm _ v hv)]
    exact val_add_smul _ (hx (σ t)) _ _
  · simp only [nu]
    apply lc_sum
    intro t
    let c : fixMu ℚ Ω F → fixMu ℚ Ω F := fun u => ⟨(σ t)⁻¹ * u * σ t, hcm _ u u.2⟩
    have hc : Continuous c :=
      Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
    exact (hlc.comp_continuous hc).comp (fun k : ZMod M => k.val • ((β (σ t) : O) • w))
  · intro g u hu
    obtain ⟨b, hb⟩ := hlift g
    simp only [nu]
    rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft b)
      (fun t => (κ ((σ t)⁻¹ * (g * u * g⁻¹) * σ t)).val • (β (σ t) : O) • w)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    show (κ ((σ (b * s))⁻¹ * (g * u * g⁻¹) * σ (b * s))).val • (β (σ (b * s)) : O) • w = _
    have hk0 : (g * σ s)⁻¹ * σ (b * s) ∈ fixMu ℚ Ω F :=
      (hmul (b * s) (b * s) (g * σ s) (σ (b * s)) (hmul b s g (σ s) hb (hσ s)).1 (hσ (b * s))).2.2.mp rfl
    obtain ⟨k, hk, hτ⟩ : ∃ k ∈ fixMu ℚ Ω F, σ (b * s) = g * σ s * k := ⟨_, hk0, by group⟩
    rw [hτ]
    have e : (g * σ s * k)⁻¹ * (g * u * g⁻¹) * (g * σ s * k) = k⁻¹ * ((σ s)⁻¹ * u * σ s) * k := by group
    rw [e, hconj k hk _ (hcm _ u hu), map_mul, map_mul, Units.val_mul, Units.val_mul, mul_smul, mul_smul,
      hfix k hk w hw]
    exact smul_comm _ _ _
  · intro u hu
    simp only [nu]
    rw [Finset.smul_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [smul_comm, hx (σ t), smul_zero]
  · intro A hA g hg
    simp only [nu]
    apply Finset.sum_eq_zero
    intro t _
    have hA' : ¬ Over ((σ t)⁻¹ • A) n := by
      intro h'
      apply hA
      have := ((pb A (σ t)⁻¹).2.2.2.1 (n : Ω)).1
      rw [map_natCast] at this
      exact this h'
    have hmem : (σ t)⁻¹ * g * σ t ∈ Ine (F := ℚ) ((σ t)⁻¹ • A) := by
      rw [(pb A (σ t)⁻¹).2.1]
      have e : (σ t)⁻¹⁻¹ * ((σ t)⁻¹ * g * σ t) * (σ t)⁻¹ = g := by group
      rw [e]
      exact hg
    rw [hunr _ hA' _ hmem, ZMod.val_zero, zero_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneRad
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem ordv_prime (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal)
    (a : ℚˣ) (ha : (a : ℚ) = r) : UpperTheory.V.Kum.ordv v a = 1 := by
  have hpr : Prime (r : 𝓞 ℚ) := by
    have h1 : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) (r : 𝓞 ℚ)) := by
      rw [map_natCast]
      exact Nat.prime_iff_prime_int.mp hr
    exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h1
  have hne : (r : 𝓞 ℚ) ≠ 0 := hpr.ne_zero
  have hspan : v.asIdeal = Ideal.span {(r : 𝓞 ℚ)} := by
    have hP : (Ideal.span {(r : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hpr
    have hbot : Ideal.span {(r : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hne
    have hmax := hP.isMaximal hbot
    have hle : Ideal.span {(r : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    exact (hmax.eq_of_le v.isPrime.ne_top hle).symm
  have hint : v.intValuation (r : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := v.intValuation_singleton hne hspan
  have hval : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ha, ← hint]
    have : ((r : ℚ)) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : v.valuationOfNeZero a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hval]
    rfl
  unfold UpperTheory.V.Kum.ordv
  rw [h2]
  simp

theorem UpperTheory.V.ML.ineRad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (r M : ℕ), r.Prime → M.Coprime r → ∀ A : ValuationSubring Ω, Over A r → ∀ ρ ζ : Ω, ρ ^ M = (r : Ω) → ζ ^ M = 1 → ∃ t ∈ Ine (F := ℚ) A, t ρ = ζ * ρ := by
  intro Ω _ _ _ r M hr hM A hA ρ ζ hρ hζ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [Nat.coprime_zero_left] at hM
    exact hr.ne_one hM
  haveI : NeZero M := ⟨hM0⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hnot : ¬ Over A M := fun h => pb.2.2.2.1 A M r hM h hA
  have hfix : Ine (F := ℚ) A ≤ fixMu ℚ Ω M := pb.2.2.2.2.1 A M hnot
  have hroot : ∀ g : G ℚ Ω, (g ρ / ρ) ^ M = 1 := by
    intro g
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hgne : ∀ g : G ℚ Ω, g ρ / ρ ≠ 0 := fun g =>
    div_ne_zero (by simpa using hρ0) hρ0
  let χ : ↥(Ine (F := ℚ) A) →* Ωˣ :=
    { toFun := fun g => Units.mk0 ((g : G ℚ Ω) ρ / ρ) (hgne g)
      map_one' := by
        ext
        simp [div_self hρ0]
      map_mul' := by
        intro g h
        ext
        have hc : (g : G ℚ Ω) ((h : G ℚ Ω) ρ / ρ) = (h : G ℚ Ω) ρ / ρ :=
          hfix g.2 _ (hroot h)
        have hh : (h : G ℚ Ω) ρ = ((h : G ℚ Ω) ρ / ρ) * ρ := by
          field_simp
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
        rw [hh, map_mul, hc]
        field_simp }
  have hχ : ∀ g, ((χ g : Ωˣ) : Ω) = (g : G ℚ Ω) ρ / ρ := fun g => rfl
  have hle : χ.range ≤ rootsOfUnity M Ω := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, hχ, hroot, Units.val_one]
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd0 : 0 < Nat.card χ.range := Nat.card_pos
  have hfixd : ∀ g ∈ Ine (F := ℚ) A, g (ρ ^ Nat.card χ.range) = ρ ^ Nat.card χ.range := by
    intro g hg
    have h1 := congrArg (fun x : χ.range => ((x : Ωˣ) : Ω))
      (pow_card_eq_one' (x := (⟨χ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : χ.range)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hχ, OneMemClass.coe_one,
      Units.val_one] at h1
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hρ0)] at h1
    rw [map_pow]
    exact h1
  obtain ⟨v, hvA, -, hvr⟩ := pb.2.2.2.2.2.2.2.2.1 A r hr hA
  let a : ℚˣ := Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)
  have ha1 : UpperTheory.V.Kum.ordv v a = 1 := ordv_prime r hr v hvr a rfl
  have hpow : UpperTheory.V.Kum.ordv v (a ^ Nat.card χ.range) = Nat.card χ.range := by
    unfold UpperTheory.V.Kum.ordv at ha1 ⊢
    rw [map_pow, toAdd_pow, nsmul_eq_mul, ← mul_neg, ha1, mul_one]
  have hdv := UpperTheory.V.Kum.dvdOfIne ℚ Ω M A v (ρ ^ Nat.card χ.range) (a ^ Nat.card χ.range) hvA
    (by
      rw [← pow_mul, mul_comm, pow_mul, hρ]
      simp [a]) hfixd
  rw [hpow] at hdv
  have hMd : M ∣ Nat.card χ.range := by exact_mod_cast hdv
  have hMle : M ≤ Nat.card χ.range := Nat.le_of_dvd hd0 hMd
  have hcard : Nat.card χ.range ≤ Nat.card (rootsOfUnity M Ω) := Subgroup.card_le_of_le hle
  have heq : χ.range = rootsOfUnity M Ω :=
    Subgroup.eq_of_le_of_card_ge hle (le_trans (card_rootsOfUnity Ω M) hMle)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hζ
    exact zero_ne_one hζ
  have hu : Units.mk0 ζ hζ0 ∈ rootsOfUnity M Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  rw [← heq] at hu
  obtain ⟨g, hg⟩ := hu
  refine ⟨g, g.2, ?_⟩
  have h2 := congrArg Units.val hg
  rw [hχ, Units.val_mk0, div_eq_iff hρ0] at h2
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolInit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolInit :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F r a : ℕ) [NeZero M] [NeZero F] (hM : M ∣ F), r.Prime → r.Coprime F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω F, h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F 1 ζ δ a y κ → ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ k : (ZMod F)ˣ → ℤ, HasOrd F r A₀ (opP δ a y) k →
    ∀ ρ : Ω, ρ ^ M = (r : Ω) → ∀ t ∈ Ine (F := ℚ) A₀, t ρ = ζ * ρ → ∀ (c : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F c σ →
    κ (σ⁻¹ * t * σ) * ZMod.castHom hM (ZMod M) (c : ZMod F) = (k c : ZMod M) := by
  intro Ω _ _ _ M F r a _ _ hM hr hrF ζ hζ δ hδ y hy0 hyfix κ hκ A₀ hA₀ k hk ρ hρ t ht htρ c σ hσ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hM0 : M ≠ 0 := NeZero.ne M
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hFr : F.Coprime r := hrF.symm
  have hMr : M.Coprime r := (hrF.coprime_dvd_right hM).symm
  have hnotF : ¬ Over A₀ F := fun h => pb.2.2.2.1 A₀ F r hFr h hA₀
  have hnotM : ¬ Over A₀ M := fun h => pb.2.2.2.1 A₀ M r hMr h hA₀
  have hIneF : Ine (F := ℚ) A₀ ≤ fixMu ℚ Ω F := pb.2.2.2.2.1 A₀ F hnotF
  have hconj : ∀ (h τ : G ℚ Ω), h ∈ fixMu ℚ Ω F → τ⁻¹ * h * τ ∈ fixMu ℚ Ω F := by
    intro h τ hh x hx
    have h1 : h (τ x) = τ x := hh _ (by rw [← map_pow, hx, map_one])
    simp [AlgEquiv.mul_apply, h1]
  have htF : t ∈ fixMu ℚ Ω F := hIneF ht
  have hg : σ⁻¹ * t * σ ∈ fixMu ℚ Ω F := hconj t σ htF
  obtain ⟨Y, hYM, hK⟩ := hκ
  obtain ⟨z, -, hzM, hζκ⟩ := hK _ hg
  rw [hyfix _ hg, div_self hy0] at hzM
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hzM
    exact zero_ne_one hzM
  have hPz : opP δ a z = 1 := by
    unfold opP
    rw [hδ z hzM, div_self (pow_ne_zero _ hz0)]
  rw [hPz, div_one] at hζκ
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hYM
    exact hy0 hYM.symm
  set w := opP δ a Y with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    unfold opP
    exact div_ne_zero (by simpa using hY0) (pow_ne_zero _ hY0)
  have hζF : ζ ^ F = 1 := (hζ.pow_eq_one_iff_dvd F).mpr hM
  have hσζ : σ ζ = ζ ^ (c : ZMod F).val := hσ ζ hζF
  have h1 : ζ ^ ((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val) = t (σ w) / σ w := by
    rw [pow_mul, ← hσζ, ← map_pow, hζκ, map_div₀]
    congr 1
    simp [AlgEquiv.mul_apply]
  set W := σ w with hW
  have hW0 : W ≠ 0 := by simpa [hW] using hw0
  have hWM : W ^ M = σ (opP δ a y) := by
    rw [hW, ← map_pow, hw]
    unfold opP
    rw [div_pow, ← map_pow, ← pow_mul, mul_comm a M, pow_mul, hYM]
  have hPfix : ∀ h ∈ fixMu ℚ Ω F, h (opP δ a y) = opP δ a y := by
    intro h hh
    unfold opP
    rw [map_div₀, map_pow, hyfix h hh]
    congr 1
    have h2 := congrArg δ (hyfix _ (hconj h δ hh))
    simpa [AlgEquiv.mul_apply] using h2
  have hXt : t (σ (opP δ a y)) = σ (opP δ a y) := by
    have h2 := congrArg σ (hPfix _ hg)
    simpa [AlgEquiv.mul_apply] using h2
  set e := W / ρ ^ (k c) with he
  have heM : e ^ M = σ (opP δ a y) / (r : Ω) ^ (k c) := by
    rw [he, div_pow, hWM, ← zpow_natCast (ρ ^ k c) M, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]
  have hvr0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have hveM : A₀.valuation e ^ M = 1 := by
    rw [← map_pow, heM, map_div₀, map_zpow₀, hk c σ hσ, div_self (zpow_ne_zero _ hvr0)]
  have hve : A₀.valuation e = 1 := by
    rcases lt_trichotomy (A₀.valuation e) 1 with hlt | heq | hgt
    · exact absurd hveM (ne_of_lt (pow_lt_one₀ zero_le' hlt hM0))
    · exact heq
    · exact absurd hveM (ne_of_gt (one_lt_pow₀ hgt hM0))
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hve
    exact zero_ne_one hve
  have hteM : (t e / e) ^ M = 1 := by
    have hX0 : σ (opP δ a y) / (r : Ω) ^ (k c) ≠ 0 := by
      rw [← heM]
      exact pow_ne_zero M he0
    rw [div_pow, ← map_pow, heM, map_div₀, hXt, map_zpow₀, map_natCast]
    exact div_self hX0
  have hin : A₀.valuation (t e - e) < 1 := ht.2 e hve.le
  have hte1 : A₀.valuation (t e / e - 1) < 1 := by
    rw [div_sub_one he0, map_div₀, hve, div_one]
    exact hin
  have hte : t e = e := by
    have h3 := pb.2.2.2.2.2.1 A₀ M (t e / e) hnotM hteM hte1
    rwa [div_eq_one_iff_eq he0] at h3
  have hWe : W = e * ρ ^ (k c) := by
    rw [he, div_mul_cancel₀ _ (zpow_ne_zero _ hρ0)]
  have htW : t W / W = ζ ^ (k c) := by
    rw [div_eq_iff hW0]
    conv_lhs => rw [hWe]
    rw [map_mul, map_zpow₀, hte, htρ, mul_zpow, hWe]
    ring
  rw [htW, ← zpow_natCast] at h1
  have hdvd : (M : ℤ) ∣ (k c) - (((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val : ℕ) : ℤ) := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hM0), ← h1, div_self (zpow_ne_zero _ (hζ.ne_zero hM0))]
  have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mpr hdvd
  push_cast at h4
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← h4, ZMod.natCast_zmod_val, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ZSumPKey
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem zSumP_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (F : ℕ) [NeZero F] (t d : (ZMod F)ˣ) (g h k : G ℚ Ω)
    (hg : Lifts F t g) (hh : Lifts F d h) (hk : Lifts F (t * d) k) : k⁻¹ * (g * h) ∈ fixMu ℚ Ω F := by
  have hg' : ∀ x : Ω, x ^ F = 1 → g x = x ^ (t : ZMod F).val := hg
  have hh' : ∀ x : Ω, x ^ F = 1 → h x = x ^ (d : ZMod F).val := hh
  have hk' : ∀ x : Ω, x ^ F = 1 → k x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val := hk
  show ∀ x : Ω, x ^ F = 1 → (k⁻¹ * (g * h)) x = x
  intro x hx
  have hgh : (g * h) x = k x := by
    rw [AlgEquiv.mul_apply, hh' x hx, map_pow, hg' x hx, ← pow_mul, hk' x hx, Units.val_mul, ZMod.val_mul]
    conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  rw [AlgEquiv.mul_apply, hgh, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.ML.zSumP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (F a : ℕ) [NeZero F] (I : O) (α : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, I ∣ (α g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ (k : (ZMod F)ˣ → ℤ), (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → I ∣ zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k) ∧
    ∀ n : ℤ, zSum α σ (fun t => n * k t) = n * zSum α σ k := by
  intro Ω _ _ _ O _ F a _ I α hI σ hσ k
  refine ⟨fun d δ hδ => ?_, fun n => ?_⟩
  · have hre : ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) = ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O) :=
      (Fintype.sum_equiv (Equiv.mulRight d) _ _ (fun t => rfl)).symm
    have h1 : zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) := by
      simp only [zSum, Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    have h2 : ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) * (1 - (α ((σ (t * d))⁻¹ * (σ t * δ)) : O)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hu : (((α (σ t))⁻¹ : Oˣ) : O) * (α (σ t) : O) = 1 := Units.inv_mul _
      simp only [map_mul, map_inv, Units.val_mul]
      linear_combination ((α δ : O) * (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)) * hu
    rw [h1, hre, h2]
    refine Finset.dvd_sum fun t _ => Dvd.dvd.mul_left ?_ _
    exact dvd_sub_comm.mp (hI _ (zSumP_key F t d (σ t) δ (σ (t * d)) (hσ t) hδ (hσ (t * d))))
  · simp only [zSum, Int.cast_mul, mul_assoc, Finset.mul_sum]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.HasOrdP
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.hasOrdP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (F r a : ℕ) [NeZero F], r ≠ 0 → ∀ (A₀ : ValuationSubring Ω) (u : Ω) (k : (ZMod F)ˣ → ℤ), HasOrd F r A₀ u k →
    (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → HasOrd F r A₀ (opP δ a u) fun t => k (t * d) - a * k t) ∧ ∀ n : ℕ, HasOrd F r A₀ (u ^ n) fun t => n * k t := by
  intro Ω _ _ _ F r a _ hr A₀ u k hk
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hv0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hr)
  have hk' : ∀ (t : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F t σ → A₀.valuation (σ u) = A₀.valuation (r : Ω) ^ k t := hk
  refine ⟨fun d δ hδ t σ hσ => ?_, fun n t σ hσ => ?_⟩
  · have hδ' : ∀ x : Ω, x ^ F = 1 → δ x = x ^ (d : ZMod F).val := hδ
    have hσ' : ∀ x : Ω, x ^ F = 1 → σ x = x ^ (t : ZMod F).val := hσ
    have hσδ : Lifts F (t * d) (σ * δ) := by
      show ∀ x : Ω, x ^ F = 1 → (σ * δ) x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val
      intro x hx
      rw [AlgEquiv.mul_apply, hδ' x hx, map_pow, hσ' x hx, ← pow_mul, Units.val_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
      rw [pow_add, pow_mul, hx, one_pow, mul_one]
    have h1 := hk' (t * d) (σ * δ) hσδ
    have h2 := hk' t σ hσ
    rw [AlgEquiv.mul_apply] at h1
    show A₀.valuation (σ (δ u / u ^ a)) = _
    rw [map_div₀, map_pow, map_div₀, map_pow, h1, h2, ← zpow_natCast, ← zpow_mul, zpow_sub₀ hv0, mul_comm (k t)]
  · show A₀.valuation (σ (u ^ n)) = _
    rw [map_pow, map_pow, hk' t σ hσ, ← zpow_natCast, ← zpow_mul, mul_comm (k t)]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem exists_cycZ_eq_add_pow_mul_of_pows (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m k : ℕ) (g : G ℚ Ω) (hg : Pows (l ^ m) k g) : ∃ e : ℤ_[l], (cycZ ℚ Ω l g : ℤ_[l]) = k + (l : ℤ_[l]) ^ m * e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := hg ζ hζ.pow_eq_one
  have h3 : ζ ^ k = ζ ^ ((PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l])).val) := h2.symm.trans h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h3
  have h4 : (k : ZMod (l ^ m)) = PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l]) := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l])), ZMod.natCast_eq_natCast_iff]
    exact h3
  have h5 : (cycZ ℚ Ω l g : ℤ_[l]) - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, ← h4, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h5
  obtain ⟨e, he⟩ := h5
  exact ⟨e, by rw [← he]; ring⟩

private theorem isUnit_add_pow_mul_of_isUnit_of_one_le (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (m : ℕ) (hm : 1 ≤ m) (u y : O) (hu : IsUnit u) : IsUnit (u + (l : O) ^ m * y) := by
  by_contra h
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hlu
    have h1 : IsUnit (algebraMap ℤ_[l] O (l : ℤ_[l])) := by rwa [map_natCast]
    have h2 := (isUnit_map_iff (algebraMap ℤ_[l] O) _).mp h1
    rw [PadicInt.isUnit_iff, PadicInt.norm_p] at h2
    have h3 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h4 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h3
    rw [h2] at h4
    exact lt_irrefl _ h4
  have h1 : u + (l : O) ^ m * y ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact h
  have h5 : (l : O) ^ m * y ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, mul_assoc]
    exact Ideal.mul_mem_right _ _ hl
  have h6 : u ∈ IsLocalRing.maximalIdeal O := by
    have := Ideal.sub_mem _ h1 h5
    simpa using this
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h6
  exact h6 hu

private theorem intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (N : ℕ) (v : W) (hv : N • v = 0) (z₁ z₂ : ℤ) (h : (z₁ : ZMod N) = z₂) : (z₁ : O) • v = (z₂ : O) • v := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨j, hj⟩ := h
  rw [← sub_eq_zero, ← sub_smul, ← Int.cast_sub, ← neg_sub, hj]
  rw [Int.cast_neg, neg_smul, neg_eq_zero, Int.cast_mul, mul_comm, mul_smul, Int.cast_natCast, Nat.cast_smul_eq_nsmul, hv, smul_zero]

private theorem isUnit_natCast_of_not_dvd' (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : O) := by
  have h1 : IsUnit (n : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (((Fact.out : l.Prime).coprime_iff_not_dvd).mpr h))
  simpa using h1.map (algebraMap ℤ_[l] O)

theorem UpperTheory.V.ML.nuSysEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F r b : ℕ) [NeZero F] (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → r.Prime → r ≡ 1 [MOD F] → b < F →
    ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) → ∀ w : QO l O, (l ^ m) • w = 0 →
    ∃ ν : List ℕ → G ℚ Ω → QO l O, NuSys l (l ^ m) F r (dualChar l α) A₀ (zVal α σ b • w) ν := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F r b _ α hD hr hrF hb A₀ hA₀ σ hσ w hw
  classical
  obtain ⟨hl2, hcop, hm, hF, htriv, hodd, ⟨g0, hg0⟩⟩ := hD
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast hl.ne_zero⟩
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hMF : l ^ m ∣ F := hF ▸ dvd_mul_left _ _
  have hF0 : F ≠ 0 := NeZero.ne F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  obtain ⟨a0, ha0⟩ := (galBasic Ω (l ^ m) (pow_ne_zero _ hl.ne_zero)).2.2.2.2.1 g0
  have hPows : Pows (l ^ m) (a0 : ZMod (l ^ m)).val g0 := ha0
  obtain ⟨e0, he0⟩ := exists_cycZ_eq_add_pow_mul_of_pows Ω l m _ g0 hPows
  obtain ⟨X, s, hLax, hOrd⟩ := laxEx Ω l F r b hl hr hrF hb A₀ hA₀
  have hSys := sysOfLax Ω l N₀ m F r _ hl hl2 hcop hm hF X s hLax g0 hPows
  let τ : ℕ → G ℚ Ω := fun q => if h : q.Prime then Classical.choose (ineTau Ω q h).2 else 1
  have hτ : ∀ q, q.Prime → IsTau q (τ q) := by
    intro q hq
    simp only [τ, dif_pos hq]
    exact Classical.choose_spec (ineTau Ω q hq).2
  have hkol : ∀ L, AdmL l F r L → ∃ κ : G ℚ Ω → ZMod (l ^ m), IsKol (l ^ m) F L.prod ζ g0 (a0 : ZMod (l ^ m)).val (der τ L ((fun d => opP g0 (a0 : ZMod (l ^ m)).val (X d) ^ (2 * N₀ * d)) L.prod)) κ := by
    intro L hL
    obtain ⟨hAdm, hprod0, -, -⟩ := isCrys_isDR_prod l F r L hL
    have hD := derBasic Ω (F * L.prod) r (mul_ne_zero hF0 hprod0) τ L _ (hSys.ne _ hAdm) (hSys.fix _ hAdm)
    exact kolEx Ω (l ^ m) F L.prod _ (mul_ne_zero hF0 hprod0) ζ hζ g0 hPows _ hD.1 hD.2.1
      (derInv Ω l (l ^ m) F r hF0 hMF _ _ hSys τ L hL (fun q hq => hτ q (hL.2 q hq).1))
  let κ : List ℕ → G ℚ Ω → ZMod (l ^ m) := fun L => if h : AdmL l F r L then Classical.choose (hkol L h) else 0
  have hκ : ∀ L (h : AdmL l F r L), IsKol (l ^ m) F L.prod ζ g0 (a0 : ZMod (l ^ m)).val (der τ L ((fun d => opP g0 (a0 : ZMod (l ^ m)).val (X d) ^ (2 * N₀ * d)) L.prod)) (κ L) := by
    intro L h
    simp only [κ, dif_pos h]
    exact Classical.choose_spec (hkol L h)
  have hchiO : ∀ (g : G ℚ Ω) (k : ℕ), Pows (l ^ m) k g → ∃ e : O, ((chiO ℚ Ω l O g : Oˣ) : O) = k + (l : O) ^ m * e := by
    intro g k hg
    obtain ⟨e, he⟩ := exists_cycZ_eq_add_pow_mul_of_pows Ω l m k g hg
    refine ⟨algebraMap ℤ_[l] O e, ?_⟩
    show algebraMap ℤ_[l] O (cycZ ℚ Ω l g : ℤ_[l]) = _
    rw [he, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast]
  have hβ : ∀ g ∈ fixMu ℚ Ω F, ((l ^ m : ℕ) : O) ∣ ((dualChar l α g : Oˣ) : O) - 1 := by
    intro g hg
    have hP : Pows (l ^ m) 1 g := by
      intro y hy
      rw [pow_one]
      exact ((galBasic Ω F hF0).2.2.2.2.2.2.2.2.1 (l ^ m) hMF) hg y hy
    obtain ⟨e, he⟩ := hchiO g 1 hP
    obtain ⟨c, hc⟩ := htriv g hg
    have hinv : ((α g)⁻¹ : Oˣ) * (α g : O) = 1 := Units.inv_mul _
    refine ⟨((α g)⁻¹ : Oˣ) * (e - c), ?_⟩
    show ((chiO ℚ Ω l O g : Oˣ) : O) * ((α g)⁻¹ : Oˣ) - 1 = _
    rw [he, Nat.cast_pow, Nat.cast_one]
    linear_combination hinv - (((α g)⁻¹ : Oˣ) : O) * hc
  refine ⟨fun L => nu (dualChar l α) σ w (κ L), ⟨?_, ?_, ?_⟩⟩
  · intro L hL
    obtain ⟨hAdm, hprod0, -, -⟩ := isCrys_isDR_prod l F r L hL
    have hD := derBasic Ω (F * L.prod) r (mul_ne_zero hF0 hprod0) τ L _ (hSys.ne _ hAdm) (hSys.fix _ hAdm)
    have hK := hκ L hL
    have hH := kolHom Ω (l ^ m) F L.prod _ (mul_ne_zero hF0 hprod0) hMF ζ hζ g0 hPows _ hD.1 hD.2.1 (κ L) hK
    have hU := kolUnr Ω (l ^ m) F L.prod r _ (mul_ne_zero hF0 hprod0) hMF ζ hζ g0 hPows _ hD.1 hD.2.1
      (hD.2.2.2.1 (hSys.unit _ hAdm)) (κ L) hK
    exact nuIs Ω O (QO l O) (l ^ m) F (F * r * L.prod) ⟨r * L.prod, by ring⟩ (dualChar l α) hβ σ hσ w hw
      (κ L) hH.1 hH.2.1 hU
  · intro q L hqL A hA φ hφ
    have hq : q.Prime := (hqL.2 q List.mem_cons_self).1
    have hL : AdmL l F r L :=
      ⟨(List.nodup_cons.mp hqL.1).2, fun p hp => hqL.2 p (List.mem_cons_of_mem _ hp)⟩
    obtain ⟨hAdmq, -, -, -⟩ := isCrys_isDR_prod l F r (q :: L) hqL
    rw [List.prod_cons] at hAdmq
    have hcopq : ¬ l ∣ q * s L.prod q := hSys.cop L.prod q hq hAdmq
    have hUn : IsUnit (((-((q * s L.prod q : ℕ) : ℤ) : ℤ) : O)) := by
      rw [Int.cast_neg, IsUnit.neg_iff, Int.cast_natCast]
      exact isUnit_natCast_of_not_dvd' l O _ hcopq
    obtain ⟨b0, -, hb0⟩ := (hτ q hq).2
    obtain ⟨t, htI, ht⟩ := (ineTau Ω q hq).1 A hA b0
    refine ⟨t, htI, hUn.unit, ?_⟩
    simp only [nu, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    have pb := (placeBasic Ω).2.2.2.2.2.2.2.2.2 A (σ c)⁻¹
    have hA' : Over ((σ c)⁻¹ • A) q := by
      have h1 := (pb.2.2.2.1 (q : Ω)).mpr hA
      rwa [map_natCast] at h1
    have hI' : (σ c)⁻¹ * t * σ c ∈ Ine ((σ c)⁻¹ • A) := by
      rw [pb.2.1]
      simpa [mul_assoc] using htI
    have hφ' : IsFrob ((σ c)⁻¹ • A) q ((σ c)⁻¹ * φ * σ c) := by
      rw [pb.2.2.1]
      simpa [mul_assoc] using hφ
    have ht' : ∀ y : Ω, y ^ q = 1 → ((σ c)⁻¹ * t * σ c) y = (τ q) y := by
      intro y hy
      have hcomm := (galBasic Ω q hq.ne_zero).2.2.2.2.2.1 y (fun g hg => hg y hy) t (σ c)
      have hback : (σ c)⁻¹ (σ c (t y)) = t y := by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, hback]
      exact (ht y hy).trans (hb0 y hy).symm
    have key := kolStep Ω l (l ^ m) F r _ hF0 hMF hr ζ hζ g0 hPows _ _ hSys τ q L hqL
      (fun p hp => hτ p (hqL.2 p hp).1) (κ L) (κ (q :: L)) (hκ L hL) (hκ (q :: L) hqL)
      ((σ c)⁻¹ • A) hA' _ hI' ht' _ hφ'
    rw [key]
    have hv : (l ^ m) • ((((dualChar l α) (σ c) : Oˣ) : O) • w) = 0 := by
      rw [smul_comm, hw, smul_zero]
    generalize ((((dualChar l α) (σ c) : Oˣ) : O) • w) = v at hv ⊢
    generalize κ L ((σ c)⁻¹ * φ * σ c) = k
    rw [IsUnit.unit_spec, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul]
    have h3 := intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero O _ (l ^ m) v hv
      (((-(((q * s L.prod q : ℕ) : ZMod (l ^ m)) * k)).val : ℕ) : ℤ)
      (-((q * s L.prod q : ℕ) : ℤ) * (k.val : ℤ)) (by push_cast; simp)
    push_cast at h3 ⊢
    exact h3
  · have hL0 : AdmL l F r [] := ⟨List.nodup_nil, fun p hp => absurd hp List.not_mem_nil⟩
    obtain ⟨hAdm1, -, -, -⟩ := isCrys_isDR_prod l F r [] hL0
    have hx0 := hSys.ne _ hAdm1
    have hxfix := hSys.fix _ hAdm1
    have hK0 := hκ [] hL0
    simp only [List.prod_nil] at hAdm1 hx0 hxfix hK0
    have hrcop : r.Coprime F := by
      have := hrF.gcd_eq
      rw [Nat.gcd_one_left] at this
      exact this
    have hMr : (l ^ m).Coprime r := (Nat.Coprime.coprime_dvd_right hMF hrcop).symm
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (r : Ω) (pow_pos hl.pos m)
    obtain ⟨t, htI, htρ⟩ := ineRad Ω r (l ^ m) hr hMr A₀ hA₀ ρ ζ hρ hζ.pow_eq_one
    obtain ⟨d, hd⟩ := (galBasic Ω F hF0).2.2.2.2.1 g0
    have hO := hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ (X 1) _ hOrd
    have hO1 := hO.1 d g0 hd
    have hO2 := ((hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ _ _ hO1).2 (2 * N₀ * 1))
    have hO3 := ((hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ _ _ hO2).1 d g0 hd)
    have hinit := kolInit Ω (l ^ m) F r (a0 : ZMod (l ^ m)).val hMF hr hrcop ζ hζ g0 hPows _ hx0
      (by simpa using hxfix) (κ []) hK0 A₀ hA₀ _ hO3 ρ hρ t htI htρ
    obtain ⟨e1, he1⟩ := hchiO g0 _ hPows
    have hU1 : IsUnit (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) := by
      have heq : ((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O) =
          (((α g0 : Oˣ) : O) - ((chiO ℚ Ω l O g0 : Oˣ) : O)) + (l : O) ^ m * e1 := by
        linear_combination he1
      rw [heq]
      exact isUnit_add_pow_mul_of_isUnit_of_one_le l O m hm _ _ hg0
    have hU2 : IsUnit (((2 * N₀ * 1 : ℕ) : ℤ) : O) := by
      rw [Int.cast_natCast]
      apply isUnit_natCast_of_not_dvd' l O
      intro hdvd
      rw [mul_one] at hdvd
      rcases (Nat.Prime.dvd_mul hl).mp hdvd with h2 | h2
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)
      · exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h2)
    have hU := (hU1.pow 2).mul hU2
    refine ⟨t, htI, hU.unit, ?_⟩
    rw [IsUnit.unit_spec]
    have hwO : ((l : O) ^ m) • w = 0 := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hw]
    have hsum : ∀ K : (ZMod F)ˣ → ℤ, (∀ (c : (ZMod F)ˣ) (σ' : G ℚ Ω), Lifts F c σ' →
        κ [] (σ'⁻¹ * t * σ') * (ZMod.castHom hMF (ZMod (l ^ m))) (c : ZMod F) = K c) →
        nu (dualChar l α) σ w (κ []) t = zSum α σ K • w := by
      intro K hK
      simp only [nu, zSum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro c _
      have hc := hK c (σ c) (hσ c)
      have hP : Pows (l ^ m) ((c : ZMod F).val) (σ c) := by
        intro y hy
        apply hσ c y
        obtain ⟨j, hj⟩ := hMF
        rw [hj, pow_mul, hy, one_pow]
      obtain ⟨e, he⟩ := hchiO (σ c) _ hP
      have hv : (l ^ m) • ((((α (σ c))⁻¹ : Oˣ) : O) • w) = 0 := by
        rw [smul_comm, hw, smul_zero]
      show (κ [] ((σ c)⁻¹ * t * σ c)).val • ((((chiO ℚ Ω l O (σ c)) * (α (σ c))⁻¹ : Oˣ) : O) • w) = _
      have hz : ((l : O) ^ m * e) • ((((α (σ c))⁻¹ : Oˣ) : O) • w) = 0 := by
        rw [mul_comm, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul O (l ^ m), hv, smul_zero]
      rw [Units.val_mul, mul_smul, he, add_smul, hz, add_zero]
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul]
      have h3 := intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero O _ (l ^ m) _ hv (((κ [] ((σ c)⁻¹ * t * σ c)).val : ℤ) * ((c : ZMod F).val : ℤ)) (K c)
        (by rw [← hc, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val])
      push_cast at h3
      exact h3.trans (mul_smul _ _ _).symm
    rw [hsum _ hinit]
    have zp := fun k => zSumP Ω O F (a0 : ZMod (l ^ m)).val ((l : O) ^ m) α htriv σ hσ k
    obtain ⟨j1, hj1⟩ := (zp (fun t : (ZMod F)ˣ => th F b ↑t)).1 d g0 hd
    have h2 := (zp (fun t : (ZMod F)ˣ => th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t)).2
      ((2 * N₀ * 1 : ℕ) : ℤ)
    obtain ⟨j3, hj3⟩ := (zp (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) *
      (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))).1 d g0 hd
    have E := hj3
    rw [h2] at E
    have E2 : zSum α σ (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d * d) -
        ↑(a0 : ZMod (l ^ m)).val * th F b ↑(t * d)) - ↑(a0 : ZMod (l ^ m)).val *
        (((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))) =
        (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) ^ 2 * (((2 * N₀ * 1 : ℕ) : ℤ) : O) *
          zVal α σ b + (l : O) ^ m * ((((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) *
          (((2 * N₀ * 1 : ℕ) : ℤ) : O) * j1 + j3) := by
      linear_combination E + (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) * (((2 * N₀ * 1 : ℕ) : ℤ) : O) * hj1
    show zSum α σ (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d * d) -
        ↑(a0 : ZMod (l ^ m)).val * th F b ↑(t * d)) - ↑(a0 : ZMod (l ^ m)).val *
        (((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))) • w = _
    rw [E2, add_smul, mul_comm ((l : O) ^ m) _, mul_smul _ ((l : O) ^ m), hwO, smul_zero, add_zero, mul_smul]
