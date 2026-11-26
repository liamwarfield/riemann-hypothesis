module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdIffIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem gdIff_pow {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (χ η : Γ →* Oˣ) {n : ℕ} (hn : n ≠ 0)
    (hχ : ∀ g, χ g ^ n = 1) (h : ∀ g, χ g = 1 → η g = 1) : ∃ j : ℕ, ∀ g, η g = χ g ^ j := by
  classical
  haveI : NeZero n := ⟨hn⟩
  have hle : χ.range ≤ rootsOfUnity n O := by
    rintro _ ⟨g, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (hχ g)
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := χ.range)
  obtain ⟨g0, hg0⟩ := x.2
  have hpow : ∀ g, ∃ k : ℕ, χ g = χ g0 ^ k := by
    intro g
    obtain ⟨k, hk⟩ : (⟨χ g, g, rfl⟩ : χ.range) ∈ Submonoid.powers x :=
      mem_powers_iff_mem_zpowers.mpr (hx _)
    refine ⟨k, ?_⟩
    have e : ((x ^ k : χ.range) : Oˣ) = χ g := congrArg Subtype.val hk
    rw [SubmonoidClass.coe_pow, ← hg0] at e
    exact e.symm
  have hord : orderOf (χ g0) ≠ 0 :=
    (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hχ g0⟩)).ne'
  haveI : NeZero (orderOf (χ g0)) := ⟨hord⟩
  have hηm : η g0 ∈ rootsOfUnity (orderOf (χ g0)) O := by
    rw [mem_rootsOfUnity, ← map_pow]
    apply h
    rw [map_pow, pow_orderOf_eq_one]
  obtain ⟨j, -, hj⟩ := (IsPrimitiveRoot.orderOf (χ g0)).eq_pow_of_mem_rootsOfUnity hηm
  refine ⟨j, fun g => ?_⟩
  obtain ⟨k, hk⟩ := hpow g
  have hker : χ (g * (g0 ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, map_pow, hk, mul_inv_cancel]
  have hη := h _ hker
  rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at hη
  rw [hη, hk, ← hj, ← pow_mul, ← pow_mul, mul_comm]

private theorem gdIff_sign {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [CharZero O] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ η : Γ →* Oˣ, η.ker = H ∧ ∀ g, η g ^ 2 = 1 := by
  classical
  have hne : (-1 : Oˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun u : Oˣ => (u : O)) h1
    simp only [Units.val_neg, Units.val_one] at h2
    have h3 : (2 : O) = 0 := by linear_combination -h2
    exact two_ne_zero h3
  let η : Γ →* Oˣ :=
    { toFun := fun g => if g ∈ H then 1 else -1
      map_one' := by simp [H.one_mem]
      map_mul' := by
        intro a b
        by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;>
          simp [ha, hb, Subgroup.mul_mem_iff_of_index_two h] }
  refine ⟨η, ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker]
    by_cases hg : g ∈ H
    · simp [η, hg]
    · simp [η, hg, hne]
  · intro g
    by_cases hg : g ∈ H
    · simp [η, hg]
    · simp [η, hg]

private theorem gdIff_index (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] :
    (galOf ℚ K Ω).index = Module.finrank ℚ K := by
  have : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (galEmbTop ℚ K Ω).2.2

theorem UpperTheory.V.HV.gdIff :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e N : ℕ) [NeZero N]
      (ψ : DirichletCharacter c.O N), (GD Ω K l e ψ ↔ ∃ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a) ∧
        ∀ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a → Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ := by
  intro Ω _ _ _ K _ _ _ l _ c e N _ ψ
  have hl : l.Prime := Fact.out
  obtain ⟨A0, hA0⟩ := (Chr.placesQ Ω).1 l hl
  have F1 : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w →
      (∀ χ1 χ2 : DirichletCharacter c.O N,
        Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2) ∧
      (∀ χ : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ⁻¹ = (Chr.dirG ℚ Ω χ)⁻¹) ∧
      (∀ χ1 χ2 : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ1 = Chr.dirG ℚ Ω χ2 → χ1 = χ2) ∧
      Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := by
    intro w hw
    have hm : ∀ χ1 χ2 : DirichletCharacter c.O N,
        Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2 :=
      fun χ1 χ2 => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).1
    have h1 : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := by
      have := hm 1 1
      rw [mul_one] at this
      exact (mul_left_cancel (a := Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N))
        (by rw [mul_one]; exact this)).symm
    refine ⟨hm, fun χ => ?_, fun χ1 χ2 h => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).2 h, h1⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, inv_mul_cancel, h1]
  have Uq : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w → ∀ u v : ℕ, u < l - 1 → v < l - 1 →
      (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v := by
    intro w hw
    have OM := (omT Ω l c).2 w hw
    have key : ∀ u v : ℕ, u < l - 1 → v < l - 1 → u ≤ v →
        (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v := by
      intro u v hu hv huv h
      have hd : l - 1 ∣ v - u := OM.2.2.2.2.2.2.1 A0 hA0 (v - u) (fun σ hσ => by
        rw [MonoidHom.mem_ker]
        show w σ ^ (v - u) = 1
        have := h σ hσ
        rw [← Nat.add_sub_cancel' huv, pow_add] at this
        exact mul_left_cancel (this.symm.trans (mul_one _).symm))
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    intro u v hu hv h
    rcases le_total u v with huv | huv
    · exact key u v hu hv huv h
    · exact (key v u hv hu huv (fun σ hσ => (h σ hσ).symm)).symm
  have TH : ¬ l ∣ orderOf ψ → th0 l ψ = ψ := by
    intro hord
    exact ((partOrd (DirichletCharacter c.O N) l hl ψ
      (Nat.pos_of_ne_zero (fun h0 => hord (h0 ▸ dvd_zero l)))).2.2.2.2.2.1 hord).2
  have HC : ∀ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a →
      Chr.dirG ℚ Ω (comp l ψ) = w ^ a ∧
      Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ ∧ ¬ l ∣ orderOf ψ := by
    intro w η a hL
    obtain ⟨hm, hinv, -, -⟩ := F1 w hL.om
    have hord : ¬ l ∣ orderOf ψ := by
      rw [← (psiBar Ω l c w hL.om N ψ).2.2.1]
      exact hL.ord
    have hth := TH hord
    obtain ⟨b, hb, hcb, -⟩ := (psiBar Ω l c w hL.om N ψ).1
    rw [hth] at hcb
    have hab : a = b := Uq w hL.om a b hL.a_lt hb (fun σ hσ => by
      have e1 := hL.ine A0 hA0 σ hσ
      have e2 := ((compIne Ω N l hl A0 hA0).2 c.O ψ).1 σ hσ
      rw [hcb] at e2
      exact e1.symm.trans e2)
    subst hab
    refine ⟨hcb, ?_, hord⟩
    unfold chiP
    rw [hth, hm, hinv, hcb]
  refine ⟨⟨?_, ?_⟩, fun w η a hL => (HC w η a hL).2.1⟩
  · intro hG
    obtain ⟨⟨w, hw, -⟩, -⟩ := omT Ω l c
    obtain ⟨hm, hinv, -, h1⟩ := F1 w hw
    have OM := (omT Ω l c).2 w hw
    have hord := hG.ord
    have hth := TH hord
    obtain ⟨b, hb, hcb, -⟩ := (psiBar Ω l c w hw N ψ).1
    rw [hth] at hcb
    have hidx : (galOf ℚ K Ω).index = 2 := by rw [gdIff_index, hG.quad]
    obtain ⟨η, hηk, hη2⟩ := gdIff_sign (O := c.O) (galOf ℚ K Ω) hidx
    have hχ' : Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹ := by
      unfold chiP
      rw [hth, hm, hinv, hcb]
    have h2b : l - 1 ∣ 2 * b := by
      rw [← OM.2.2.1]
      apply orderOf_dvd_of_pow_eq_one
      have : Chr.dirG ℚ Ω (comp l ψ ^ 2) = 1 := by rw [hG.ine, h1]
      rw [pow_two, hm, hcb, ← pow_add, ← two_mul] at this
      exact this
    refine ⟨w, η, b, ⟨hw, hηk, hG.l_odd, hG.e_pos, hG.N_even, ?_, ?_, hb, h2b, ?_, hG.quad, hG.imag,
      hG.l_cop, hG.cop, ?_, ?_⟩⟩
    · rw [(psiBar Ω l c w hw N ψ).2.2.1]
      exact hord
    · intro A hA σ hσ
      change Chr.dirG ℚ Ω ψ σ = (w ^ b) σ
      rw [((compIne Ω N l hl A hA).2 c.O ψ).1 σ hσ, hcb]
    · intro σ hσ
      exact ((psiBar Ω l c w hw N ψ).2.1 e).mp hG.par σ hσ
    · intro i j hC
      apply hG.eta
      have hd1 : Chr.dirG ℚ Ω ψ ^ orderOf ψ = 1 := by
        rw [← (psiBar Ω l c w hw N ψ).2.2.1]
        exact pow_orderOf_eq_one _
      have hwS : w ∈ (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply,
          show 2 * ((l - 1) * orderOf ψ) = (l - 1) * (2 * orderOf ψ) by ring, pow_mul, hw.1, one_pow]
      have hψS : Chr.dirG ℚ Ω ψ ∈
          (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply,
          show 2 * ((l - 1) * orderOf ψ) = orderOf ψ * (2 * (l - 1)) by ring, pow_mul, hd1, one_pow]
      have hXS := Subgroup.mul_mem _ (Subgroup.pow_mem _ hwS i)
        (Subgroup.pow_mem _ (Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS b))) j)
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hXS
      have hηm : η ^ (2 * ((l - 1) * orderOf ψ)) = 1 := by
        refine MonoidHom.ext fun σ => ?_
        show η σ ^ (2 * ((l - 1) * orderOf ψ)) = 1
        rw [pow_mul, hη2, one_pow]
      have hlm : ¬ l ∣ 2 * ((l - 1) * orderOf ψ) := by
        intro hdiv
        rcases (Nat.Prime.dvd_mul hl).mp hdiv with h2 | h'
        · exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)
        · rcases (Nat.Prime.dvd_mul hl).mp h' with h3 | h4
          · have := hl.two_le
            have := Nat.le_of_dvd (by omega) h3
            omega
          · exact hord h4
      have heq := (congrFacts Ω l c).2.2.2.2 η _ _ hlm hηm hXS hC
      rw [← OM.1, hχ', ← hηk, heq]
      intro σ hσ
      obtain ⟨hσ1, hσ2⟩ := Subgroup.mem_inf.mp hσ
      rw [MonoidHom.mem_ker] at hσ1 hσ2 ⊢
      show w σ ^ i * ((Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹) σ) ^ j = 1
      rw [hσ2, hσ1, one_pow, one_pow, one_mul]
    · intro hd
      apply hG.gen
      exact (Nat.dvd_add_right h2b).mp (by rw [show 2 * b + 2 * e = 2 * (e + b) by ring]; exact hd)
  · rintro ⟨w, η, a, hL⟩
    obtain ⟨hm, hinv, hinj, h1⟩ := F1 w hL.om
    have OM := (omT Ω l c).2 w hL.om
    obtain ⟨hcomp, hχ', hord⟩ := HC w η a hL
    have h2a : w ^ (2 * a) = 1 := by
      obtain ⟨k, hk⟩ := hL.two_a
      rw [hk, pow_mul, hL.om.1, one_pow]
    refine ⟨hL.l_odd, hL.e_pos, hL.N_even, hord, ?_, ?_, hL.quad, hL.imag, hL.l_cop, hL.cop, ?_, ?_⟩
    · apply hinj
      rw [pow_two, hm, hcomp, h1, ← pow_add, ← two_mul, h2a]
    · exact ((psiBar Ω l c w hL.om N ψ).2.1 e).mpr hL.par
    · intro hle
      obtain ⟨χ', hχ'e⟩ : ∃ χ' : G ℚ Ω →* c.Oˣ, χ' = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ := ⟨_, rfl⟩
      rw [← OM.1, hχ', ← hχ'e] at hle
      have hn : orderOf (Chr.dirG ℚ Ω ψ) * (l - 1) ≠ 0 :=
        mul_ne_zero (fun h0 => hL.ord (h0 ▸ dvd_zero l)) (by have := hl.two_le; omega)
      have hwS : w ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_comm, pow_mul, hL.om.1, one_pow]
      have hψS : Chr.dirG ℚ Ω ψ ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_mul, pow_orderOf_eq_one, one_pow]
      have hχS : χ' ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [hχ'e]
        exact Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS a))
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hχS
      have hpowχ : ∀ g, (χ'.comp w.ker.subtype) g ^ (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) = 1 :=
        fun g => congrArg (fun f : G ℚ Ω →* c.Oˣ => f g) hχS
      have hker : ∀ g, (χ'.comp w.ker.subtype) g = 1 → (η.comp w.ker.subtype) g = 1 := by
        intro g hg
        have : (g : G ℚ Ω) ∈ η.ker := by
          rw [hL.eta_ker]
          exact hle ⟨g.2, hg⟩
        exact this
      obtain ⟨j, hj⟩ := gdIff_pow (χ'.comp w.ker.subtype) (η.comp w.ker.subtype) hn hpowχ hker
      have hθ : w.ker ≤ (η * (χ' ^ j)⁻¹).ker := by
        intro σ hσ
        rw [MonoidHom.mem_ker]
        show η σ * ((χ' σ) ^ j)⁻¹ = 1
        have := hj ⟨σ, hσ⟩
        rw [show η σ = χ' σ ^ j from this, mul_inv_cancel]
      obtain ⟨b', -, hb'⟩ := OM.2.2.2.2.2.2.2 _ hθ
      apply hL.eta b' j
      rw [← hχ'e]
      have heq : η = w ^ b' * χ' ^ j := by
        rw [← hb']
        exact (inv_mul_cancel_right η (χ' ^ j)).symm
      rw [← heq]
      exact (congrFacts Ω l c).1.refl _
    · intro hd
      apply hL.gen
      rw [show 2 * (e + a) = 2 * e + 2 * a by ring]
      exact dvd_add hd hL.two_a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EqOfIndexTwo
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem mem_of_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h2 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hz]
  exact z.2

private theorem det_lt {Ω ι : Type} [Field Ω] [Fintype ι] [DecidableEq ι] (A : ValuationSubring Ω) (M : Matrix ι ι Ω)
    (hM : ∀ i j, M i j ∈ A) {a b : ι} (hab : a ≠ b) (h : ∀ i, A.valuation (M i a - M i b) < 1) :
    A.valuation M.det < 1 := by
  classical
  set M' : Matrix ι ι Ω := M.updateCol a (fun k => M k a + (-1 : Ω) • M k b) with hM'
  have hdet : M'.det = M.det := Matrix.det_updateCol_add_smul_self M hab (-1)
  have hent : ∀ i j, M' i j ∈ A := by
    intro i j
    rw [hM', Matrix.updateCol_apply]
    split_ifs
    · simpa [← sub_eq_add_neg] using A.sub_mem (hM i a) (hM i b)
    · exact hM i j
  have hcol : ∀ i, A.valuation (M' i a) < 1 := by
    intro i
    rw [hM', Matrix.updateCol_self]
    simpa [← sub_eq_add_neg] using h i
  rw [← hdet, Matrix.det_apply']
  refine Valuation.map_sum_lt _ one_ne_zero (fun σ _ => ?_)
  rw [← Finset.mul_prod_erase Finset.univ (fun i => M' (σ i) i) (Finset.mem_univ a)]
  have hs : ((Equiv.Perm.sign σ : ℤ) : Ω) ∈ A := intCast_mem A.toSubring _
  have hp : (∏ i ∈ Finset.univ.erase a, M' (σ i) i) ∈ A := A.toSubring.prod_mem (fun i _ => hent _ _)
  rw [Valuation.map_mul, Valuation.map_mul]
  have e1 := (A.valuation_le_one_iff _).mpr hs
  have e2 := (A.valuation_le_one_iff _).mpr hp
  calc A.valuation ((Equiv.Perm.sign σ : ℤ) : Ω) * (A.valuation (M' (σ a) a) * A.valuation (∏ i ∈ Finset.univ.erase a, M' (σ i) i))
      ≤ 1 * (A.valuation (M' (σ a) a) * 1) := by gcongr
    _ < 1 := by rw [one_mul, mul_one]; exact hcol _

private theorem ine_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} (hl : l.Prime) (hd : ¬ l ∣ (discr K).natAbs) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  intro σ hσ
  have hin : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := (show σ ∈ Inertia A from hσ).2
  show ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  let ι : K →ₐ[ℚ] Ω := (algebraMap K Ω).toRatAlgHom
  let ι' : K →ₐ[ℚ] Ω := (σ : Ω ≃ₐ[ℚ] Ω).toAlgHom.comp ι
  have hιι : ι ≠ ι' := by
    intro h
    apply hx₀
    have := congrArg (fun f : K →ₐ[ℚ] Ω => f x₀) h
    exact this.symm
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card ℚ K Ω, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivOfCardEq hcard
  have hdisc := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis K) e
  rw [← NumberField.coe_discr] at hdisc
  have hint : ∀ (f : K →ₐ[ℚ] Ω) i, IsIntegral ℤ (f (integralBasis K i)) := by
    intro f i
    rw [integralBasis_apply]
    exact (RingOfIntegers.isIntegral_coe _).map ((f : K →+* Ω).toIntAlgHom)
  have hlt : A.valuation (Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis K) e).det < 1 := by
    refine det_lt A _ ?_ (a := e.symm ι) (b := e.symm ι') (e.symm.injective.ne hιι) ?_
    · intro i j
      simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply]
      exact mem_of_int A (hint _ _)
    · intro i
      simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply,
        Equiv.apply_symm_apply]
      rw [Valuation.map_sub_swap]
      exact hin _ ((A.valuation_le_one_iff _).mpr (mem_of_int A (hint _ _)))
  have hdv : A.valuation ((discr K : ℤ) : Ω) < 1 := by
    have h1 : ((discr K : ℤ) : Ω) = algebraMap ℚ Ω ((discr K : ℤ) : ℚ) := by simp
    rw [h1, hdisc, Valuation.map_pow]
    exact pow_lt_one₀ zero_le' hlt two_ne_zero
  have hcop : Nat.Coprime l (discr K).natAbs := (Nat.Prime.coprime_iff_not_dvd hl).mpr hd
  have hic : IsCoprime (l : ℤ) (discr K) := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  obtain ⟨u, v, huv⟩ := hic
  have hΩ : (u : Ω) * (l : Ω) + (v : Ω) * ((discr K : ℤ) : Ω) = 1 := by
    have := congrArg (fun t : ℤ => (t : Ω)) huv
    push_cast at this
    exact this
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A.toSubring _)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A.toSubring _)
  have h1 : A.valuation ((u : Ω) * (l : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (u : Ω) * A.valuation (l : Ω) ≤ 1 * A.valuation (l : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hA
  have h2 : A.valuation ((v : Ω) * ((discr K : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (v : Ω) * A.valuation ((discr K : ℤ) : Ω) ≤ 1 * A.valuation ((discr K : ℤ) : Ω) := by gcongr
      _ < 1 := by rw [one_mul]; exact hdv
  have := Valuation.map_add_lt _ h1 h2
  rw [hΩ, Valuation.map_one] at this
  exact lt_irrefl _ this

private theorem exists_neg (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (w : G ℚ Ω →* Oˣ)
    (hw : w.ker = (Chr.cls ℚ Ω l).ker) : ∃ σ : G ℚ Ω, w σ = -1 ∧ ((Chr.dirG ℚ Ω ψ σ : Oˣ) : O) = ψ (-1) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  obtain ⟨σ, hσ⟩ := (Chr.clsOnto Ω (l * N)).1 (-1)
  have hcomp := (Chr.clsFacts ℚ Ω (l * N)).2.1
  have hdown : ∀ (M : ℕ) [NeZero M] (h : M ∣ l * N), Chr.cls ℚ Ω M σ = -1 := by
    intro M _ h
    rw [← hcomp M h, MonoidHom.comp_apply, hσ]
    ext
    simp [ZMod.unitsMap_def]
  have hl1 := hdown l (dvd_mul_right l N)
  have hN1 := hdown N (dvd_mul_left N l)
  refine ⟨σ, ?_, ?_⟩
  · have hsq : σ * σ ∈ w.ker := by
      rw [hw, MonoidHom.mem_ker, map_mul, hl1]
      simp
    have hne : w σ ≠ 1 := by
      intro h
      have h' : σ ∈ w.ker := h
      rw [hw, MonoidHom.mem_ker, hl1] at h'
      haveI : Fact (2 < l) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hl)⟩
      exact ZMod.neg_one_ne_one (congrArg Units.val h')
    have e1 : w σ * w σ = 1 := by rw [← map_mul]; exact hsq
    have e2 : ((w σ : Oˣ) : O) * (w σ : O) = 1 := by rw [← Units.val_mul, e1, Units.val_one]
    rcases mul_self_eq_one_iff.mp e2 with h | h
    · exact absurd (Units.ext h) hne
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω N σ) : Oˣ) : O) = ψ (-1)
    rw [MulChar.coe_toUnitHom, hN1, Units.val_neg, Units.val_one]

private theorem eq_of_index_two {Γ M : Type} [Group Γ] [CommRing M] [IsDomain M] (H : Subgroup Γ) (hH : H.index = 2)
    (θ : Γ →* Mˣ) (hθ : H ≤ θ.ker) {τ : Γ} (hτ : θ τ ≠ 1) {σ : Γ} (hσ : σ ∉ H) : θ σ = -1 := by
  have hτH : τ ∉ H := fun h => hτ (hθ h)
  have h1 : σ * σ ∈ H := (Subgroup.mul_mem_iff_of_index_two hH).mpr (Iff.rfl)
  have h2 : σ * τ ∈ H := (Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false hσ hτH)
  have e1 : θ σ * θ σ = 1 := by rw [← map_mul]; exact hθ h1
  have e2 : θ σ * θ τ = 1 := by rw [← map_mul]; exact hθ h2
  have e3 : θ τ = θ σ := by
    calc θ τ = θ σ * θ σ * θ τ := by rw [e1, one_mul]
      _ = θ σ * (θ σ * θ τ) := mul_assoc _ _ _
      _ = θ σ := by rw [e2, mul_one]
  have e4 : ((θ σ : Mˣ) : M) * (θ σ : M) = 1 := by rw [← Units.val_mul, e1, Units.val_one]
  rcases mul_self_eq_one_iff.mp e4 with h | h
  · exact absurd (by rw [e3]; exact Units.ext h) hτ
  · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

theorem UpperTheory.V.HV.gdLoc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e N : ℕ) [NeZero N]
      (ψ : DirichletCharacter c.O N) (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a →
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ galOf ℚ K Ω ∧ ∃ σ ∈ Ine (F := ℚ) A,
        ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ ^ 2 : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) ∧
      (∃ σ ∈ galOf ℚ K Ω, ((w σ * Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) ∧
      (∃ σ ∈ galOf ℚ K Ω, (((w σ)⁻¹ * Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : c.Oˣ) : c.O) - 1 ∉ IsLocalRing.maximalIdeal c.O) := by
  intro Ω _ _ _ K _ _ _ l _ c e N _ ψ w η a hG
  have hp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hG.l_odd
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  have hom := hG.om
  have hw1 : w ^ (l - 1) = 1 := hom.1
  have hwc : Congr c w (chiO ℚ Ω l c.O) := hom.2
  have hOm := (omT Ω l c).2 w hom
  have hCF := congrFacts Ω l c
  set D := Chr.dirG ℚ Ω ψ with hD
  have hcE : ∀ n : ℕ, Congr c (chiO ℚ Ω l c.O ^ n) (w ^ n) := by
    intro n
    induction n with
    | zero => simp only [pow_zero]; exact hCF.1.refl _
    | succ n ih => rw [pow_succ, pow_succ]; exact (hCF.2.1 _ _ _ _ ih (hCF.1.symm hwc)).1
  have hΨc : Congr c (Chr.Psi l e D) (w ^ e * D) := by
    have hΨ : Chr.Psi l e D = chiO ℚ Ω l c.O ^ e * D := by simp [Chr.Psi]
    rw [hΨ]
    exact (hCF.2.1 _ _ _ _ (hcE e) (hCF.1.refl D)).1
  have hl1 : ¬ l ∣ l - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hwσ : ∀ σ, (w σ) ^ (l - 1) = 1 := by
    intro σ
    rw [← MonoidHom.pow_apply, hw1, MonoidHom.one_apply]
  have hdisc : ¬ l ∣ (discr K).natAbs := fun h => hG.l_cop (dvd_mul_of_dvd_left h _)
  have hidx : (galOf ℚ K Ω).index = 2 := by
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
    rw [(galEmbTop ℚ K Ω).2.2, hG.quad]
  set m := (l - 1) * orderOf D with hmdef
  have hm : ¬ l ∣ m := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hl1 h
    · exact hG.ord h
  have hpow : ∀ j : ℕ, (w ^ j * D) ^ m = 1 := by
    intro j
    rw [mul_pow, ← pow_mul, hmdef, show j * ((l - 1) * orderOf D) = (l - 1) * (j * orderOf D) by ring,
      pow_mul, hw1, one_pow, one_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨σ₀, hwσ₀, hDσ₀⟩ := exists_neg Ω l hl2 ψ w hOm.2.1
  have hev : ψ (-1) = (-1) ^ e := ((psiBar Ω l c w hom N ψ).2.1 e).mpr hG.par
  have hne1 : ((-1 : (c.O)ˣ)) ≠ 1 := by
    intro h
    have h2 : ((-1 : (c.O)ˣ) : PadicAlgCl l) = ((1 : (c.O)ˣ) : PadicAlgCl l) := by rw [h]
    simp at h2
    norm_num at h2
  have hθ0 : ∀ j : ℕ, (((w ^ j * D) σ₀ : (c.O)ˣ) : c.O) = (-1) ^ j * (-1) ^ e := by
    intro j
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwσ₀, Units.val_mul, Units.val_pow_eq_pow_val, hDσ₀, hev,
      Units.val_neg, Units.val_one]
  have key : ∀ j : ℕ, (∀ σ ∈ galOf ℚ K Ω, (((w ^ j * D) σ : (c.O)ˣ) : c.O) - 1 ∈ IsLocalRing.maximalIdeal c.O) →
      (-1 : c.O) ^ j * (-1) ^ e = -1 → η = w ^ j * D := by
    intro j hj hv
    have hle : galOf ℚ K Ω ≤ (w ^ j * D).ker := by
      intro σ hσ
      rw [MonoidHom.mem_ker]
      refine hCF.2.2.2.1 _ 1 m hm ?_ (one_pow _) (by simpa using hj σ hσ)
      rw [← MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
    have hτ : (w ^ j * D) σ₀ ≠ 1 := by
      intro h
      apply hne1
      apply Units.ext
      rw [Units.val_neg, Units.val_one, ← hv, ← hθ0 j, h, Units.val_one]
    have hηle : galOf ℚ K Ω ≤ η.ker := le_of_eq hG.eta_ker.symm
    refine MonoidHom.ext (fun σ => ?_)
    by_cases hσ : σ ∈ galOf ℚ K Ω
    · rw [MonoidHom.mem_ker.mp (hηle hσ), MonoidHom.mem_ker.mp (hle hσ)]
    · have hητ : η σ ≠ 1 := by
        intro h
        apply hσ
        rw [← hG.eta_ker]
        exact h
      rw [eq_of_index_two _ hidx η hηle hητ hσ, eq_of_index_two _ hidx _ hle hτ hσ]
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    refine ⟨ine_le Ω K hp hdisc A hA, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hG.gen
    apply hOm.2.2.2.2.2.2.1 A hA (2 * (e + a))
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hx : (w ^ (2 * (e + a))) σ = ((w ^ e * D) σ) ^ 2 := by
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, hD, hG.ine A hA σ hσ,
        ← pow_add, ← pow_mul, mul_comm 2]
    have hm1 : (((w ^ (2 * (e + a))) σ : (c.O)ˣ) : c.O) - (((Chr.Psi l e D σ) ^ 2 : (c.O)ˣ) : c.O)
        ∈ IsLocalRing.maximalIdeal c.O := by
      rw [hx, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, sq_sub_sq]
      apply Ideal.mul_mem_left
      have := hΨc σ
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
    have hm2 := hcon σ hσ
    refine hCF.2.2.2.1 _ 1 (l - 1) hl1 ?_ (one_pow _) ?_
    · rw [← MonoidHom.pow_apply, ← pow_mul, mul_comm, pow_mul, hw1, one_pow, MonoidHom.one_apply]
    · have := Ideal.add_mem _ hm1 hm2
      rw [sub_add_sub_cancel] at this
      simpa using this
  · by_contra hcon
    push_neg at hcon
    have hθ := key (e + 1) (fun σ hσ => by
        have h1 := hcon σ hσ
        have h2 : (((w ^ (e + 1) * D) σ : (c.O)ˣ) : c.O) - ((w σ * Chr.Psi l e D σ : (c.O)ˣ) : c.O)
            ∈ IsLocalRing.maximalIdeal c.O := by
          have hu : (w ^ (e + 1) * D) σ = w σ * ((w ^ e * D) σ) := by
            rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_succ',
              mul_assoc]
          rw [hu, Units.val_mul, Units.val_mul, ← mul_sub]
          apply Ideal.mul_mem_left
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hΨc σ)
        have := Ideal.add_mem _ h2 h1
        rwa [sub_add_sub_cancel] at this)
      (by rw [← pow_add]; exact Odd.neg_one_pow ⟨e, by ring⟩)
    apply hG.eta (e + 1 + a) 1
    have hg : w ^ (e + 1 + a) * (D * (w ^ a)⁻¹) ^ 1 = w ^ (e + 1) * D := by
      rw [pow_one, pow_add w (e + 1) a, mul_comm D, ← mul_assoc, mul_inv_cancel_right]
    rw [hθ, hg]
    exact hCF.1.refl _
  · by_contra hcon
    push_neg at hcon
    obtain ⟨e', he⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by have := hG.e_pos; omega⟩
    have hθ := key e' (fun σ hσ => by
        have h1 := hcon σ hσ
        have h2 : (((w ^ e' * D) σ : (c.O)ˣ) : c.O) - (((w σ)⁻¹ * Chr.Psi l e D σ : (c.O)ˣ) : c.O)
            ∈ IsLocalRing.maximalIdeal c.O := by
          have hu : (w ^ e' * D) σ = (w σ)⁻¹ * ((w ^ e * D) σ) := by
            rw [he, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_succ',
              mul_assoc, inv_mul_cancel_left]
          rw [hu, Units.val_mul, Units.val_mul, ← mul_sub]
          apply Ideal.mul_mem_left
          rw [← neg_sub]
          exact Submodule.neg_mem _ (hΨc σ)
        have := Ideal.add_mem _ h2 h1
        rwa [sub_add_sub_cancel] at this)
      (by rw [he, ← pow_add]; exact Odd.neg_one_pow ⟨e', by ring⟩)
    apply hG.eta (e' + a) 1
    have hg : w ^ (e' + a) * (D * (w ^ a)⁻¹) ^ 1 = w ^ e' * D := by
      rw [pow_one, pow_add w e' a, mul_comm D, ← mul_assoc, mul_inv_cancel_right]
    rw [hθ, hg]
    exact hCF.1.refl _
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem open_galOf (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsOpen (galOf ℚ K Ω : Set (G ℚ Ω)) := by
  let b := Module.finBasis ℚ K
  have e : (galOf ℚ K Ω : Set (G ℚ Ω)) = ⋂ i, {σ : G ℚ Ω | σ (algebraMap K Ω (b i)) = algebraMap K Ω (b i)} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_galOf]
    refine ⟨fun h i => h _, fun h x => ?_⟩
    have := b.ext (f₁ := σ.toLinearMap ∘ₗ (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap)
      (f₂ := (IsScalarTower.toAlgHom ℚ K Ω).toLinearMap) h
    exact LinearMap.congr_fun this x
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := ℚ) _ (fun t => t = algebraMap K Ω (b i))

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem tor_eq_one {R : Type} [CommRing R] {t : Rˣ} (h : tor R t = 1) : t = 1 := by
  have h1 := congrArg (fun x : GL (Fin 3) R => (x : Matrix (Fin 3) (Fin 3) R) 0 0) h
  apply Units.ext
  simpa [tor_val, wt1] using h1

private theorem diagonal_rep_eq_one_iff {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    r0 η Ψ g = 1 ↔ η g = 1 ∧ Ψ g = 1 := by
  refine ⟨fun h => ⟨congrArg SemidirectProduct.right h, tor_eq_one (congrArg SemidirectProduct.left h)⟩, fun h => ?_⟩
  refine SemidirectProduct.ext ?_ h.1
  rw [unitaryThreeReflection_left, h.2, map_one]
  rfl

private theorem bar_lc {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ)
    (hΨ : CharCont Ψ) : IsLocallyConstant (barChar O Ψ) := by
  refine IsLocallyConstant.desc _ Units.val ?_ Units.val_injective
  have h := (hΨ 1 1).comp (Ideal.Quotient.factor (pow_one (maximalIdeal O)).le)
  simp only [zpow_one] at h
  exact h

theorem UpperTheory.V.U3.dat_facts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      D.cc * D.cc = 1 ∧ D.η D.cc = -1 ∧ D.Ψ D.cc = 1 ∧ IsLocallyConstant D.η ∧ IsLocallyConstant (barChar c.O D.Ψ) ∧
      (∀ g ∈ D.Kill, r0 D.η D.Ψ g = 1) ∧ IsUnit (2 : c.O) ∧ IsCMField K ∧ Continuous D.ΨQ ∧
      (∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧ D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1) ∧
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.η.ker ∧
        ∃ s ∈ Ine (F := ℚ) A, IsUnit ((D.Ψ s : c.O) ^ 2 - 1)) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨w, η', a, hlit⟩ := (gdIff Ω K l c e N ψ).1.1 D.gd
  have himag := D.gd.imag
  have hΨ : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
      D.Ψ g = Chr.dirG ℚ Ω ψ g := fun A hA g hg => by
    show (chiO ℚ Ω l c.O g) ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g = _
    have : chiO ℚ Ω l c.O g = 1 := by
      unfold chiO
      rw [MonoidHom.comp_apply, cyc_ine Ω l A hA hg, map_one]
    rw [this, _root_.one_zpow, one_mul]
  have hkill : ∀ g, g ∈ D.Kill ↔ ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧
      D.η g = 1 ∧ Chr.dirG ℚ Ω ψ g = 1 := fun g => by
    refine exists_congr fun A => and_congr_right fun hA => and_congr_right fun hg => ?_
    unfold rbar
    rw [diagonal_rep_eq_one_iff]
    refine and_congr_right fun _ => ?_
    unfold barChar
    rw [MonoidHom.comp_apply, hΨ A hA g hg]
    refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hlit.ord ?_ (one_pow _) ?_
    · rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, Units.val_one, map_one]
      exact congrArg Units.val h
  obtain ⟨φ, hφ⟩ := D.conj
  refine ⟨?_, ?_, hlit.par D.cc ⟨φ, hφ⟩, ?_, ?_, fun g hg => ?_, ?_, ?_, ?_, hkill, fun A hA => ?_⟩
  · refine AlgEquiv.ext fun x => φ.injective ?_
    rw [AlgEquiv.mul_apply, hφ, hφ]
    simp
  · refine (Int.units_eq_one_or _).resolve_left fun h => ?_
    have h1 : D.cc ∈ galOf ℚ K Ω := D.η_ker ▸ h
    refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]
  · exact locConst _ (D.η_ker ▸ open_galOf Ω K)
  · exact bar_lc _ D.Ψ_cont
  · obtain ⟨A, hA, hg, h1, h2⟩ := (hkill g).1 hg
    exact (diagonal_rep_eq_one_iff _ _ _).2 ⟨h1, (hΨ A hA g hg).trans h2⟩
  · have := (dvrFacts l c.O).2.2.2.2.2.2.2.2 2 fun h => D.gd.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  · have : Algebra.IsQuadraticExtension ℚ K := ⟨D.gd.quad⟩
    exact IsCMField.ofCMExtension ℚ K
  · have hf : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom := by
      refine ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val).congr fun x => ?_
      exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x).symm
    have h1 := ((hf.units_map _).comp (continuous_cycZ ℚ Ω l)).zpow (e : ℤ)
    have h2 := (((locConst _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom).comp
      (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom)).continuous
    refine (h1.mul h2).congr fun g => ?_
    show _ = Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g)
    rw [map_mul, map_zpow]
    rfl
  · obtain ⟨h1, s, hs, h2⟩ := (gdLoc Ω K l c e N ψ w η' a hlit).1 A hA
    refine ⟨D.η_ker ▸ h1, s, hs, ?_⟩
    rw [Units.val_pow_eq_pow_val] at h2
    exact not_not.1 h2
