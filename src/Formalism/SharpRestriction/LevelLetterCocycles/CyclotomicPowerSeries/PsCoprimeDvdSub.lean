module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem powerSeries_algHom_C' {O : Type} [CommRing O] (ψ : PowerSeries O →ₐ[O] PowerSeries O) (c : O) :
    ψ (C c) = C c := by
  first
  | exact ψ.commutes c
  | (have e : (C c : PowerSeries O) = c • (1 : PowerSeries O) := by
       rw [PowerSeries.smul_eq_C_mul, mul_one]
     rw [e, map_smul, map_one])
  | simpa using ψ.commutes c

theorem psCoprime_dvdSub {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    (X * (X + C (l : O)) : PowerSeries O) ∣ φ a - C (constantCoeff a) := by
  obtain ⟨b, hb⟩ : (X : PowerSeries O) ∣ a - C (constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have e : φ (a - C (constantCoeff a)) = φ a - C (constantCoeff a) := by
    rw [map_sub, powerSeries_algHom_C']
  rw [← e, hb, map_mul]
  exact dvd_mul_of_dvd_left h _

private theorem constantCoeff_algHom_eq_of_X_mul_dvd {O : Type} [CommRing O] (l : ℕ)
    (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (a : PowerSeries O) :
    constantCoeff (φ a) = constantCoeff a := by
  have h1 := psCoprime_dvdSub l φ h a
  have h2 : (X : PowerSeries O) ∣ φ a - C (constantCoeff a) :=
    dvd_trans (dvd_mul_right (X : PowerSeries O) _) h1
  rw [PowerSeries.X_dvd_iff] at h2
  first
  | simpa [sub_eq_zero] using h2
  | (rw [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h2; exact h2)

theorem psCoprime_cc {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s : ℕ) :
    constantCoeff ((⇑φ)^[s] (X + C (l : O))) = (l : O) := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', constantCoeff_algHom_eq_of_X_mul_dvd l φ h, ih]

theorem psCoprime_qdvd {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (t : ℕ) :
    (X + C (l : O) : PowerSeries O) ∣ (⇑φ)^[t + 1] (X + C (l : O)) - C (l : O) := by
  rw [Function.iterate_succ_apply']
  have h1 := psCoprime_dvdSub l φ h ((⇑φ)^[t] (X + C (l : O)))
  rw [psCoprime_cc l φ h t] at h1
  exact dvd_trans (dvd_mul_left _ _) h1

private theorem algHom_iterate_C_add_mul {O : Type} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (c : O) (s : ℕ) (b d : PowerSeries O) :
    (⇑φ)^[s] (C c + b * d) = C c + (⇑φ)^[s] b * (⇑φ)^[s] d := by
  induction s with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, map_add (f := _), map_mul, powerSeries_algHom_C']

theorem psCoprime_lt {O : Type} [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : (X * (X + C (l : O)) : PowerSeries O) ∣ φ X) (s s' : ℕ) (hs : s < s') :
    (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), (⇑φ)^[s'] (X + C (l : O))} := by
  obtain ⟨t, rfl⟩ : ∃ t, s' = s + (t + 1) := ⟨s' - s - 1, by omega⟩
  obtain ⟨q, hq⟩ := psCoprime_qdvd l φ h t
  have hq' : (⇑φ)^[t + 1] (X + C (l : O)) = C (l : O) + (X + C (l : O)) * q := by
    linear_combination hq
  have e : (⇑φ)^[s + (t + 1)] (X + C (l : O)) =
      C (l : O) + (⇑φ)^[s] (X + C (l : O)) * (⇑φ)^[s] q := by
    rw [Function.iterate_add_apply, hq', algHom_iterate_C_add_mul]
  rw [Ideal.mem_span_pair]
  exact ⟨-((⇑φ)^[s] q), 1, by linear_combination e⟩

theorem psCoprime : PsCoprimeStatement := by
  unfold PsCoprimeStatement
  intro O _ l φ h
  refine ⟨fun s => ?_, fun s s' hss => ?_⟩
  · have hc := psCoprime_cc l φ h s
    obtain ⟨r, hr⟩ : (X : PowerSeries O) ∣ (⇑φ)^[s] (X + C (l : O)) - C (l : O) := by
      rw [PowerSeries.X_dvd_iff, map_sub, hc]
      first
      | simp
      | rw [PowerSeries.constantCoeff_C, sub_self]
    rw [Ideal.mem_span_pair]
    exact ⟨1, -r, by linear_combination hr⟩
  · rcases Nat.lt_or_gt_of_ne hss with hlt | hlt
    · exact psCoprime_lt l φ h s s' hlt
    · rw [Set.pair_comm]
      exact psCoprime_lt l φ h s' s hlt

end LevelStatements.Lv
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval
noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_coe_eq_aeval {O T : Type} [CommRing O] [CommRing T] [Algebra O T]
    (ρ : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    all_goals first
      | exact ρ.commutes a
      | simpa using ρ.commutes a
      | (rw [← ρ.commutes a]; rfl)

theorem constantCoeff_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    all_goals first
      | rfl
      | simp [PowerSeries.algebraMap_apply'']
      | (rw [IsScalarTower.algebraMap_apply O S (PowerSeries S)]; simp)

theorem eq_of_X_mul_eq {S : Type} [CommRing S] {f g : PowerSeries S}
    (h : (X : PowerSeries S) * f = X * g) : f = g := by
  first
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff (n + 1)) h)
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff S (n + 1)) h)
  | exact PowerSeries.X_mul_cancel h
  | exact mul_left_cancel₀ PowerSeries.X_ne_zero h

private theorem map_coe_eq_X_pow_lemma {O K : Type} [CommRing O] [CommRing K] (I : Ideal O) (f : O →+* K)
    (hf : ∀ c ∈ I, f c = 0) (P : Polynomial O) (hP : P.IsDistinguishedAt I) :
    PowerSeries.map f (P : PowerSeries O) = X ^ P.natDegree := by
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have hmem : ∀ {n : ℕ}, n < P.natDegree → P.coeff n ∈ I := by
    intro n hn
    first | exact hP.mem hn | exact hP.1.mem hn | exact hP.toIsWeaklyEisensteinAt.mem hn
  ext n
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, PowerSeries.coeff_X_pow]
  split_ifs with hn
  · rw [hn, hmon.coeff_natDegree, map_one]
  · rcases Nat.lt_or_gt_of_ne hn with h | h
    · exact hf _ (hmem h)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]

private theorem exists_weierstrass_div_lemma_2 {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O))
    (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < P.natDegree ∧
      a = (P : PowerSeries O) * q + r := by
  have h1 : PowerSeries.map (residue O) (P : PowerSeries O) = X ^ P.natDegree :=
    map_coe_eq_X_pow_lemma _ _ (fun c hc => (residue_eq_zero_iff c).2 hc) P hP
  have h2 : (PowerSeries.map (residue O) (P : PowerSeries O)).order.toNat = P.natDegree := by
    rw [h1, PowerSeries.order_X_pow]; rfl
  have h3 : PowerSeries.map (residue O) (P : PowerSeries O) ≠ 0 := by
    rw [h1]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hr, he⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) h3
  have h2' : (PowerSeries.map (Ideal.Quotient.mk (maximalIdeal O)) (P : PowerSeries O)).order.toNat =
      P.natDegree := by
    first
      | exact h2
      | (rw [map_coe_eq_X_pow_lemma _ _ (fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc) P hP,
          PowerSeries.order_X_pow]; rfl)
  refine ⟨q, r, ?_, he⟩
  first
    | (rw [h2'] at hr; exact hr)
    | (rw [h2] at hr; exact hr)
    | simpa [h2'] using hr

theorem rhoCompl : RhoComplStatement := by
  intro O LL S _ _ _ _ _ _ _ _ _ _ _ P hP ρ hunit hann
  have hmon : P.Monic := by first | exact hP.monic | exact hP.2
  have key : ∀ a : PowerSeries O, (X : PowerSeries S) ∣ ρ a → (P : PowerSeries O) ∣ a := by
    intro a ha
    obtain ⟨q, r, hr, he⟩ := exists_weierstrass_div_lemma_2 P hP a
    obtain ⟨w, hw⟩ := hunit
    have hρa : ρ a = (w : PowerSeries S) * X * ρ q + Polynomial.aeval (ρ X) r := by
      rw [he, map_add (f := _), map_mul, hw, algHom_coe_eq_aeval]
    have h0 : constantCoeff (ρ a) = 0 := by
      obtain ⟨c, hc⟩ := ha
      rw [hc, map_mul, PowerSeries.constantCoeff_X, zero_mul]
    have hr0 : Polynomial.aeval (constantCoeff (ρ X)) r = 0 := by
      have h1 := congrArg constantCoeff hρa
      rw [h0, map_add (f := _), map_mul, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul, zero_add,
        constantCoeff_aeval] at h1
      exact h1.symm
    have hdvd : P.map (algebraMap O LL) ∣ r.map (algebraMap O LL) := by
      apply hann
      first | (rw [Polynomial.aeval_map_algebraMap]; exact hr0) | simpa [Polynomial.aeval_map_algebraMap] using hr0
    have hmap0 : r.map (algebraMap O LL) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
      calc (r.map (algebraMap O LL)).degree ≤ r.degree := by
            first | exact Polynomial.degree_map_le | exact Polynomial.degree_map_le _ _
        _ < P.natDegree := hr
        _ = P.degree := (Polynomial.degree_eq_natDegree hmon.ne_zero).symm
        _ = (P.map (algebraMap O LL)).degree := (hmon.degree_map _).symm
    have hr' : r = 0 := by
      apply Polynomial.map_injective (algebraMap O LL) (IsFractionRing.injective O LL)
      rw [hmap0, Polynomial.map_zero]
    rw [hr', Polynomial.coe_zero, add_zero] at he
    exact ⟨q, he⟩
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := key a (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) ha)
    obtain ⟨w, hw⟩ := hunit
    rw [map_mul, hw] at ha
    obtain ⟨c, hc⟩ := ha
    have h2 : (w : PowerSeries S) * ρ b = X ^ k * c := by
      apply eq_of_X_mul_eq
      linear_combination hc
    have hb : (X : PowerSeries S) ^ k ∣ ρ b := by
      refine ⟨(↑w⁻¹ : PowerSeries S) * c, ?_⟩
      calc ρ b = (↑w⁻¹ : PowerSeries S) * ((w : PowerSeries S) * ρ b) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = (↑w⁻¹ : PowerSeries S) * (X ^ k * c) := by rw [h2]
        _ = X ^ k * ((↑w⁻¹ : PowerSeries S) * c) := by ring
    obtain ⟨d, hd⟩ := ih b hb
    exact ⟨d, by rw [hd]; ring⟩

end LevelStatements.Lv
end
end
