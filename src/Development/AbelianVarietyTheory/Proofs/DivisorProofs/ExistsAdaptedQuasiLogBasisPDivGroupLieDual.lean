module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractions
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.LogUniq

theorem eq_zero_of_linear_zero_coboundary_zero_fractions : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E]
    [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E,
    lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  intro p _ O E _ _ _ hF d μ hμ R hlin hcob
  classical
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : E) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow]
    refine (hF.unit_p.pow a).mul ?_
    have hc : Nat.Coprime m p :=
      Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have := (hF.unit_coprime m hc).map (algebraMap O E)
    simpa using this
  have hL : IsLift (RingHom.id O) μ := ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have hlow : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (up E μ i) = coeff α (addLaw E d i) := by
    intro i α hα
    rw [up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hL i α hα, GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hdeg : ∀ a e : Fin d →₀ ℕ, (Finsupp.sumElim a e).degree = (a + e).degree := by
    intro a e
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
    simp
  have key : ∀ N : ℕ, ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro N
    induction N with
    | zero => intro α h; omega
    | succ N ih =>
      intro α hα
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hα) with h | h
      · exact ih α h
      have hc := (GlobalTheory.CobLead.cob_eq_additive_lead E d (up E μ) N hlow).1 R ih
      have hcoef : ∀ a e : Fin d →₀ ℕ, a + e = α →
          coeff (Finsupp.sumElim a e) (cob1 (addLaw E d) R) = 0 := by
        intro a e hae
        rw [← (hc _).2 (by rw [hdeg, hae, h]), hcob, map_zero]
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 h
          subst h0
          have := hcoef 0 0 (by simp)
          rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial] at this
          simpa using this
        · obtain ⟨j, rfl⟩ := GlobalTheory.Katz.LowLaw.eq_single_of_degree_eq_one h
          exact congrFun hlin j
      · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
          by_contra! hc0
          have : α = 0 := Finsupp.ext hc0
          rw [this, map_zero] at h
          omega
        set a := α - Finsupp.single i 1 with ha
        have hae : a + Finsupp.single i 1 = α := by
          ext k
          simp only [ha, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with h1 <;> (try subst h1) <;> omega
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, zero_add] at hae
          rw [← hae, Finsupp.degree_single] at h
          omega
        have hs0 : Finsupp.single i 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
        have := hcoef a (Finsupp.single i 1) hae
        rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial, if_neg hs0, if_neg ha0, sub_zero, sub_zero, hae] at this
        have hpos : (∏ s, (α s).choose (a s)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun s _ => (Nat.choose_pos ?_).ne'
          rw [← hae]; simp
        exact (hunit _ hpos).mul_right_eq_zero.1 this
  ext α
  simpa using key (α.degree + 1) α (by omega)

end GlobalTheory.LogUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractionsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E, lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  first | exact @GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | exact GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | (intros; apply GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntLogOfIsLiePSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundaryStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  first | exact @GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | exact GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | (intros; apply GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrime
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrimeStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  first | exact @GlobalTheory.CobModP.coboundary_mod_p | exact GlobalTheory.CobModP.coboundary_mod_p | (intros; apply GlobalTheory.CobModP.coboundary_mod_p <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefec
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefecStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  first | exact @GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | exact GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | (intros; apply GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev <;> assumption)
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem GlobalTheory.QLog.exists_int_log_of_isLie_p_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ O E _ _ _ hF G d c f l hf hl
  obtain ⟨s₁, hs₁, hl₁⟩ := (c.isLie_iff hF.inj f _).1 hl 1
  rw [pow_one] at hs₁
  have hdiv : ∀ (w : G.dual.omega) (φ : CartierDual O (G.A 1)), dUnit (R := O) φ = w.1 1 →
      (p : O) ∣ φ (c.ev 1 s₁) := by
    intro w φ hφ
    have h1 := hl₁ w φ hφ
    rw [pow_one, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (dvd_sub_right (dvd_mul_right _ _)).1 h1
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd p O G 1 (p : O) (c.ev 1 s₁) hdiv
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect p O E hF G d c f s₁ z hf hs₁ hz
  obtain ⟨hf0, hflin, -⟩ := hf
  choose b _ hb using hflin
  obtain ⟨g, hg0, hglin, hgcob⟩ := GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hF d c.μ c.isLaw (fun i => b i - lin t i)
  have hμ : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.isLaw.const i, map_zero]
  refine ⟨t, g, hgcob, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hf0, hg0, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
    simp
  · intro i
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    have : lin (f - map (algebraMap O E) t - g) i = lin f i - algebraMap O E (lin t i) - lin g i := by
      simp [lin, coeff_map]
    rw [this, hb i, hglin i, map_sub, map_zero]
    simp
  · have hsub : f - map (algebraMap O E) t - g = (f - map (algebraMap O E) t) + (-1 : E) • g := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, formalCoboundary_add hμ, formalCoboundary_smul hμ, hgcob, smul_zero, add_zero]
    exact ht
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByP
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLogInj

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE f l hf hL
  exact GlobalTheory.QLog.exists_int_log_of_isLie_p_smul p O E hE G d c f l hf hL

end GlobalTheory.QLogInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByPStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  first | exact @GlobalTheory.QLogInj.main | exact GlobalTheory.QLogInj.main | (intros; apply GlobalTheory.QLogInj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecomposition
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogStep

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem constantCoeff_up_eq_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up E μ i) = 0 := by
  rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
    map_zero]

theorem ql_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} {f g : MvPowerSeries (Fin d) E} (hf : QL μ N f) (hg : QL μ N g) :
    QL μ N (f + g) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨by rw [map_add (f := _), f0, g0, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := f1 i
    obtain ⟨b, hb, hb'⟩ := g1 i
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    simp only [lin, map_add (f := _)] at ha' hb' ⊢
    rw [ha', hb']
  · obtain ⟨a, ha, ha'⟩ := f2 α
    obtain ⟨b, hb, hb'⟩ := g2 α
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    rw [formalCoboundary_add (constantCoeff_up_eq_zero hμ), map_add (f := _), ha', hb', map_add (f := _)]

theorem ql_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} (a : O) {f : MvPowerSeries (Fin d) E} (hf : QL μ N f) :
    QL μ N (algebraMap O E a • f) := by
  obtain ⟨f0, f1, f2⟩ := hf
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, f0,
      mul_zero]
  · obtain ⟨b, hb, hb'⟩ := f1 i
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    simp only [lin, coeff_smul] at hb' ⊢
    rw [hb', map_mul]
  · obtain ⟨b, hb, hb'⟩ := f2 α
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    rw [formalCoboundary_smul (constantCoeff_up_eq_zero hμ), coeff_smul, hb', map_mul]

theorem ql_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (N : Ideal O) : QL μ N (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
  have := formalCoboundary_smul (constantCoeff_up_eq_zero (E := E) hμ) 0 0
  rw [zero_smul, zero_smul] at this
  rw [this, map_zero, map_zero]

theorem comb_add {ι : Type} [Fintype ι] (b b' : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb (b + b') e = comb b e + comb b' e := by
  simp only [comb, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem ql_comb {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E)
    (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact ql_zero hμ _
  | cons i s hi ih => rw [Finset.sum_cons]; exact ql_add hμ (ql_smul hμ _ (he i)) ih

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQe hcob hlin hLie f hf
  have hμ := c.isLaw.const
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hc0 := constantCoeff_up_eq_zero (E := E) hμ

  let t : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) fun j => lb j
  have ht : ∀ i, c.IsLie (e i) (t i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF _ (hQe (Sum.inl i))
      have := ((GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ l l 0 hl hl).2.2 (hcob i))
      subst this
      exact hl
    · exact hLie j

  have hcombS : ∀ (b : Fin d ⊕ Fin k → O) (S : Finset (Fin d ⊕ Fin k)),
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e i) (∑ i ∈ S, b i • t i) ∧
        QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e i) := by
    intro b S
    induction S using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ⟨c.isLie_zero hinj, ql_zero hμ _⟩
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_comm, add_comm (b i • t i)]
      exact ⟨(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ _ _ (b i) ih.1 (ht i)).1 ih.2 (hQe i),
        ql_add hμ ih.2 (ql_smul hμ _ (hQe i))⟩
  have hcombLie : ∀ b : Fin d ⊕ Fin k → O, c.IsLie (comb b e) (∑ i, b i • t i) :=
    fun b => (hcombS b Finset.univ).1

  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF f hf
  let b0 : Fin d ⊕ Fin k → O := Sum.elim (0 : Fin d → O) fun j => lb.repr l j
  have hb0 : ∑ i, b0 i • t i = l := by
    rw [Fintype.sum_sum_type]
    simp only [b0, t, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]
    exact lb.sum_repr l
  set f' := f + algebraMap O E (-1) • comb b0 e with hf'
  have hQf' : QL c.μ ⊤ f' := ql_add hμ hf (ql_smul hμ _ (ql_comb hμ b0 e hQe))
  have hLf' : c.IsLie f' ((p : O) • 0) := by
    have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f (comb b0 e) l _ (-1) hl (hcombLie b0)).1 hf
      (ql_comb hμ b0 e hQe)
    rwa [hb0, neg_one_smul, add_neg_cancel, ← smul_zero (p : O)] at this
  obtain ⟨s, g, hg, hh⟩ := GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p p C v O hv G d c E hF f' 0 hQf' hLf'
  set h := f' - map (algebraMap O E) s - g with hhdef

  have hw : ∀ i, ∃ w : O, lin g i = algebraMap O E w := by
    intro i
    obtain ⟨b1, -, hb1⟩ := hQf'.2.1 i
    obtain ⟨b3, -, hb3⟩ := hh.2.1 i
    refine ⟨b1 - coeff (Finsupp.single i 1) s - b3, ?_⟩
    have : g = f' - map (algebraMap O E) s - h := by rw [hhdef]; ring
    simp only [lin] at hb1 hb3 ⊢
    rw [this, map_sub, map_sub, hb1, hb3, coeff_map, map_sub, map_sub]
  choose w hw using hw
  let bw : Fin d ⊕ Fin k → O := Sum.elim w 0
  have hcw : comb bw e = ∑ i, algebraMap O E (w i) • e (Sum.inl i) := by
    simp [comb, bw, Fintype.sum_sum_type]

  have hgw : g = comb bw e := by
    have key := GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E hF d c.μ c.isLaw (g - comb bw e) ?_ ?_
    · exact sub_eq_zero.1 key
    · funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lin, hcw, map_sub, map_sum, coeff_smul, Pi.zero_apply] at hw ⊢
      have hl' : ∀ j, coeff (Finsupp.single i 1) (e (Sum.inl j)) =
          (Pi.single j (1 : E) : Fin d → E) i := fun j => congrFun (hlin j) i
      simp only [hl', hw]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp
    · let L : MvPowerSeries (Fin d) E →+ MvPowerSeries (Fin d ⊕ Fin d) E :=
        AddMonoidHom.mk' (cob1 (up E c.μ)) (formalCoboundary_add hc0)
      have hL : ∀ x, L x = cob1 (up E c.μ) x := fun _ => rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hL, map_sub, hcw, map_sum]
      simp only [hL, formalCoboundary_smul hc0, hcob, smul_zero, Finset.sum_const_zero, sub_zero]
      exact hg

  obtain ⟨u, hu⟩ := hF.unit_p
  refine ⟨bw + b0, s, (↑u⁻¹ : E) • h, ?_, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · obtain ⟨b, hb, hb'⟩ := h1 i
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      simp only [lin, coeff_smul] at hb' ⊢
      rw [hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · obtain ⟨b, hb, hb'⟩ := h2 α
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      rw [formalCoboundary_smul hc0, coeff_smul, hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul,
        one_mul]
  · rw [smul_smul, ← hu, Units.mul_inv, one_smul, comb_add, ← hgw]
    rw [map_neg, map_one, neg_one_smul] at hf'
    rw [hhdef, hf']
    ring

end GlobalTheory.QLogStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecompositionStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_division_step_decomposition : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  first | exact @GlobalTheory.QLogStep.main | exact GlobalTheory.QLogStep.main | (intros; apply GlobalTheory.QLogStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadic
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.Conv

section SlopeTestRemainingChoices

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem exists_lim {p : ℕ} (h : IsFrame p E (RingHom.id O)) (a : ℕ → O) :
    ∃ L : O, ∀ N : ℕ, ∃ c : O,
      L = ∑ n ∈ Finset.range N, (p : O) ^ n * a n + (p : O) ^ N * c := by
  obtain ⟨L, hL⟩ := h.complete.toIsPrecomplete.prec
    (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]
      exact dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left
        (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))
  refine ⟨L, fun N => ?_⟩
  have hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L
      [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)] := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨-c, by linear_combination -hc⟩

theorem eq_zero_of_forall {p : ℕ} (h : IsFrame p E (RingHom.id O)) {x : E}
    (hx : ∀ N : ℕ, ∃ b : O, x = algebraMap O E ((p : O) ^ N * b)) : x = 0 := by
  obtain ⟨b, hb⟩ := hx 0
  have h0 : (p : O) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun N => by
    obtain ⟨c, hc⟩ := hx N
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [hb, h0, map_zero]

theorem comb_add_mul {ι : Type} [Fintype ι] (x y : ι → O) (c : O)
    (e : ι → MvPowerSeries (Fin d) E) :
    comb (fun i => x i + c * y i) e = comb x e + algebraMap O E c • comb y e := by
  unfold comb
  simp only [map_add (f := _), map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def IntD (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (g : MvPowerSeries (Fin d) E) : Prop :=
  (∀ i, ∃ b : O, lin g i = algebraMap O E b) ∧ In (⊤ : Ideal O) (cob1 (up E μ) g)

variable {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}

theorem up_const (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp [up, hμ]

theorem IntD.ofQL {g : MvPowerSeries (Fin d) E} (hg : QL μ ⊤ g) : IntD μ g :=
  ⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩

theorem IntD.zero (hμ : ∀ i, constantCoeff (μ i) = 0) : IntD μ (0 : MvPowerSeries (Fin d) E) := by
  have h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0 := by
    simpa using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)
  refine ⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩

theorem IntD.add (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g + g') := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    obtain ⟨b', hb'⟩ := hg'.1 i
    refine ⟨b + b', ?_⟩
    simp only [lin, map_add (f := _)] at hb hb' ⊢
    rw [hb, hb']
  · obtain ⟨b, -, hb⟩ := hg.2 α
    obtain ⟨b', -, hb'⟩ := hg'.2 α
    exact ⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add (f := _), hb, hb', map_add (f := _)]⟩

theorem IntD.smul (hμ : ∀ i, constantCoeff (μ i) = 0) (c : O) {g : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) : IntD μ (algebraMap O E c • g) := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    refine ⟨c * b, ?_⟩
    simp only [lin, coeff_smul] at hb ⊢
    rw [hb, map_mul]
  · obtain ⟨b, -, hb⟩ := hg.2 α
    exact ⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩

theorem IntD.sub (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g - g') := by
  have : g - g' = g + algebraMap O E (-1) • g' := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact hg.add hμ (hg'.smul hμ _)

theorem IntD.comb (hμ : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → O)
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, IntD μ (e i)) : IntD μ (comb b e) :=
  Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ)
    fun i _ => (he i).smul hμ (b i)

theorem IntD.map (hμ : ∀ i, constantCoeff (μ i) = 0) (s : MvPowerSeries (Fin d) O) :
    IntD μ (MvPowerSeries.map (algebraMap O E) s) := by
  refine ⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩
  have := ((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm
  rw [show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) =
      MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]
  exact In.top_iff.2 ⟨_, rfl⟩

end SlopeTestRemainingChoices

theorem generate_of_step : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  intro p _ O E _ _ _ h d μ hμ ι _ e he H f hf
  have hc := hμ.const
  choose! bf sf ff hQ hff using H
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n) :=
    ⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩
  have hFQ : ∀ n, QL μ ⊤ (F n) := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hf
    | succ n ih => rw [hFs]; exact hQ _ ih
  have step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1) :=
    fun n => by rw [hFs]; exact hff _ (hFQ n)
  have hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N) := fun N => by
    rw [map_pow, map_natCast]
  have tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
      ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N := by
    intro N
    induction N with
    | zero =>
      have : comb (fun _ : ι => (0 : O)) e = 0 := by simp [comb]
      simp only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [comb_add_mul, ← hpE]
      have hs := step N
      rw [ih] at *
      linear_combination (norm := module) ((p : E) ^ N) • hs
  choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)
  choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))
  obtain ⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α := ⟨Sc, fun _ => rfl⟩
  have key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧
      f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g := by
    intro N
    choose cB hcB using fun i => hB i N
    choose cS hcS using fun α => hS α N
    obtain ⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α := ⟨cS, fun _ => rfl⟩
    refine ⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩
    · exact ((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc
        (IntD.map hc T)
    · have h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
          (p : E) ^ N • comb cB e := by
        rw [hpE, ← comb_add_mul]
        congr 1
        funext i
        exact hcB i
      have h2 : map (algebraMap O E) S =
          ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) +
            (p : E) ^ N • map (algebraMap O E) T := by
        ext α
        set_option synthInstance.maxHeartbeats 100000 in
          rw [coeff_map, hSd, hcS α, map_add (f := _), map_add (f := _), coeff_smul, coeff_map, hTd, map_sum (coeff α)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]
      rw [h1, h2]
      linear_combination (norm := module) tele N
  have hR : f - comb Bv e - map (algebraMap O E) S = 0 := by
    refine GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E h d μ hμ _ ?_ ?_
    · funext i
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, hb⟩ := hg.1 i
      refine ⟨b, ?_⟩
      rw [hgN]
      simp only [lin, coeff_smul] at hb ⊢
      rw [hb, hpE, map_mul]
    · ext α
      rw [coeff_zero]
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, -, hb⟩ := hg.2 α
      refine ⟨b, ?_⟩
      rw [hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]
  exact ⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩

end GlobalTheory.QLog.Conv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadicStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  first | exact @GlobalTheory.QLog.Conv.generate_of_step | exact GlobalTheory.QLog.Conv.generate_of_step | (intros; apply GlobalTheory.QLog.Conv.generate_of_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogBasis

section Gen

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
  (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)

theorem up_const (h : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp only [up, constantCoeff_map, h, map_zero]

def cobL (h : ∀ i, constantCoeff (μ i) = 0) :
    MvPowerSeries (Fin d) E →ₗ[E] MvPowerSeries (Fin d ⊕ Fin d) E where
  toFun := cob1 (up E μ)
  map_add' := formalCoboundary_add (up_const μ h)
  map_smul' := formalCoboundary_smul (up_const μ h)

theorem cobL_apply (h : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) :
    cobL μ h f = cob1 (up E μ) f := rfl

variable {μ}

theorem in_top_add {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f + g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a + b, trivial, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem in_top_sub {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f - g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a - b, trivial, by rw [map_sub, ha, hb, map_sub]⟩

theorem in_top_smul {σ : Type} {f : MvPowerSeries σ E} (a : O) (hf : In (⊤ : Ideal O) f) :
    In (⊤ : Ideal O) (algebraMap O E a • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨a * b, trivial, by rw [map_smul, hb, smul_eq_mul, map_mul]⟩

theorem in_top_map {σ : Type} {f : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, f = map (algebraMap O E) s := by
  have hf' : ∀ α, ∃ b : O, coeff α f = algebraMap O E b := fun α => by
    obtain ⟨b, -, hb⟩ := hf α
    exact ⟨b, hb⟩
  choose s hs using hf'
  refine ⟨s, ?_⟩
  ext α
  exact (hs α).trans (coeff_map (algebraMap O E) α s).symm

theorem ql_zero (h : ∀ i, constantCoeff (μ i) = 0) : QL μ (⊤ : Ideal O) (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, trivial, by simp [lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
  rw [← cobL_apply μ h, map_zero, map_zero, map_zero]

theorem ql_add_smul (h : ∀ i, constantCoeff (μ i) = 0) {f g : MvPowerSeries (Fin d) E}
    (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) : QL μ ⊤ (f + algebraMap O E a • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h1 := hf.1
    have h2 := hg.1
    rw [← coeff_zero_eq_constantCoeff_apply] at h1 h2 ⊢
    rw [map_add (f := _), map_smul, h1, h2, smul_zero, add_zero]
  · obtain ⟨a1, -, h1⟩ := hf.2.1 i
    obtain ⟨a2, -, h2⟩ := hg.2.1 i
    refine ⟨a1 + a * a2, trivial, ?_⟩
    simp only [lin] at h1 h2 ⊢
    rw [map_add (f := _), map_smul, h1, h2, smul_eq_mul, map_add (f := _), map_mul]
  · rw [← cobL_apply μ h, map_add (f := _), map_smul, cobL_apply, cobL_apply]
    exact in_top_add hf.2.2 (in_top_smul a hg.2.2)

theorem comb_sub {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (b b' : ι → O) :
    comb (b - b') e = comb b e - comb b' e := by
  simp only [comb, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

end Gen

section Chart

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
  {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {E : Type} [CommRing E] [Algebra O E]
  (hE : IsFrame p E (RingHom.id O))
include hv hE

theorem isLie_add {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (hf : QL c.μ ⊤ f)
    (hg : QL c.μ ⊤ g) (hl : c.IsLie f l) (hl' : c.IsLie g l') (a : O) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f g l l' a hl hl').1 hf hg

theorem isLie_int {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (hs : ∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.1 hs

theorem isLie_log {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (h : cob1 (up E c.μ) f = 0) : l = 0 :=
  (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hE f f l l 0 hl hl).2.2 h

theorem isLie_zero : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE 0 (ql_zero c.isLaw.const)
  rwa [isLie_int hv c hE hl ⟨0, (map_zero _).symm⟩] at hl

theorem isLie_comb {ι : Type} [Fintype ι] {e : ι → MvPowerSeries (Fin d) E} {L : ι → G.dual.Lie}
    (he : ∀ i, QL c.μ ⊤ (e i)) (hL : ∀ i, c.IsLie (e i) (L i)) (b : ι → O) :
    c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  have h0 := c.isLaw.const
  suffices ∀ s : Finset ι, QL c.μ ⊤ (∑ i ∈ s, algebraMap O E (b i) • e i) ∧
      c.IsLie (∑ i ∈ s, algebraMap O E (b i) • e i) (∑ i ∈ s, b i • L i) from
    (this Finset.univ).2
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using ⟨ql_zero (E := E) h0, isLie_zero hv c hE⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • L a)]
    exact ⟨ql_add_smul h0 ih.1 (he a) (b a), isLie_add hv c hE ih.1 (he a) ih.2 (hL a) (b a)⟩

theorem exists_isLie (l : G.dual.Lie) : ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l := by
  have h0 := c.isLaw.const
  let M : Submodule O G.dual.Lie :=
    { carrier := {l | ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l}
      add_mem' := by
        rintro l1 l2 ⟨f1, hf1, hl1⟩ ⟨f2, hf2, hl2⟩
        refine ⟨f1 + algebraMap O E 1 • f2, ql_add_smul h0 hf1 hf2 1, ?_⟩
        have := isLie_add hv c hE hf1 hf2 hl1 hl2 1
        rwa [one_smul] at this
      zero_mem' := ⟨0, ql_zero (E := E) h0, isLie_zero hv c hE⟩
      smul_mem' := by
        rintro a l ⟨f, hf, hl⟩
        refine ⟨0 + algebraMap O E a • f, ql_add_smul h0 (ql_zero (E := E) h0) hf a, ?_⟩
        have := isLie_add hv c hE (ql_zero (E := E) h0) hf (isLie_zero hv c hE) hl a
        simpa only [zero_add] using this }
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp : Ideal.span {(p : O)} ≤ (⊥ : Ideal O).jacobson :=
    ((Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (Fact.out : ¬IsUnit (p : O)))).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have htop : (⊤ : Submodule O G.dual.Lie) ≤ M := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hp fun x _ => ?_
    obtain ⟨f, l', l'', hf, hl', rfl⟩ := GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul p C v O hv G d c E hE x
    exact Submodule.add_mem_sup ⟨f, hf, hl'⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  exact htop Submodule.mem_top

end Chart

theorem adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hE
  have h0 := c.isLaw.const
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  let lb := Module.finBasis O G.dual.Lie
  choose F hF using fun j => exists_isLie hv c hE (lb j)
  choose large₂ hLg using fun i : Fin d => GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hE d c.μ c.isLaw (Pi.single i 1)
  have hlin : ∀ i, lin (large₂ i) = Pi.single i 1 := fun i => funext fun i' => by
    rw [(hLg i).2.1 i', Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  let e : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → MvPowerSeries (Fin d) E := Sum.elim large₂ F
  have hQ : ∀ i, QL c.μ ⊤ (e i) := by
    rintro (i | j)
    · refine ⟨(hLg i).1, fun i' => ⟨_, trivial, (hLg i).2.1 i'⟩, fun α => ⟨0, trivial, ?_⟩⟩
      show coeff α (cob1 (up E c.μ) (large₂ i)) = _
      rw [(hLg i).2.2, map_zero, map_zero]
    · exact (hF j).1
  have hcob : ∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0 := fun i => (hLg i).2.2
  have hlin' : ∀ i, lin (e (Sum.inl i)) = Pi.single i 1 := hlin
  have hlie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := fun j => (hF j).2
  let L : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → G.dual.Lie := Sum.elim 0 lb
  have hL : ∀ i, c.IsLie (e i) (L i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hE _ (hQ (Sum.inl i))
      rw [isLie_log hv c hE hl (hcob i)] at hl
      exact hl
    · exact hlie j
  have huniq : ∀ b : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → O, In (⊤ : Ideal O) (comb b e) → b = 0 := by
    intro b hb
    obtain ⟨s, hs⟩ := in_top_map hb
    have hl0 : ∑ i, b i • L i = 0 := isLie_int hv c hE (isLie_comb hv c hE hQ hL b) ⟨s, hs⟩
    have hr : ∀ j, b (Sum.inr j) = 0 := by
      have : ∑ j, b (Sum.inr j) • lb j = 0 := by simpa [Fintype.sum_sum_type, L] using hl0
      exact Fintype.linearIndependent_iff.1 lb.linearIndependent _ this
    have hc : cob1 (up E c.μ) (map (algebraMap O E) s) = 0 := by
      rw [← hs, ← cobL_apply c.μ h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [comb, map_sum, map_smul, Fintype.sum_sum_type, cobL_apply, hcob, hr]
    have hs0 := GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero p C v O hv G d c E hE s hc
    have hc0 : comb b e = 0 := by rw [hs, hs0, map_zero]
    have hl : ∀ i, b (Sum.inl i) = 0 := fun i => by
      have h1 := congrArg (coeff (Finsupp.single i 1)) hc0
      have hco : ∀ i', coeff (Finsupp.single i 1) (e (Sum.inl i')) = (Pi.single i' (1 : E) : Fin d → E) i :=
        fun i' => congrFun (hlin' i') i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [comb, map_sum, Fintype.sum_sum_type, hr, hco, Pi.single_apply] at h1
      exact hE.inj (by rw [map_zero]; simpa [Algebra.smul_def] using h1)
    funext x
    cases x with
    | inl i => exact hl i
    | inr j => exact hr j
  refine ⟨Module.finrank O G.dual.Lie, e, lb, ⟨hQ, fun f hf => ?_⟩,
    fun i => ⟨fun α => ⟨0, (RingHom.mem_ker).2 (map_zero _), by rw [hcob i, map_zero, map_zero]⟩,
      hlin' i⟩, hcob, hlie⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic p O E hE d c.μ c.isLaw _ e hQ
    (GlobalTheory.T.quasiLogarithm_division_step_decomposition p C v O hv G d c E hE _ e lb hQ hcob hlin' hlie) f hf
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have h1 : In (⊤ : Ideal O) (comb (b' - b) e) := by
    rw [comb_sub]
    have := in_top_sub hb hb'
    rwa [sub_sub_sub_cancel_left] at this
  exact sub_eq_zero.1 (huniq _ h1)

end GlobalTheory.QLogBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.QLogBasis.adapted_basis | exact GlobalTheory.QLogBasis.adapted_basis | (intros; apply GlobalTheory.QLogBasis.adapted_basis <;> assumption)
end
