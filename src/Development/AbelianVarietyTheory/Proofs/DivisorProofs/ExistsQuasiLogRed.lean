module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCocycleAdditiveLawReductionCoboundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardAdditiveLawWittVectorFractionFieldModP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardAdditiveLawWittVectorFractionFieldModP
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem algebraMap_pow_ne_zero (m : ℕ) :
    algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) ≠ 0 := fun h =>
  pow_ne_zero m (WittVector.p_nonzero p k)
    (IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [h, map_zero]))

theorem coeff_wsmul {σ : Type} (w : WittVector p k) (f : MvPowerSeries σ (Fr p k))
    (α : σ →₀ ℕ) : coeff α (w • f) = algebraMap (WittVector p k) (Fr p k) w * coeff α f := by
  rw [← Algebra.smul_def]; rfl

theorem mem_one_of_p_smul {σ : Type} (f : MvPowerSeries σ (Fr p k))
    (hf : (p : WittVector p k) • f ∈ intBy p k σ (p : WittVector p k)) : f ∈ intBy p k σ 1 := by
  intro α
  obtain ⟨w, hw⟩ := hf α
  refine ⟨w, ?_⟩
  rw [coeff_wsmul, map_mul] at hw
  rw [one_mul]
  have h0 := algebraMap_pow_ne_zero p k 1
  rw [pow_one] at h0
  exact mul_left_cancel₀ h0 hw

theorem exists_pow_smul_mem {d N : ℕ} (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
    (he : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) :
    ∃ m : ℕ, ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) := by
  classical
  have hfin := Finsupp.finite_of_degree_le (σ := Fin d ⊕ Fin d) N
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (WittVector p k)) (hfin.toFinset.image fun γ => coeff γ e)
  have hb0 : (b : WittVector p k) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (b : WittVector p k) hb0
  refine ⟨n + 1, fun γ => ?_⟩
  by_cases hγ : γ.degree = N
  · have hmem : coeff γ e ∈ hfin.toFinset.image fun γ => coeff γ e :=
      Finset.mem_image.2 ⟨γ, by simp [hγ], rfl⟩
    obtain ⟨w, hw⟩ := hb _ hmem
    refine ⟨((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) * w, ?_⟩
    have hw' : algebraMap (WittVector p k) (Fr p k) w =
        algebraMap (WittVector p k) (Fr p k) (b : WittVector p k) * coeff γ e := by
      rw [hw, Algebra.smul_def]
    have hu1 : algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) *
        algebraMap (WittVector p k) (Fr p k) (u : WittVector p k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_mul, map_pow] at hw'
    rw [coeff_wsmul, map_mul, map_mul, map_pow, pow_succ]
    linear_combination (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) *
      algebraMap (WittVector p k) (Fr p k) ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hw' +
      (-algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) ^ n *
        algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) * coeff γ e) * hu1
  · refine ⟨0, ?_⟩
    rw [coeff_wsmul, he γ hγ]
    simp

theorem lift_addLaw (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext γ
  rw [coeff_lift]
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : γ = Finsupp.single (Sum.inl i) 1
  · have h2 : γ ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h; exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    simp only [if_pos h1, if_neg h2, add_zero, map_one, map_one]
  · by_cases h2 : γ = Finsupp.single (Sum.inr i) 1
    · simp only [if_neg h1, if_pos h2, zero_add, map_one, map_one]
    · simp only [if_neg h1, if_neg h2, add_zero, WittVector.teichmuller_zero, map_zero]

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz.LazardModP

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]

theorem step (d N : ℕ) (hN : 2 ≤ N) (m : ℕ) : ∀ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) →
    swap e - e ∈ intBy p k _ (p : WittVector p k) →
    ((p : WittVector p k) ^ m) • e ∈ intBy p k _ (p : WittVector p k) →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ (p : WittVector p k) := by
  have hconst : ∀ i, constantCoeff (addLaw (Fr p k) d i) = 0 := fun i => by simp [addLaw]
  have hA := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst 0
  have hlaw : IsLaw (addLaw (Fr p k) d) := hA.2.2.2.2.1
  have hcob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconst 0 0
    rwa [zero_smul, zero_smul] at this
  have hR := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hR3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have hRC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (fun i => by simp [addLaw])
  rw [lift_addLaw] at hRC
  induction m with
  | zero =>
    intro e _ _ _ hm
    refine ⟨0, fun _ _ => by simp, ?_⟩
    rw [hcob0, sub_zero]
    simpa using hm
  | succ m ih =>
    intro e he hcb hsw hm
    have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)), ((p : WittVector p k) ^ m) • x =
        algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m) • x :=
      fun x => (algebraMap_smul (Fr p k) _ x).symm
    have hQ := algebraMap_pow_ne_zero p k m
    rw [pow_succ', mul_smul] at hm
    have he' := mem_one_of_p_smul p k _ hm
    obtain ⟨c, hc⟩ := (hR.1 _).1 he'
    have hcb' : cob2 (addLaw (Fr p k) d) (((p : WittVector p k) ^ m) • e) ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).1, ← hsm]
      exact Submodule.smul_mem _ _ hcb
    have hsw' : swap (((p : WittVector p k) ^ m) • e) - ((p : WittVector p k) ^ m) • e ∈
        intBy p k _ (p : WittVector p k) := by
      rw [hsm, (hA.2.2.2.1 _ e).2, ← smul_sub, ← hsm]
      exact Submodule.smul_mem _ _ hsw
    obtain ⟨hr2, hrs⟩ := hRC.1 _ _ hc
    have hc2 : cob2 (addLaw k d) c = 0 := hR3.2.1 _ _ _ hr2 ((hR3.2.2.2.2.2.1 _).1 hcb')
    have hcs : swap c = c := sub_eq_zero.1
      (hR.2.1 _ _ _ (hR.2.2.2.1 _ _ _ _ hrs hc).2 ((hR.2.2.2.2.2.1 _).1 hsw'))
    have hch : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0 := by
      intro γ hγ
      obtain ⟨w, hw1, hw2⟩ := hc γ
      rw [coeff_wsmul, he γ hγ, mul_zero] at hw1
      have hw0 : w = 0 := IsFractionRing.injective (WittVector p k) (Fr p k) (by rw [← hw1, map_zero])
      rw [← hw2, hw0, map_zero]
    obtain ⟨h', hh', hred⟩ := GlobalTheory.T.homogeneous_cocycle_additiveLaw_reduction_coboundary p k d N c hN ⟨hc2, hcs⟩ hch
    have hdiff : ((p : WittVector p k) ^ m) • e - cob1 (addLaw (Fr p k) d) h' ∈
        intBy p k _ (p : WittVector p k) := by
      have := (hR.2.2.2.1 _ _ _ _ hc hred).2
      rw [sub_self] at this
      exact (hR.2.2.2.2.2.1 _).2 this
    have hcobh1 : ((p : WittVector p k) ^ m) • cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') =
        cob1 (addLaw (Fr p k) d) h' := by
      rw [hsm, ← formalCoboundary_smul hconst, smul_smul, mul_inv_cancel₀ hQ, one_smul]
    have hh1 : ∀ α : Fin d →₀ ℕ, α.degree ≠ N →
        coeff α ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h') = 0 := by
      intro α hα
      rw [coeff_smul, hh' α hα, mul_zero]
    have hcoc := (GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (addLaw (Fr p k) d) hconst
      ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h')).2.2.2.2.2 hlaw
    obtain ⟨h2, hh2, hfin⟩ := ih (e - cob1 (addLaw (Fr p k) d)
        ((algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h'))
      (fun γ hγ => by
        rw [map_sub, he γ hγ, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).1 _ hh1 γ hγ, sub_zero])
      (by rw [((hA.2.2.1) e _).2.1, hcoc.1, sub_zero]; exact hcb)
      (by
        rw [((hA.2.2.1) e _).2.2, hcoc.2]
        convert hsw using 1
        abel)
      (by rw [smul_sub, hcobh1]; exact hdiff)
    refine ⟨(algebraMap (WittVector p k) (Fr p k) ((p : WittVector p k) ^ m))⁻¹ • h' + h2,
      fun α hα => by rw [map_add (f := _), hh1 α hα, hh2 α hα, add_zero], ?_⟩
    rw [formalCoboundary_add hconst]
    convert hfin using 1
    abel

end GlobalTheory.Katz.LazardModP

namespace GlobalTheory.Katz

theorem lazard_mod_p_frac : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N →
    (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) →
    cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p →
    ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧
      e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  intro p _ k _ _ _ d N e hN he hcb hsw
  obtain ⟨m, hm⟩ := LazardModP.exists_pow_smul_mem p k e he
  exact LazardModP.step p k d N hN m e he hcb hsw hm

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardAdditiveLawWittVectorFractionFieldModPStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)), 2 ≤ N → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0) → cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ p → swap e - e ∈ intBy p k _ p → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ e - cob1 (addLaw (Fr p k) d) h ∈ intBy p k _ p := by
  first | exact @GlobalTheory.Katz.lazard_mod_p_frac | exact GlobalTheory.Katz.lazard_mod_p_frac | (intros; apply GlobalTheory.Katz.lazard_mod_p_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStep
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt {R τ : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : τ →₀ ℕ, γ.degree < M → coeff γ (at2 c u v) = 0 := by
  intro γ hγ
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := by
    rintro (i | i)
    · exact hu i
    · exact hv i
  have hs : HasSubst (Sum.elim u v) := hasSubst_of_constantCoeff_zero ha
  have h1 : (1 : ℕ∞) ≤ ⨅ s, (Sum.elim u v s).order := le_iInf fun s => by
    apply MvPowerSeries.le_order
    intro δ hδ
    have h0 : δ.degree = 0 := by exact_mod_cast ENat.lt_one_iff_eq_zero.mp hδ
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact ha s
  have h2 : (M : ℕ∞) ≤ c.order := MvPowerSeries.le_order fun δ hδ => hc δ (by exact_mod_cast hδ)
  have h3 := le_order_subst hs c
  unfold at2
  apply coeff_of_lt_order
  calc (γ.degree : ℕ∞) < M := by exact_mod_cast hγ
    _ ≤ 1 * c.order := by rw [one_mul]; exact h2
    _ ≤ (⨅ s, (Sum.elim u v s).order) * c.order := mul_le_mul_left h1 _
    _ ≤ _ := h3

theorem coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree < M → coeff γ (cob2 μ c) = 0 := by
  intro γ hγ
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    rw [← coeff_zero_eq_constantCoeff_apply]
    refine coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt (μ i) u v hu hv 1 (fun α hα => ?_) 0 (by simp)
    have h0 : α.degree = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact hμ i
  unfold cob2
  simp only [map_add (f := _), map_sub]
  rw [coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx2 hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ (hop _ _ hx1 hx2) hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 (hop _ _ hx2 hx3) M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 hx2 M hc γ hγ]
  simp

theorem degree_mapDomain_swap_ord {d : ℕ} (γ : Fin d ⊕ Fin d →₀ ℕ) :
    (γ.mapDomain Sum.swap).degree = γ.degree := by
  induction γ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a n => rw [Finsupp.mapDomain_single, Finsupp.degree_single, Finsupp.degree_single]

end GlobalTheory.Katz

theorem GlobalTheory.Katz.quasiLog_approx_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc N f hN hf hlow
  have hL0 : ∀ i, constantCoeff ((fun i => Katz.lift p (μ i)) i) = 0 :=
    fun i => constantCoeff_lift p (hμ.const i)
  have CC := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL0 0
  have Q := GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p p k d μ hμ f hf
  have RD := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have RD3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have RC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have LIN := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have LEAD := GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) N (fun i α hα => (LIN i α hα).2)
  have HOM := GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N
  obtain ⟨g, hg⟩ : ∃ g, g = cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c := ⟨_, rfl⟩
  rw [← hg] at hlow

  have hg2 : cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (cob2 (fun i => Katz.lift p (μ i)) (Katz.lift p c)) 0 := by
      have := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).1
      rwa [hc.1] at this
    rw [hg, (CC.2.2.1 _ _).2.1]
    exact sub_mem Q.1 ((RD3.2.2.2.2.2.1 _).2 h1)
  have hgs : swap g - g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (swap (Katz.lift p c) - Katz.lift p c) 0 := by
      have a := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).2
      rw [hc.2] at a
      have := (RD.2.2.2.1 _ _ _ _ a (RD.2.2.1 c)).2
      rwa [sub_self] at this
    have : swap g - g = (swap (cob1 (fun i => Katz.lift p (μ i)) f) -
        cob1 (fun i => Katz.lift p (μ i)) f) - (swap (Katz.lift p c) - Katz.lift p c) := by
      rw [hg, (CC.2.2.1 _ _).2.2]; abel
    rw [this]
    exact sub_mem Q.2 ((RD.2.2.2.2.2.1 _).2 h1)

  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ e = if γ.degree = N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree = N then coeff γ g else 0, fun γ => rfl⟩
  obtain ⟨low, hlo⟩ : ∃ low : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ low = if γ.degree < N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree < N then coeff γ g else 0, fun γ => rfl⟩
  have hhigh : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → coeff γ (g - low - e) = 0 := by
    intro γ hγ
    rw [map_sub, map_sub, he, hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1, if_neg (by omega)]; ring
    · rw [if_neg h1, if_pos (by omega)]; ring
  have hlowI : low ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1]; exact hlow γ h1
    · rw [if_neg h1]; exact ⟨0, by simp⟩
  have ehom : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0 := by
    intro γ hγ; rw [he, if_neg hγ]
  have eord : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → coeff γ e = 0 :=
    fun γ hγ => ehom γ (by omega)
  have hcob2e : cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    by_cases hγ : γ.degree = N
    · rw [← LEAD.2 e eord γ hγ.le]
      have hsplit : e = g - low - (g - low - e) := by abel
      have hz := coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt (fun i => Katz.lift p (μ i)) hL0
        (g - low - e) (N + 1) hhigh γ (by omega)
      obtain ⟨w1, hw1⟩ := hg2 γ
      obtain ⟨w2, hw2⟩ := (RC.2.2.2 _ low hlowI).1 γ
      refine ⟨w1 - w2, ?_⟩
      rw [hsplit, (CC.2.2.1 _ _).2.1, (CC.2.2.1 _ _).2.1, map_sub, map_sub, hz, hw1, hw2,
        mul_sub, map_sub, sub_zero]
    · rw [HOM.2.1 e ehom γ hγ]; exact ⟨0, by simp⟩
  have hswape : swap e - e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [map_sub, HOM.2.2.1, he, he, degree_mapDomain_swap_ord]
    by_cases hγ : γ.degree = N
    · rw [if_pos hγ, if_pos hγ]
      obtain ⟨w, hw⟩ := hgs γ
      rw [map_sub, HOM.2.2.1] at hw
      exact ⟨w, hw⟩
    · rw [if_neg hγ, if_neg hγ]; exact ⟨0, by simp⟩
  obtain ⟨h, hhom, hint⟩ := GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p p k d N e hN ehom hcob2e hswape
  have hord : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0 := fun α hα => hhom α (by omega)
  have hsub : cob1 (fun i => Katz.lift p (μ i)) (f - h) =
      cob1 (fun i => Katz.lift p (μ i)) f - cob1 (fun i => Katz.lift p (μ i)) h := by
    rw [eq_sub_iff_add_eq, ← formalCoboundary_add hL0, sub_add_cancel]
  have K : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k,
      coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) =
        algebraMap (WittVector p k) (Fr p k) (p * w) := by
    intro γ hγ
    have e1 : cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c =
        g - cob1 (fun i => Katz.lift p (μ i)) h := by rw [hsub, hg]; abel
    rw [e1, map_sub]
    obtain ⟨hL1, hL2⟩ := LEAD.1 h hord γ
    by_cases h1 : γ.degree < N
    · rw [hL1 h1, sub_zero]; exact hlow γ h1
    · have hN' : γ.degree = N := by omega
      rw [hL2 hN'.le]
      have : coeff γ g = coeff γ e := by rw [he, if_pos hN']
      rw [this, ← map_sub]
      exact hint γ
  have hnegq : -h ∈ quasiInt p k (Fin d) := by
    intro α i
    by_cases hα : α.degree = N
    · refine GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N f (-h) hN hf
        (fun β hβ => by rw [map_neg, hord β hβ, neg_zero]) (fun γ hγ => ?_) α i hα
      obtain ⟨w, hw⟩ := K γ (by omega)
      refine ⟨p * w + WittVector.teichmuller p (coeff γ c), ?_⟩
      rw [← sub_eq_add_neg, map_add (f := _), ← hw, map_sub, coeff_lift]; ring
    · rw [map_neg, hhom α hα, neg_zero, mul_zero]; exact ⟨0, by simp⟩
  refine ⟨h, hhom, sub_mem hf ((neg_mem_iff).1 hnegq), K⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStepStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_successive_approximation_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.Katz.quasiLog_approx_step | exact GlobalTheory.Katz.quasiLog_approx_step | (intros; apply GlobalTheory.Katz.quasiLog_approx_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModP
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WittStart

theorem eq_zero_or_single {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ι →₀ ℕ) (h : γ.degree < 2) :
    γ = 0 ∨ ∃ s, γ = Finsupp.single s 1 := by
  by_cases h0 : γ = 0
  · exact Or.inl h0
  right
  obtain ⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Finsupp.ext hc)
  rw [Finsupp.degree_eq_sum] at h
  have hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  refine ⟨s, Finsupp.ext fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    have : ∑ i ∈ Finset.univ.erase t, γ i ≥ 0 := Nat.zero_le _
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_apply, Ne.symm hts, if_false]
    have : γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)
    omega

variable {R : Type} [CommRing R] {d : ℕ}

theorem coeff_single_linear_substitution_pair {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (at2 c u v) =
      ∑ i, coeff (Finsupp.single (Sum.inl i) 1) c * coeff (Finsupp.single t 1) (u i) +
      ∑ i, coeff (Finsupp.single (Sum.inr i) 1) c * coeff (Finsupp.single t 1) (v i) := by
  unfold at2
  rw [GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]
  · rfl
  · rintro (i | i)
    · exact hu i
    · exact hv i

theorem constantCoeff_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  unfold op at2
  rw [constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]
  exact hμ0 i

theorem coeff_single_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) (t : τ) :
    coeff (Finsupp.single t 1) (op μ u v i) =
      coeff (Finsupp.single t 1) (u i) + coeff (Finsupp.single t 1) (v i) := by
  classical
  unfold op
  rw [coeff_single_linear_substitution_pair _ _ _ hu hv]
  simp only [hμ, addLaw, map_add (f := _), GlobalTheory.FormalCalc.coeff_single_X]
  simp [add_mul, Finset.sum_add_distrib]

theorem coeff_single_coc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0)
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : IsCoc μ c) (s : Fin d ⊕ Fin d) :
    coeff (Finsupp.single s 1) c = 0 := by
  classical
  have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0 := by
    intro j
    have h := congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1
    unfold cob2 at h
    rw [map_sub, map_add (f := _), map_sub, map_zero,
      coeff_single_linear_substitution_pair _ _ _ hx2 hx3,
      coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3,
      coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3),
      coeff_single_linear_substitution_pair _ _ _ hx1 hx2] at h
    simp only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3,
      GlobalTheory.FormalCalc.coeff_single_X] at h
    simpa using h
  cases s with
  | inl j => exact hinl j
  | inr j =>
    have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2
    unfold swap at h
    rw [coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
    simp only [GlobalTheory.FormalCalc.coeff_single_X] at h
    simp only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    simp [hinl]

end GlobalTheory.WittStart

namespace GlobalTheory.WittStart

theorem start : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c →
    ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc w
  classical
  have hL := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1 := fun s => by
    rw [Finsupp.degree_single]
  have hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i) :=
    fun i s => (hL i _ (hdeg s)).1
  have hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) =
      coeff (Finsupp.single s 1) (addLaw (Fr p k) d i) := fun i s => (hL i _ (hdeg s)).2
  have hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hclin := coeff_single_coc hμ.const hμk c hc
  set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x)
    with hT
  set f : MvPowerSeries (Fin d) (Fr p k) :=
    (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) +
      ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf
  have hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then T (w i) else 0 := by
    intro α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, map_add (f := _), map_sum]
    have e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)),
        coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g := fun r g => by
      rw [← algebraMap_smul (Fr p k) r g, coeff_smul]
    simp only [e, coeff_one, coeff_X, hT, map_neg]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
  refine ⟨f, ?_, ?_, ?_⟩
  · intro α
    rw [hcoeff α]
    refine ⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [one_mul, map_add (f := _), map_sum]
    congr 1
    · split_ifs <;> simp [hT]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hT]
  · intro i
    refine ⟨WittVector.teichmuller p (w i), ?_, ?_⟩
    · show coeff _ f = _
      rw [hcoeff]
      simp [Finsupp.single_eq_single_iff, hT]
    · rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  · intro γ hγ
    refine ⟨0, ?_⟩
    rw [mul_zero, map_zero]
    rcases eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩
    · have h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1 :=
        fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm
      rw [coeff_zero_eq_constantCoeff_apply, map_sub]
      unfold cob1 inL inR
      rw [map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _),
        constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]
      simp [hT, coeff_zero_eq_constantCoeff_apply, h0s]
    · rw [map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]
      unfold cob1 inL inR
      rw [map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F,
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _),
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]
      simp only [hμF, addLaw, map_add (f := _), mul_add, Finset.sum_add_distrib]
      ring

end GlobalTheory.WittStart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModPStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cob1_witt_lift_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.WittStart.start | exact GlobalTheory.WittStart.start | (intros; apply GlobalTheory.WittStart.start <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeqOfStep
namespace GlobalTheory.SequenceFromIteration

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hstep : ∀ (n : ℕ) (a : A), P n a → ∃ b : A, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n : ℕ, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  choose g hgP hgQ using hstep
  let G : (n : ℕ) → {a : A // P n a} := fun n =>
    Nat.rec (motive := fun n => {a : A // P n a}) ⟨a₀, h₀⟩
      (fun k x => ⟨g k x.1 x.2, hgP k x.1 x.2⟩) n
  exact ⟨fun n => (G n).1, rfl, fun n => ⟨(G n).2, hgQ n (G n).1 (G n).2⟩⟩

end GlobalTheory.SequenceFromIteration
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRed
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hs : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  first
  | exact @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | (apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step ..)

theorem exists_limit_of_steps {R σ : Type} [CommRing R] (F : ℕ → MvPowerSeries σ R)
    (hF : ∀ n (α : σ →₀ ℕ), α.degree ≠ n + 2 → coeff α (F (n + 1)) = coeff α (F n)) :
    ∃ f : MvPowerSeries σ R, ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → coeff α f = coeff α (F n) := by
  have stab : ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → ∀ m, n ≤ m →
      coeff α (F m) = coeff α (F n) := by
    intro n α hα m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hF m α (by omega), ih]
  refine ⟨fun α => coeff α (F α.degree), fun n α hα => ?_⟩
  change coeff α (F α.degree) = _
  rw [← stab α.degree α (by omega) (max n α.degree) (le_max_right _ _),
    stab n α hα _ (le_max_left _ _)]

theorem exists_quasiLog_red (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) :
    ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h,
      Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  intro c hc w
  obtain ⟨f₀, hf₀, hw, hb⟩ := GlobalTheory.T.exists_cob1_witt_lift_mod_p p k d μ h c hc w
  have hq₀ : f₀ ∈ quasiInt p k (Fin d) := by
    intro α i
    obtain ⟨v, hv⟩ := hf₀ α
    exact ⟨(α i : WittVector p k) * (1 * v), by rw [hv, map_mul _ (α i : WittVector p k), map_natCast]⟩
  obtain ⟨F, hF0, hF⟩ := exists_seq_of_step
    (fun n (f : MvPowerSeries (Fin d) (Fr p k)) => f ∈ quasiInt p k (Fin d) ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < n + 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w))
    (fun n a b => ∀ α : Fin d →₀ ℕ, α.degree ≠ n + 2 → coeff α b = coeff α a) f₀ ⟨hq₀, hb⟩
    (by
      intro n a ha
      obtain ⟨g, hg0, hg1, hg2⟩ := GlobalTheory.T.quasiLogarithm_successive_approximation_step p k d μ h c hc (n + 2) a (by omega) ha.1 ha.2
      exact ⟨a - g, ⟨hg1, hg2⟩, fun α hα => by rw [map_sub, hg0 α hα, sub_zero]⟩)
  obtain ⟨f, hf⟩ := exists_limit_of_steps F fun n => (hF n).2
  have hq : f ∈ quasiInt p k (Fin d) := by
    intro α i
    rw [hf α.degree α (by omega)]
    exact (hF α.degree).1.1 α i
  have hp : cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c ∈ intBy p k (Fin d ⊕ Fin d) p := by
    intro γ
    obtain ⟨v, hv⟩ := (hF γ.degree).1.2 γ (by omega)
    refine ⟨v, ?_⟩
    have h1 := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) (γ.degree + 2)
      (fun i α hα => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ h i α hα).2)).1 (f - F γ.degree)
      (fun α hα => by rw [map_sub, hf _ α hα, sub_self]) γ).1 (by omega)
    have h2 := formalCoboundary_add (fun i => constantCoeff_lift p (h.const i)) (f - F γ.degree) (F γ.degree)
    rw [sub_add_cancel] at h2
    rw [h2, add_sub_assoc, map_add (f := _), h1, zero_add, hv]
  obtain ⟨r1, -, r3, r4, -, r6, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hred : Red p (cob1 (fun i => Katz.lift p (μ i)) f) c := by
    have := (r4 _ _ _ _ ((r6 _).1 hp) (r3 c)).1
    rwa [sub_add_cancel, zero_add] at this
  refine ⟨f, ⟨hq, (r1 _).2 ⟨c, hred⟩⟩, hred, ?_⟩
  have hl : lin f = lin f₀ := by
    funext i
    unfold lin
    rw [hf 0 _ (by simp), hF0]
  rw [hl]
  exact hw

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRedStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  first | exact @GlobalTheory.Katz.exists_quasiLog_red | exact GlobalTheory.Katz.exists_quasiLog_red | (intros; apply GlobalTheory.Katz.exists_quasiLog_red <;> assumption)
end
