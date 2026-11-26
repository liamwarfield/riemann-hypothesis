module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NormRepMoveOfSteps
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem normRepMove_of_steps (D : D7) (u u' : D.what₂.Word) (hE : TermEqIff D u u')
    (h1 : StepExp D) (h2 : StepGram D) (h3 : StepGlob D) (h4 : StepLoc D) (h5 : StepTr D) :
    PI.NormRepChange.NormRepMove D u u' := by
  intro F0 Λ hΛ t _hrel F₁ F₂ hR1 hA1 hR2 hA2 w _hw
  obtain ⟨p1, e1⟩ := hR1
  obtain ⟨p2, e2⟩ := hR2
  have hDC : DCRel Λ (lf D F0) F₁ F₂ :=
    ((hE F0 Λ hΛ) ⟨F₁, p1⟩ ⟨F₂, p2⟩).mp (e1.trans e2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hDC
  obtain ⟨hNu, hNe⟩ := h1 Λ (lf D F0) n hn
  obtain ⟨hMu, hMe⟩ := h1 Λ F₁ m hm
  have hG := h2 (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hNe hMe hfr
  obtain ⟨A, B, hA, hB, hZ, hs⟩ := core_Z _ _ _ _ hNu hMu hG
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  rw [hs]
  obtain ⟨_, ⟨_, _, hLift0, hConv0⟩, hXS0⟩ := hΛ
  obtain ⟨hLift1, _, hConv1, hXS1⟩ := p1
  have hglob : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E,
      (o : D.host.E) = (sgUp (fmat D (lf D F0) n) + sgUp (fmat D F₁ m)) * δ := by
    intro δ hδ
    obtain ⟨o1, ho1⟩ := h3 Λ (lf D F0) n hn hXS0 hLift0.1 δ hδ
    obtain ⟨o2, ho2⟩ := h3 Λ F₁ m hm hXS1 hLift1.1 δ hδ
    exact ⟨o1 + o2, by rw [add_mul, ← ho1, ← ho2]; norm_cast⟩
  have hloc := h4 Λ (lf D F0) F₁ F₂ n m hn hm hfr hConv0 hConv1 hA1 hA2 hLift0.1 hLift1.1
  obtain ⟨k, hk⟩ := h5 _ hglob hloc
  exact psiInf_of_trace (gS D) _ _ k hk

end PI.NRCW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.TraceIntOfMulDd
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem coe_algebraMap_OF (D : D7) (δ : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (δ : D.host.F) := rfl

theorem trace_int_of_mul_dd (D : D7) (x : D.host.E)
    (hx : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * δ) :
    ∃ k : ℤ, Algebra.trace ℚ D.host.E x = k := by
  have ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F),
      ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
    intro δ hδ
    have hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D := by
      unfold ddS
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩
    obtain ⟨o, ho⟩ := hx _ hmem
    have htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
      rw [ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    rw [htr] at hint
    exact ⟨⟨_, hint⟩, rfl⟩
  have hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F,
      FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha'⟩ := ha y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨a, by rw [mul_comm]; exact ha'⟩
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)] at hdual
  obtain ⟨k, hk⟩ := hdual 1 (FractionalIdeal.one_mem_one _)
  refine ⟨k, ?_⟩
  have h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x) := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]
  simp

theorem stepTr (D : D7) : StepTr D := by
  intro y hy hP
  have hg0 : (gS D : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  have hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ := by
    intro δ hδ
    obtain ⟨o, ho⟩ := hy δ hδ
    have hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ := by
      unfold ddS at hδ
      obtain ⟨d', -, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hδ
      exact ⟨d', hd'⟩
    obtain ⟨d', rfl⟩ := hδint
    have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1 := by
      intro P
      by_cases hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · rw [map_mul]
        exact mul_le_one' (hP P hPg) (P.valuation_le_one d')
      · have h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1 := by
          have h2 := (P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg
          simpa using h2
        have e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E) := by ring
        rw [e, map_div₀, h1, div_one, ← ho]
        exact P.valuation_le_one o
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)
    exact ⟨o', ho'⟩
  obtain ⟨k, hk⟩ := trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint
  refine ⟨k, ?_⟩
  have e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E)) := by
    rw [Algebra.smul_def, map_natCast]
    field_simp
  rw [e, LinearMap.map_smul, hk, smul_eq_mul]

end PI.NRCW
end
end

noncomputable section

open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_representative_move (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (hS : Formalism.L2.SG.TermDef.TermStable D u u') (hE : Formalism.L2.SG.TermDef.TermEqIff D u u') (hF : Formalism.L2.SG.TermDef.TermFun D u u') (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hsig : (Formalism.MainNotions.S.VS D).SigOK) : PI.NormRepChange.NormRepMove D u u' :=
  PI.NRCW.normRepMove_of_steps D u u' hE (PI.NRCW.stepExp D) (PI.NRCW.stepGram D) (PI.NRCW.stepGlob D)
    (PI.NRCW.stepLoc D) (PI.NRCW.stepTr D)
