module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariant
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportional
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GoodOriginTowerHeight
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AbelianCmStokesIdentity

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
private theorem cross_ne_zero_of_linearIndependent (a b : Fin 2 → ℤ) (h : LinearIndependent ℤ ![a, b]) :
    a 0 * b 1 - a 1 * b 0 ≠ 0 := by
  intro hd
  rw [LinearIndependent.pair_iff] at h
  by_cases h1 : b 1 = 0 ∧ a 1 = 0
  · obtain ⟨hb1, ha1⟩ := h1
    have h2 := h (b 0) (-(a 0)) (by
      funext i
      fin_cases i <;> simp [hb1, ha1] <;> ring)
    have ha : a = 0 := by
      funext i
      fin_cases i <;> simp_all
    have h3 := h 1 0 (by simp [ha])
    simp at h3
  · have h2 := h (b 1) (-(a 1)) (by
      funext i
      fin_cases i <;> simp <;> first | linear_combination hd | linear_combination -hd | ring)
    exact h1 ⟨h2.1, neg_eq_zero.mp h2.2⟩

private theorem card_le_one_of_linearIndependent_cross_zero (I : Submodule ℤ (Fin 2 → ℤ))
    (hI : ∀ v ∈ I, ∀ w ∈ I, v 0 * w 1 - v 1 * w 0 = 0) (ρ : ℕ) (v : Fin ρ → (Fin 2 → ℤ))
    (hv : ∀ a, v a ∈ I) (hli : LinearIndependent ℤ v) : ρ ≤ 1 := by
  by_contra h
  push_neg at h
  have hli2 : LinearIndependent ℤ ![v ⟨0, by omega⟩, v ⟨1, h⟩] := by
    have h3 := hli.comp (fun i : Fin 2 => (⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩ : Fin ρ))
      (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
    convert h3 using 1
    funext i
    fin_cases i <;> rfl
  exact cross_ne_zero_of_linearIndependent _ _ hli2 (hI _ (hv _) _ (hv _))

private theorem relIndex_span_le_natAbs_of_cross_zero (I : Submodule ℤ (Fin 2 → ℤ))
    (hI : ∀ v ∈ I, ∀ w ∈ I, v 0 * w 1 - v 1 * w 0 = 0) (w : Fin 2 → ℤ) (hw : w ∈ I)
    (hb : w 1 ≠ 0) :
    (Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup ≤ (w 1).natAbs := by
  have hn0 : (w 1).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  haveI : NeZero (w 1).natAbs := ⟨hn0⟩
  let f : I.toAddSubgroup →+ ZMod (w 1).natAbs :=
    (Int.castAddHom (ZMod (w 1).natAbs)).comp
      ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1).toAddMonoidHom.comp
        I.toAddSubgroup.subtype)
  have hker : f.ker ≤ (Submodule.span ℤ {w}).toAddSubgroup.addSubgroupOf I.toAddSubgroup := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    have hx' : (((x : Fin 2 → ℤ) 1 : ℤ) : ZMod (w 1).natAbs) = 0 := hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx'
    obtain ⟨t, ht⟩ : w 1 ∣ (x : Fin 2 → ℤ) 1 := Int.natAbs_dvd.mp hx'
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hxI : (x : Fin 2 → ℤ) ∈ I := x.2
    have hd := hI _ hxI _ hw
    have hy0 : (x : Fin 2 → ℤ) 0 = t * w 0 := by
      have h4 : ((x : Fin 2 → ℤ) 0 - t * w 0) * w 1 = 0 := by
        rw [ht] at hd
        linear_combination hd
      rcases mul_eq_zero.mp h4 with h5 | h5
      · linarith
      · exact absurd h5 hb
    have hy : (x : Fin 2 → ℤ) = t • w := by
      funext i
      fin_cases i
      · simp [hy0]
      · simp [ht, mul_comm]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hdvd := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker] at hdvd
  have hcard : Nat.card f.range ≤ (w 1).natAbs :=
    (Nat.card_le_card_of_injective (fun x : f.range => (x : ZMod (w 1).natAbs))
      Subtype.val_injective).trans (Nat.card_zmod _).le
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  exact (Nat.le_of_dvd hpos hdvd).trans hcard

private theorem corrected_weight_regularization_lemma_5 {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    {D : ComponentData II Ψ K J Ω W} (Cd : CuspData D ℤ (Fin 2 → ℤ)) (z : (Σ k, J k) → ℂ)
    (u : ℝ) (hu : 0 ≤ u) (hform : ∀ v w, Cd.form v w = v 0 * w 1 - v 1 * w 0)
    (n : ℕ) (hn : 0 < n) (A : ℝ) (Q : (Fin 2 → ℤ) → ℝ)
    (hQ : ∀ w : Fin 2 → ℤ, |((w 1 : ℤ) : ℝ)| ≤ Q w)
    (hprod : ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)) (hρ : ρ = 1),
      (∏ τ : Ψ, (Cd.gramLie z τ v).det.re) = (A * Q (v ⟨0, by omega⟩)) ^ n)
    (hA : Real.exp (-u) ≤ A ^ n)
    (hNz0 : Cd.Nz z (Submodule.span ℤ {![1, 0]}) = Real.exp (-u)) :
    Cd.cuspWeight z = u := by
  classical
  let e0 : Fin 2 → ℤ := ![1, 0]
  let I0 : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ {e0}
  have memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0 := by
    intro v
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      simp [e0]
    · intro h
      exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩
  have isoI0 : IsIsoSub Cd.form I0 := by
    intro v hv w hw
    rw [hform, (memI0 v).1 hv, (memI0 w).1 hw]
    ring
  have hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub Cd.form I →
      ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1 := by
    intro I hI ρ v hv
    exact le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hform]; exact hI a ha b hb)
      ρ v hv.2.1 hv.2.2.1) hv.1
  have hmem : u ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)} := by
    refine ⟨I0, ?_, ?_, isoI0, ?_⟩
    · rw [Submodule.ne_bot_iff]
      exact ⟨e0, Submodule.mem_span_singleton_self e0, by simp [e0]⟩
    · intro v k hk hv
      rw [memI0] at hv ⊢
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      rcases mul_eq_zero.mp hv with h | h
      · exact absurd h hk
      · exact h
    · rw [hNz0, Real.log_exp, neg_neg]
  have hub : ∀ x ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)}, x ≤ u := by
    rintro x ⟨I, hne, hsat, hiso, rfl⟩
    by_cases hI : I = I0
    · subst hI
      rw [hNz0, Real.log_exp, neg_neg]
    · rw [CuspData.Nz]
      split_ifs with h
      · have hsp := h.choose_spec.choose_spec
        have hρ := hρ1 I hiso _ _ hsp
        rw [hprod _ _ hρ]
        have hrange : Set.range h.choose_spec.choose = {h.choose_spec.choose ⟨0, by omega⟩} := by
          ext y
          constructor
          · rintro ⟨i, rfl⟩
            have : i = ⟨0, by omega⟩ := Fin.ext (by have := i.2; omega)
            rw [this]
            exact Set.mem_singleton _
          · rintro rfl
            exact ⟨_, rfl⟩
        have hwI := hsp.2.1 ⟨0, by omega⟩
        have hwne := hsp.2.2.1.ne_zero ⟨0, by omega⟩
        have hrel := hsp.2.2.2
        rw [hrange] at hrel
        rw [hrange]
        generalize h.choose_spec.choose ⟨0, by omega⟩ = w at hwI hwne hrel ⊢
        have hw1 : w 1 ≠ 0 := by
          intro hw1
          apply hI
          have hw0 : w 0 ≠ 0 := by
            intro h0'
            apply hwne
            funext i
            fin_cases i <;> simp [h0', hw1]
          apply le_antisymm
          · intro x hx
            rw [memI0]
            have hd : x 0 * w 1 - x 1 * w 0 = 0 := by rw [← hform]; exact hiso x hx w hwI
            rw [hw1] at hd
            have h6 : x 1 * w 0 = 0 := by linarith
            rcases mul_eq_zero.mp h6 with h5 | h5
            · exact h5
            · exact absurd h5 hw0
          · show Submodule.span ℤ {e0} ≤ I
            rw [Submodule.span_le, Set.singleton_subset_iff]
            apply hsat e0 (w 0) hw0
            have h7 : w 0 • e0 = w := by
              funext i
              fin_cases i <;> simp [e0, hw1]
            rw [h7]
            exact hwI
        have hr := relIndex_span_le_natAbs_of_cross_zero I (fun a ha b hb => by rw [← hform]; exact hiso a ha b hb) w hwI hw1
        have hrpos : (0 : ℝ) < ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hrel
        have hrR : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
            ≤ |((w 1 : ℤ) : ℝ)| := by
          have h8 : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℤ)
              ≤ ((w 1).natAbs : ℤ) := by exact_mod_cast hr
          rw [Int.natCast_natAbs] at h8
          rw [← Int.cast_abs]
          exact_mod_cast h8
        have hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hw1
        generalize ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) = r at hrpos hrR ⊢
        have hQ1 := hQ w
        have hQn : Q w ≤ Q w ^ n := le_self_pow₀ (by linarith) hn.ne'
        have hApos : 0 ≤ A ^ n := le_trans (Real.exp_pos _).le hA
        have hkey : Real.exp (- u) ≤ (A * Q w) ^ n / r := by
          rw [mul_pow, le_div_iff₀ hrpos]
          have h1 : r ≤ Q w ^ n := by linarith
          calc Real.exp (-u) * r ≤ A ^ n * r := mul_le_mul_of_nonneg_right hA hrpos.le
            _ ≤ A ^ n * Q w ^ n := mul_le_mul_of_nonneg_left h1 hApos
        have h10 := Real.log_le_log (Real.exp_pos _) hkey
        rw [Real.log_exp] at h10
        linarith
      · rw [Real.log_one, neg_zero]
        exact hu
  unfold CuspData.cuspWeight
  rw [IsGreatest.csSup_eq ⟨hmem, hub⟩, max_eq_right hu]

private theorem exists_cuspData_cuspWeight_eq_of_torus_invariant (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (D : ComponentData II Ψ K J Ω W) [Nonempty Ψ] (U : ((Σ k, J k) → ℂ) → ℝ)
    (hU : ∀ z, 0 ≤ U z)
    (hT : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) :
    ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), ∀ z, Cd.cuspWeight z = U z := by
  classical
  let fm : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
    LinearMap.mk₂ ℤ (fun v w => v 0 * w 1 - v 1 * w 0)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
  have hfm : ∀ v w, fm v w = v 0 * w 1 - v 1 * w 0 := fun _ _ => rfl
  let e0 : Fin 2 → ℤ := ![1, 0]
  let I0 : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ {e0}
  have memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0 := by
    intro v
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      simp [e0]
    · intro h
      exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩
  have isoI0 : IsIsoSub fm I0 := by
    intro v hv w hw
    rw [hfm, (memI0 v).1 hv, (memI0 w).1 hw]
    ring
  have hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub fm I →
      ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1 := by
    intro I hI ρ v hv
    exact le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb)
      ρ v hv.2.1 hv.2.2.1) hv.1
  have h0 : ∃ (ρ : ℕ) (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I0 ρ v := by
    refine ⟨1, ![e0], le_rfl, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      exact Submodule.mem_span_singleton_self e0
    · rw [linearIndependent_unique_iff]
      simp [e0]
    · have h1 : Submodule.span ℤ (Set.range ![e0]) = I0 := by simp [I0]
      rw [h1, AddSubgroup.relIndex_self]
      exact one_ne_zero
  have hs0 : IsNzFamily I0 h0.choose h0.choose_spec.choose := h0.choose_spec.choose_spec
  have hρ0 : h0.choose = 1 := hρ1 I0 isoI0 _ _ hs0
  let w0 : Fin 2 → ℤ := h0.choose_spec.choose ⟨0, hs0.1⟩
  have hw0I : w0 ∈ I0 := hs0.2.1 _
  have hw0ne : w0 ≠ 0 := hs0.2.2.1.ne_zero _
  have hw01 : w0 1 = 0 := (memI0 w0).1 hw0I
  have ha0 : w0 0 ≠ 0 := by
    intro h
    apply hw0ne
    funext i
    fin_cases i <;> simp [h, hw01]
  let r0 : ℕ := (Submodule.span ℤ (Set.range h0.choose_spec.choose)).toAddSubgroup.relIndex
    I0.toAddSubgroup
  have hr0 : r0 ≠ 0 := hs0.2.2.2
  have hr0R : (1 : ℝ) ≤ r0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
  let n : ℕ := Fintype.card Ψ
  have hn : 0 < n := Fintype.card_pos
  have hmN : 0 < D.N - D.j := by
    have := D.j_le
    have := D.two_le_N
    have := D.one_le_j
    omega
  have hm : (0 : ℝ) < ((D.N - D.j : ℕ) : ℝ) := by exact_mod_cast hmN
  let ε : ℝ := 1 / |((w0 0 : ℤ) : ℝ)|
  have ha0R : ((w0 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hε : 0 < ε := one_div_pos.mpr (abs_pos.mpr ha0R)
  have hεa : ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 = 1 := by
    simp only [ε, div_pow, one_pow, sq_abs]
    field_simp
  let s : ((Σ k, J k) → ℂ) → ℝ := fun z =>
    Real.exp ((Real.log r0 - U z) / n) / ((D.N - D.j : ℕ) : ℝ)
  have hs : ∀ z, 0 < s z := fun z => div_pos (Real.exp_pos _) hm
  have hms : ∀ z, (((D.N - D.j : ℕ) : ℝ) * s z) ^ n = r0 * Real.exp (- U z) := by
    intro z
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e1 : ((D.N - D.j : ℕ) : ℝ) * s z = Real.exp ((Real.log r0 - U z) / n) := by
      simp only [s]
      field_simp
    rw [e1, ← Real.exp_nat_mul,
      show (n : ℝ) * ((Real.log r0 - U z) / n) = Real.log r0 - U z by field_simp,
      Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]
  let Q : (Fin 2 → ℤ) → ℝ := fun w => ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2
  let L : (Fin 2 → ℤ) → ℂ := fun w =>
    ((ε * ((w 0 : ℤ) : ℝ) : ℝ) : ℂ) + ((((w 1 : ℤ) : ℝ)) : ℂ) * Complex.I
  have hL : ∀ w, ‖L w‖ ^ 2 = Q w := by
    intro w
    simp only [L, Q]
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hLne : ∀ w : Fin 2 → ℤ, w ≠ 0 → L w ≠ 0 := by
    intro w hw h
    have hq := hL w
    rw [h, norm_zero] at hq
    have hA := mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))
    have hB := sq_nonneg ((w 1 : ℤ) : ℝ)
    simp only [Q] at hq
    have h1 : ((w 1 : ℤ) : ℝ) ^ 2 = 0 := by linarith
    have h2 : ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 = 0 := by linarith
    have h2' : ((w 0 : ℤ) : ℝ) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (pow_ne_zero 2 hε.ne')
      · exact h3
    have e0' : w 0 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2'
    have e1' : w 1 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1
    apply hw
    funext i
    fin_cases i <;> simp [e0', e1']
  let σ : ((Σ k, J k) → ℂ) → ℝ := fun z => Real.sqrt (s z)
  have hσ : ∀ z, σ z ^ 2 = s z := fun z => Real.sq_sqrt (hs z).le
  have hσpos : ∀ z, 0 < σ z := fun z => Real.sqrt_pos.mpr (hs z)
  have hsT : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → s (torusSmul c z) = s z := by
    intro z hz c hc
    simp only [s, hT z hz c hc]
  have hC : ∀ z, 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z := fun z => by
    have := hs z
    positivity
  let Cd : CuspData D ℤ (Fin 2 → ℤ) :=
    { rank := 2
      basis := Pi.basisFun ℤ (Fin 2)
      form := fm
      alt := fun v => by rw [hfm]; ring
      unimod := by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, hfm, Pi.basisFun_apply]
      emb := fun _ => Int.castRingHom ℂ
      normSq := fun z v => ((n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1) *
        (((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2)
      normSq_pos := by
        intro z _ v hv
        have hC1 : 0 < (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1 := by
          have := hC z
          positivity
        apply mul_pos hC1
        by_contra hle
        push_neg at hle
        have h1 : ((v 0 : ℤ) : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]
        have h2 : ((v 1 : ℤ) : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]
        have e0' : v 0 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1
        have e1' : v 1 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2
        apply hv
        funext i
        fin_cases i <;> simp [e0', e1']
      form_le := by
        intro z _ v w
        rw [hfm]
        push_cast
        have hC1 : 1 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1 := by
          have := hC z
          have : 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) := by positivity
          linarith
        set C := (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1
        set A := ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2 with hA
        set B := ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 with hB
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by positivity
        have hlag : (((v 0 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ) - ((v 1 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ)) ^ 2 ≤ A * B := by
          rw [hA, hB]
          nlinarith [sq_nonneg (((v 0 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ) + ((v 1 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ))]
        have hAB : A * B ≤ (C * A) * (C * B) := by
          have hCC : 1 ≤ C * C := by nlinarith
          nlinarith [mul_nonneg hA0 hB0]
        linarith
      lie := fun z _ v _ => ((σ z : ℝ) : ℂ) * L v
      lie_add := by
        intro z τ v w
        funext c
        simp only [L, Pi.add_apply]
        push_cast
        ring
      lie_smul := by
        intro z τ a v
        funext c
        simp only [L, Pi.smul_apply, smul_eq_mul, Int.coe_castRingHom]
        push_cast
        ring
      lie_le := by
        intro z _ v
        have hterm : ‖((σ z : ℝ) : ℂ) * L v‖ ^ 2 = s z * Q v := by
          rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hterm]
        have h1 := hC z
        have h2 := mul_nonneg (hC z) (sq_nonneg ((v 0 : ℤ) : ℝ))
        have h3 := mul_nonneg (hC z) (mul_nonneg (sq_nonneg ε) (sq_nonneg ((v 1 : ℤ) : ℝ)))
        have h4 := sq_nonneg ((v 0 : ℤ) : ℝ)
        have h5 := sq_nonneg ((v 1 : ℤ) : ℝ)
        show (n : ℝ) * (((D.N - D.j : ℕ) : ℝ) * (s z * (ε ^ 2 * ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2))) ≤ _
        nlinarith
      inj := by
        intro z _ τ I hI ρ v hvI hli
        have hρ : ρ ≤ 1 := card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb)
          ρ v hvI hli
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hρ with rfl | rfl
        · exact linearIndependent_empty_type
        · rw [linearIndependent_unique_iff]
          intro h
          have h1 := congrFun h ⟨0, hmN⟩
          simp only [Pi.zero_apply] at h1
          rcases mul_eq_zero.mp h1 with h2 | h2
          · exact (hσpos z).ne' (by exact_mod_cast h2)
          · exact hLne _ (hli.ne_zero default) h2
      torus := by
        intro z hz c hc
        have h := hsT z hz c hc
        constructor
        · funext v
          simp only [h]
        · funext τ v w
          simp only [σ, h] }
  have hent : ∀ z τ (w : Fin 2 → ℤ),
      (∑ c : Fin (D.N - D.j), (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c).re
        = ((D.N - D.j : ℕ) : ℝ) * (s z * Q w) := by
    intro z τ w
    have h1 : ∀ c, (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c = ((s z * Q w : ℝ) : ℂ) := by
      intro c
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
      congr 1
      show ‖((σ z : ℝ) : ℂ) * L w‖ ^ 2 = _
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hprod : ∀ z ρ (v : Fin ρ → (Fin 2 → ℤ)) (hρ : ρ = 1),
      (∏ τ : Ψ, (Cd.gramLie z τ v).det.re)
        = (((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩)) ^ n := by
    intro z ρ v hρ
    subst hρ
    have h1 : ∀ τ, (Cd.gramLie z τ v).det.re
        = ((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩) := by
      intro τ
      rw [Matrix.det_unique, _root_.mul_assoc]
      exact hent z τ (v default)
    rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_const, Finset.card_univ]
  have hNz0 : ∀ z, Cd.Nz z I0 = Real.exp (- U z) := by
    intro z
    rw [CuspData.Nz, dite_eq_left h0, hprod z _ _ hρ0]
    have hQ : Q (h0.choose_spec.choose ⟨0, by omega⟩) = 1 := by
      show ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 + ((w0 1 : ℤ) : ℝ) ^ 2 = 1
      rw [hεa, hw01]
      simp
    rw [hQ, _root_.mul_one, hms z]
    show (r0 : ℝ) * Real.exp (- U z) / (r0 : ℝ) = _
    have : (r0 : ℝ) ≠ 0 := by linarith
    field_simp
  have hQge : ∀ w : Fin 2 → ℤ, |((w 1 : ℤ) : ℝ)| ≤ Q w := by
    intro w
    have h9 : |((w 1 : ℤ) : ℝ)| ≤ ((w 1 : ℤ) : ℝ) ^ 2 ∨ ((w 1 : ℤ) : ℝ) = 0 := by
      by_cases hw : w 1 = 0
      · right
        simp [hw]
      · left
        have hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hw
        rw [← sq_abs]
        nlinarith
    have := mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))
    show _ ≤ ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2
    rcases h9 with h9 | h9
    · linarith
    · rw [h9]
      simp
      positivity
  have hA : ∀ z, Real.exp (- U z) ≤ (((D.N - D.j : ℕ) : ℝ) * s z) ^ n := by
    intro z
    rw [hms z]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hr0R
  exact ⟨Cd, fun z => corrected_weight_regularization_lemma_5 Cd z (U z) (hU z) hfm n hn _ Q hQge (hprod z) (hA z) (hNz0 z)⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd _ _ M U S S' rd Lval Ch Cu hS hS' hU hT hPos hConj hHt hMean
  obtain ⟨Cd, hCd⟩ := exists_cuspData_cuspWeight_eq_of_torus_invariant K J II Ψ Ω W D U hU hT
  have hw : Cd.cuspWeight = U := funext hCd
  have hcorr : cuspCorr Hd Cd = corrW Hd U := by
    funext z
    simp only [cuspCorr, corrW, hCd]
  revert S' hS' hPos hConj hHt
  rw [← hcorr]
  intro S' hS' hPos hConj hHt
  refine ⟨⟨Hd, Cd, M, S, hS, S', hS', rd, Lval⟩, rfl, fun z _ => hCd z, rfl, rfl, hPos, hConj,
    ?_, ?_, ?_⟩
  · intro B p q hB hp hpq
    obtain ⟨t₀, ht₀, h⟩ := hHt B p q hB hp hpq
    exact ⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩
  · intro B p q hB hp hpq
    obtain ⟨t₀, ht₀, h⟩ := hHt B p q hB hp hpq
    exact ⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩
  · intro hj hN B hB
    show meanU Hd Cd ≤ _
    rw [meanU, hw]
    exact hMean hj hN B hB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  first | exact @GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | exact GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | (intros; apply GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionTower
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelay
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  first | exact @LevelTowerAlt.good_origin_tower_height | exact LevelTowerAlt.good_origin_tower_height
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  exact @GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StokesLimitIffPosOfResK
noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImage
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SheetDecomposition.PF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  intro II hII K _ ρ _ K' _ ρ' _ κ v P' d r G Jf L L' N hv hP' hP hJ hL hLL' hN
  have hA : IsArithVar P' (d + r + 1) := by rwa [Nat.add_right_comm] at hP'
  have hs : ∀ j, IsSmoothHerm (Fin.append L' N j) := fun j => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      exact GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hv (hLL' j) (hL j)
    · rw [Fin.append_right]
      exact hN j
  have h := GlobalTheory.T.projection_formula_of_arith_system ⟨II, hII⟩ II hII.1 K ρ K' ρ' κ v P' (d + 1) r G Jf
    (Fin.snoc (α := fun _ => HermLine ρ) L (cst ρ)) (Fin.snoc (α := fun _ => HermLine ρ') L' (cst ρ')) N hv hP' hP hJ
    (LevelTowerAlt.snoc_cst_smooth L hL)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.snoc_last]
        refine ⟨?_, fun z => rfl⟩
        show (0 : K' → ℤ) = pullDeg κ 0
        funext k
        by_cases hk : ∃ a, κ a = k
        · obtain ⟨a, rfl⟩ := hk
          exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
        · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm
      · simpa using hLL' j)
    hN
  rw [LevelTowerAlt.ii_cst_int hII.1 hP L hL, ← position_eq, ii_cast hII.1 _ hA _ (LevelTowerAlt.snoc_cst_smooth _ hs), LevelTowerAlt.ii_cst_int hII.1 hA _ hs,
    mul_neg, neg_inj] at h
  exact h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | exact GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | (intros; apply GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionTower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem testPoly_eq_slX : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  intro hAg hPr hCmp hGiv hPts E _ _ _ _ H D Xo l c Y _ T o II hGl hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or hB hBB hqp hbg hsm hGood hgen hS
  have hIn : PB.Inputs := hGiv.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty (CMType H) := GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.cm_nonempty H
  have hUnif := GlobalTheory.T.good_tower_real_agreement hGiv E H D Xo l c Y T o II hGl hEx hII hp hq
  have hProp : T.Proportional :=
    GlobalTheory.T.real_tower_proportional hPr hIn II hII (CMType H) (D.p + D.q) T (Top.realOf o.toTowerOrigin) hUnif
  have hJpos : 0 < Top.testDeg (CMType H) (D.p + D.q) T.j :=
    (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) T.j T.j_pos T.j_lt).2.1
  have hLim : ArLimExists X.H X.S B :=
    (GlobalTheory.T.height_comparison_between_models hGiv hPts K J II (CMType H) Ω W Dc X.H X.M X.M X.S X.S B hII X.S_tied X.S_tied).1
  have hMass := (GlobalTheory.T.measure_limit_statement_holds II (CMType H) K J Ω W Dc O Lt X B hII.1 hLim).2
  have hSm := GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II (CMType H) Ω W Dc X.H X.M X.S B X.S_tied
  obtain ⟨K₃, _, ι₃, _, κ, v, P₃, e, r, cf, Mt, Nt, δ, hb, hY, himg, hδ, hdeg, hNs, hpull, hT, hGeo⟩ :=
    GlobalTheory.T.good_origin_intersection_relay hAg hPr hCmp hGiv hPts E H D Xo l c Y T o II hGl hEx hII hp hq B B₁ a K J Ω W Dc O Lt X Or hB hBB hqp hbg hsm hGood hgen hS
  have hXar : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (imageZ v P₃) (Dc.n + 1) := by rw [himg]; exact Dc.arith
  obtain ⟨G⟩ := GlobalTheory.CompanionTheory.Ar.PB.Known.genFibreExists K J K₃ ι₃ κ v P₃ _ hb hY
  obtain ⟨Jf, hJf, -⟩ := (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers G.Φ (FibreBlock κ) (fibreIdx ι₃ κ)).1
  have hPF := GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩
  set fibN : Fin r → ℝ := fun m => (Jf (fibreIdeal κ G) e (fun i => fibreDeg κ (Nt 1 m i).a) : ℝ) with hfibN
  set fib : ℝ := ∑ m, cf m * fibN m with hfib
  have hEq1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m)) =
      fib * arLimFun X.H X.S B t := by
    filter_upwards [hSm, hpull] with t ht hp'
    rw [hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := hPF II hII.1 K J K₃ ι₃ κ v P₃ (Dc.n + 1) e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt t m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs t m)
    have hd : (fun i => fibreDeg κ (Nt t m i).a) = fun i => fibreDeg κ (Nt 1 m i).a := by
      funext i; rw [hdeg t m i]
    rw [h, himg, hd]
    simp only [arLimFun, hfibN]
    ring
  have hEq2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      fib * geomDeg (mCoordIdeal Dc.y) (muReg X.H X.S B t) Dc.n := by
    filter_upwards [hSm, hpull, hGeo] with t ht hp' hg
    rw [← hg, hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image II hII K J K₃ ι₃ κ v P₃ Dc.n e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt 1 m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs 1 m)
    rw [h, himg]
    simp only [geomDeg, hfibN]
    ring
  obtain ⟨L, hL⟩ := hLim
  have hA : arLim X.H X.S B = L := hL.limUnder_eq
  have h1 : δ * T.PPc II B a (Top.testPoly T.j) = fib * L :=
    tendsto_nhds_unique hT ((hL.const_mul fib).congr' (hEq1.mono fun t h => h.symm))
  have h2 : δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * degMu X.H :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hEq2) (hMass.const_mul fib)
  have h3 : (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := hProp.2.1 B a _
  rw [h3] at h2
  have hvol : 0 < T.vol a := hProp.1 a
  have hvJ : 0 < T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := mul_pos hvol hJpos
  have hpos : 0 < fib * degMu X.H := by rw [← h2]; exact mul_pos hδ hvJ
  have hd0 : 0 ≤ degMu X.H := GlobalTheory.CompanionTheory.StokesCompare.degMu_nonneg X
  have hdpos : 0 < degMu X.H := by
    refine lt_of_le_of_ne hd0 fun h => ?_
    rw [← h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hdpos, ⟨L, hL⟩, ?_⟩
  have hj : Dc.j = D.p := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · obtain ⟨τ⟩ := (inferInstance : Nonempty (CMType H))
      have := congrFun (hbg.symm.trans h) τ
      simp at this
  have hNn : Dc.N = D.p + D.q := Or.N_eq
  have hdim : ((Dc.n + 1 : ℕ) : ℝ) = (Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1 := by
    have hjT : T.j = D.p := o.j_eq
    have : Dc.n = Top.dimX (CMType H) (D.p + D.q) T.j := by
      simp only [ComponentData.n, Top.dimX, hj, hNn, hjT]
      ring
    rw [this]
    push_cast
    ring
  have hne : ((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) ≠ 0 := by positivity
  have hsl : slX X B = L / (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * degMu X.H) := by
    rw [slX, hA, hdim]
  rw [hsl]
  apply mul_left_cancel₀ hδ.ne'
  rw [h1]
  have hdn := hdpos.ne'
  field_simp
  linear_combination (-L) * h2

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionTowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_tower : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX | exact GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @ModelDimension.abelian_cm_stokes_identity | exact ModelDimension.abelian_cm_stokes_identity
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | exact GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_final_estimate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopBase

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem base_setting_of_good_origin : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  intro Ch Cu hNine hWeil hAgr hProp hCmp hGiven hPts E _ _ _ _ H D Xo l c Y _ T o II hGlob hExtra hFull hp hq hqp
    hbad B hB a
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have := hne
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr hne
  have hN2 : 2 ≤ D.p + D.q := by omega
  have hsq : 4 ≤ (D.p + D.q) ^ 2 := by nlinarith
  have hB16 : 16 * Fintype.card (CMType H) ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by omega
  have hB4 : 4 * Fintype.card (CMType H) + 2 ≤ B := by omega
  have hgen : genPt (o.Or B a).𝔐.ξ₀ = genPt (o.Fx a).ξf :=
    genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset ℕ, ∀ r, r ∈ S₁ ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad :=
    ⟨(Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ∉ T.bad), by
      intro r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩⟩
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp => ((o.bad_iff p).1 hp).1
  have hS₁P : ∀ p ∈ S₁, p.Prime := fun p hp => ((hS₁ p).1 hp).1
  have hdisj : Disjoint S₁ T.bad := Finset.disjoint_left.2 fun p hp hp' => ((hS₁ p).1 hp).2.2 hp'
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ T.bad := fun p hp hd =>
    (o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have horigin :=
    GlobalTheory.T.full_intersection_generic_bound hGiven hWeil E H D Xo l c Y II hFull hGlob hp hq _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ T.bad S₁
      false hbadP hS₁P hdisj hdisc
  obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, hgen', hS, hj, hbg, -, hHT⟩ := horigin
  simp only [Bool.false_eq_true, ite_false] at hj hbg
  have hsm : Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨h, -, -⟩
    · exact h
    · exact absurd (congrFun (hbg.symm.trans h) hne.some) Sum.inl_ne_inr
  have hGood : Or.Good :=
    ⟨fun p hp => hHT p (Finset.mem_union_left _ hp),
      fun p hp => hHT p (Finset.mem_union_right _ (by rw [← hS]; exact hp))⟩
  have hSc : ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad := by
    intro r; rw [hS]; exact hS₁ r
  have hN : Dc.N = D.p + D.q := Or.N_eq
  have hAdm : admitted Xo l c Y Or B := by
    refine ⟨hGlob, hGood, o.bad_iff, ?_, ?_, hSc, ?_⟩
    · show T.bad.card ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2
      rw [hN]; exact hbad
    · exact hB4
    · show Dc.N - Dc.j ≤ Dc.j
      rw [hN, hj]; omega
  obtain ⟨U, M, S, S', hcw, hU0, hUt, hSt, hS't, hconj⟩ :=
    GlobalTheory.T.cusp_weight_regularisations_tied hGiven E H D Xo l c Y II K J Ω W Dc Hd T.bad Or
  obtain ⟨hpos, hht, hmean⟩ := hNine E H D Xo l c Y II K J Ω W Dc Hd T.bad Or B U M S' hFull hAdm hcw hS't
  obtain ⟨X, hXH, hXU, hXrd, hXL, hX1, hX2, hX3, hX4, hX5⟩ :=
    GlobalTheory.T.corrected_weight_regularization K J II (CMType H) Ω W Dc Hd M U S S' (hostRd E) (hostLval H) Ch Cu hSt hS't hU0 hUt hpos hconj
      hht hmean
  subst hXH
  obtain ⟨hdeg, hlim, hPP⟩ := GlobalTheory.T.good_origin_intersection_tower hAgr hProp hCmp hGiven hPts E H D Xo l c Y T o II hGlob hExtra hFull hp hq
    B B a K J Ω W Dc ℤ (Fin 2 → ℤ) X Or hB2 le_rfl hqp hbg hsm hGood (hgen'.trans hgen) hSc
  obtain ⟨-, -, hSemi, -, hResK, -, -, hGaga, -, hInputs, -, hAn, -, -⟩ := hGiven
  have hStk : Top.StokesAt X B :=
    GlobalTheory.T.intersection_final_estimate hInputs hAn hResK hGaga hSemi E H D Xo l c Y II K J Ω W Dc X.H T.bad Or B U hFull hAdm hcw ℤ
      (Fin 2 → ℤ) X rfl hXU hX1 B hB4 hlim
  exact ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, W, inferInstance, inferInstance, Dc, ℤ,
    Fin 2 → ℤ, inferInstance, inferInstance, inferInstance, X, hN, hj.trans o.j_eq.symm, hXrd, hXL, hX1, hX2, hX3, hX4,
    hX5, hdeg, hlim, hStk, hPP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_setting_of_good_tower : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : _root_.GlobalTheory.CompanionTheory.Ar.Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.TopBase.base_setting_of_good_origin
end
