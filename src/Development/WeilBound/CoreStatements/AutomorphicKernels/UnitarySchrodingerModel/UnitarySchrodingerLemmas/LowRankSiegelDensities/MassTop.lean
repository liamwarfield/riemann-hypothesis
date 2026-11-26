module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SharpCount
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.OneVecBinaryMassOf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PfSWUS.HMass

def SharpCount : Prop :=
  ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ),
    Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, s ≠ 0 →
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤
      (Fintype.card k : ℝ) ^ (M - 1)

theorem real_bound2 (q N Nf : ℝ) (hq : 0 < q) (M : ℕ) (hM : 1 ≤ M)
    (h : |Nf - q ^ (2 * M - 1)| ≤ q ^ (M - 1)) (h1 : N ≤ Nf) (h2 : Nf ≤ N + 1) :
    |N * (q⁻¹) ^ (2 * M - 1) - 1| ≤ 1 / q ^ M + 1 / q ^ (2 * M - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1] at h ⊢
  rw [e2] at h
  have hQ : q ^ (2 * m + 1) = q ^ (m + 1) * q ^ m := by rw [← pow_add]; congr 1; omega
  have hQpos : 0 < q ^ (2 * m + 1) := by positivity
  have habs : |N - q ^ (2 * m + 1)| ≤ q ^ m + 1 := by
    obtain ⟨h3, h4⟩ := abs_le.1 h
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have e3 : N * (q⁻¹) ^ (2 * m + 1) - 1 = (N - q ^ (2 * m + 1)) / q ^ (2 * m + 1) := by
    rw [inv_pow]; field_simp
  rw [e3, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
  have hm1 : q ^ (m + 1) ≠ 0 := by positivity
  have e4 : (1 / q ^ (m + 1) + 1 / q ^ (2 * m + 1)) * q ^ (2 * m + 1) = q ^ m + 1 := by
    rw [add_mul, one_div, one_div, inv_mul_cancel₀ hQpos.ne', hQ, ← mul_assoc, inv_mul_cancel₀ hm1, one_mul]
  rw [e4]
  exact habs

section Loc

open GlobalTheory.CompanionTheory.SW.LGPrim

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem coreSharp (hSC : SharpCount) (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hBs : B.IsSymm)
    (hBint : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hBdet : Valued.v B.det = 1)
    (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v)
    (hs : s ∈ v.adicCompletionIntegers F) (hsu : Valued.v s = 1) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M +
        1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  classical
  let 𝒪 := v.adicCompletionIntegers F
  let 𝓴 := IsLocalRing.ResidueField 𝒪
  let res := IsLocalRing.residue 𝒪
  have hLoc := GlobalTheory.T.completion_is_local_ring F v
  haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, hcard⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hlam
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)
  letI : Fintype 𝓴 := Fintype.ofFinite _
  have hcardk : Fintype.card 𝓴 = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨BO, rfl⟩ : ∃ BO : Matrix ι ι 𝒪, BO.map phi = B :=
    ⟨Matrix.of fun i j => ⟨B i j, hBint i j⟩, by ext i j; rfl⟩
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  let c : 𝒪 := ⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩
  have hc : (c : Fv F v) = 2⁻¹ := rfl
  have hc2 : c * 2 = 1 := by
    apply Subtype.ext
    have e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2 := map_mul _ _ _
    have e2 : (phi : 𝒪 →+* Fv F v) 2 = 2 := map_ofNat _ 2
    have e3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [e2, e3, inv_mul_cancel₀ h20] at e
    exact e
  have hr1 : res c * 2 = 1 := by
    have := congrArg res hc2
    rwa [map_mul, map_one, map_ofNat] at this
  have hr : res c = 2⁻¹ := eq_inv_of_mul_eq_one_left hr1
  have hchar : ringChar 𝓴 ≠ 2 := by
    intro h
    have h0 : (2 : 𝓴) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := 𝓴)
      rw [h] at this
      exact_mod_cast this
    rw [h0, mul_zero] at hr1
    exact zero_ne_one hr1
  have hBO : BO.IsSymm := by
    exact Matrix.IsSymm.ext fun i j => Subtype.ext (congrFun (congrFun hBs i) j)
  have hBks : (BO.map res).IsSymm := hBO.map _
  have hBkdet : (BO.map res).det ≠ 0 := by
    intro h0
    have e : res BO.det = (BO.map res).det := RingHom.map_det res BO
    rw [← e] at h0
    have h3 := (res_eq_zero_iff _).1 h0
    have e2 : ((BO.det : 𝒪) : Fv F v) = (BO.map phi).det := RingHom.map_det phi BO
    rw [e2, hBdet] at h3
    exact lt_irrefl _ h3
  set sb : 𝓴 := res (⟨s, hs⟩ : 𝒪) with hsb
  have hsb0 : sb ≠ 0 := by
    intro h0
    have h' := (res_eq_zero_iff _).1 h0
    change Valued.v s < 1 at h'
    rw [hsu] at h'
    exact lt_irrefl _ h'
  have hcount := hSC 𝓴 hchar ι M hM hM1 (BO.map res) hBks hBkdet sb hsb0
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  let T : Finset (ι → 𝓴) := Fl.filter fun y => y ≠ 0
  have hN : Nat.card {x : ι → 𝓴 // (2 : 𝓴)⁻¹ * (x ⬝ᵥ ((BO.map res) *ᵥ x)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])
  rw [hN, hcardk] at hcount
  have hle1 : T.card ≤ Fl.card := Finset.card_filter_le _ _
  have hle2 : Fl.card ≤ T.card + 1 := by
    have hsub : Fl ⊆ insert 0 T := by
      intro y hy
      by_cases h0 : y = 0
      · simp [h0]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, h0⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hqpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  refine ⟨(T.card : ℝ≥0) * ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ (2 * M - 1), ?_, fun A hA hAs => ?_⟩
  · push_cast
    exact real_bound2 _ _ (Fl.card : ℝ) hqpos M hM1 hcount (by exact_mod_cast hle1)
      (by exact_mod_cast hle2)
  · set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
    have hQc : Continuous Qf := by
      refine continuous_const.mul ?_
      exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    let P : (ι → 𝓴) → Set (ι → Fv F v) := fun y =>
      {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}
    let T0 : Finset (ι → 𝓴) := Finset.univ.filter fun y => y ≠ 0
    have hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
        (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
        ⋃ y ∈ T0, P y := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨h1, h3, h4⟩
        obtain ⟨y, hy, h⟩ := (cover x).1 ⟨h1, h3⟩
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩
      · rintro ⟨y, hy, h, h4⟩
        obtain ⟨h1, h3⟩ := (cover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩
        exact ⟨h1, h3, h4⟩
    have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} :=
      by
      have h := (Valued.isOpen_ball (Fv F v) 1).measurableSet
      simpa [Valuation.restrict_lt_iff_lt_embedding] using h
    have hmeas : ∀ y ∈ T0, MeasurableSet (P y) := by
      intro y _
      have e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A := by
        ext x
        simp [P]
      rw [e]
      refine (MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)
      exact ((continuous_apply i).sub continuous_const).measurable hball
    have hdisj : Set.PairwiseDisjoint (↑T0) P := by
      intro y _ y' _ hne
      exact Set.disjoint_left.2 fun x hx hx' => hne (eq_of_close x y y' hx.1 hx'.1)
    have hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) =
        if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (2 * M - 1)) * lam A else 0 := by
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
      obtain ⟨hint, hprim⟩ := (cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
      obtain ⟨a, haQ, har⟩ := res_Q c hc hr BO y
      have key := GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
      have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
      rw [hkey, hM]
      have hcl : Valued.v (s - Qf (lf y)) < 1 ↔ qk y = sb := by
        have := res_eq_iff (⟨s, hs⟩ : 𝒪) a
        rw [har] at this
        rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
        exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
      split_ifs with he
      · have hlt := hcl.2 he
        have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
          refine Set.inter_eq_left.2 fun z hz => ?_
          have h5 : Valued.v (z - s) < 1 := hAs hz
          have h6 := Valuation.map_add_lt _ h5 hlt
          have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
          rw [e] at h6
          exact h6
        rw [this]
      · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
          have h5 : Valued.v (z - s) < 1 := hAs hz.1
          have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
          have h7 := Valuation.map_sub_lt _ h6 h5
          have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
          rw [e] at h7
          exact h7
        rw [this, measure_empty, mul_zero]
    rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hT : T0.filter (fun y => qk y = sb) = T := by
      ext y
      simp [T0, T, Fl, and_comm]
    rw [hT]
    have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by exact_mod_cast hq0
    push_cast [ENNReal.coe_inv hq0']
    rw [mul_assoc]

theorem dens_unit (hSC : SharpCount) (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (h2 : Valued.v (2 : Fv F v) = 1) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v))
    (hBs : B.IsSymm) (hBint : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hBdet : Valued.v B.det = 1)
    (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v) (hsu : Valued.v s = 1) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ M ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  have hs : s ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hsu.le
  obtain ⟨Dp, hDp, hprim⟩ := coreSharp hSC lam hlam h2 ι B hBs hBint hBdet M hM hM1 s hs hsu
  obtain ⟨π, hπ⟩ := GlobalTheory.CompanionTheory.SW.GBall.exists_unif v
  have hqN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hqN.le
  refine ⟨Dp, ?_, fun A hA hsub => ?_⟩
  · refine hDp.trans ?_
    have h3 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hq (by omega))
    have h4 : 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ M =
        1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M := by ring
    rw [h4]
    linarith
  · have hball : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => by
      have := hsub hz
      rw [hsu] at this
      exact this
    rw [← hprim A hA hball]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hQ⟩
      refine ⟨hx, ?_, hQ⟩
      by_contra hnp
      have h5 := GlobalTheory.CompanionTheory.SW.GBall.q_nonprim h2 hBint hπ hx hnp
      have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) - s) < Valued.v s := hsub hQ
      have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
      rw [hv, hsu] at h5
      have hlt1 : WithZero.exp (-2 : ℤ) < 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.2 (by norm_num)
      exact absurd h5 (not_le.2 hlt1)
    · rintro ⟨hx, -, hQ⟩
      exact ⟨hx, hQ⟩

end Loc

section Lat

theorem lattice_unit (hSC : SharpCount) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ s : Fv F v, Valued.v s = 1 → |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ M := by
  intro F E _ _ _ _ _ σ hCM M J hJ h3 d b
  classical
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM M J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hd, mul_comm]
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent] with v hv2 hvd hve lam hlam m hm s hsu
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  obtain ⟨D, hD1, hD⟩ := dens_unit hSC lam hlam hv2' (Fin M × Fin d)
    (B.map (algebraMap F (Fv F v))) (hBs.map _) (fun i j => hve i j) hdet M hcard h3 s hsu
  rw [GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM M J hJ d b v (B.map (algebraMap F (Fv F v))) (fun x y => hBt (Fv F v) x y)
    lam hlam m hm s hs0 D hD]
  exact hD1

end Lat

theorem oneVecBinaryMass_of (hSC : SharpCount) : OneVecBinaryMass := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM2 d b
  subst hM2
  refine ⟨2, ?_⟩
  filter_upwards [lattice_unit hSC F E σ hCM 2 J hJ (by norm_num) d b] with v hv lam hl m hm s hs
  exact hv lam hl m hm s hs

end PositivityTheory.PfSWUS.HMass
end
end

open MeasureTheory Matrix ComplexConjugate

noncomputable section

namespace PositivityTheory.PfSWUS.HMass.SC

open GlobalTheory.CompanionTheory.SW.QuadricCount

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem sum_sq_eq (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0) :
    ∑ y : k, ψ (a * y ^ 2) = ∑ u : k, (quadraticChar k u : ℂ) * ψ (a * u) := by
  have h1 : ∑ y : k, ψ (a * y ^ 2) =
      ∑ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) * ψ (a * u) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : k => y ^ 2) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [h1]
  have h2 : ∀ u : k, ((Finset.univ.filter fun y : k => y ^ 2 = u).card : ℂ) =
      (quadraticChar k u : ℂ) + 1 := by
    intro u
    have := quadraticChar_card_sqrts hF u
    have e : ({x : k | x ^ 2 = u}.toFinset) = Finset.univ.filter fun y : k => y ^ 2 = u := by
      ext; simp
    rw [e] at this
    exact_mod_cast this
  simp_rw [h2, add_mul, one_mul, Finset.sum_add_distrib]
  have h3 : ∑ u : k, ψ (a * u) = 0 := by
    have hp := AddChar.IsPrimitive.of_ne_one hψ
    have := AddChar.sum_mulShift a hp
    simpa [ha, mul_comm] using this
  rw [h3, add_zero]

theorem sum_sq_scale (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a t : k) (ha : a ≠ 0)
    (ht : t ≠ 0) :
    ∑ y : k, ψ (t * a * y ^ 2) = (quadraticChar k t : ℂ) * ∑ y : k, ψ (a * y ^ 2) := by
  rw [sum_sq_eq hF ψ hψ (t * a) (mul_ne_zero ht ha), sum_sq_eq hF ψ hψ a ha, Finset.mul_sum]
  have hsq : (quadraticChar k t : ℂ) * quadraticChar k t = 1 := by
    have := quadraticChar_sq_one ht
    rw [sq] at this
    exact_mod_cast this
  refine Fintype.sum_equiv (Equiv.mulLeft₀ t ht) _ _ (fun u => ?_)
  show (quadraticChar k u : ℂ) * ψ (t * a * u) =
    (quadraticChar k t : ℂ) * ((quadraticChar k (t * u) : ℂ) * ψ (a * (t * u)))
  have hm : quadraticChar k (t * u) = quadraticChar k t * quadraticChar k u := map_mul _ _ _
  rw [show a * (t * u) = t * a * u by ring, hm]
  push_cast
  linear_combination (-(quadraticChar k u : ℂ) * ψ (t * a * u)) * hsq

theorem addChar_sum (ψ : AddChar k ℂ) {α : Type} [DecidableEq α] (s : Finset α) (f : α → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) :=
  Finset.induction_on s (by simp) (fun a s ha ih => by
    rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_const (hF : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (t : k)
    (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (1 * quadForm B x) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hF
  letI : Invertible (2 : k) := invertibleOfNonzero h2
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm k (ι → k), β = Matrix.toBilin' B := ⟨_, rfl⟩
  have hβapp : ∀ x y, β x y = x ⬝ᵥ (B *ᵥ y) := fun x y => by rw [hβ]; exact Matrix.toBilin'_apply' B x y
  have hsymm : β.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  have hn2 : Module.finrank k (ι → k) = 2 * M := by rw [Module.finrank_fintype_fun_eq_card, hM]
  obtain ⟨w, hw⟩ : ∃ w : Fin (Module.finrank k (ι → k)) → k, w = fun i => β (v i) (v i) := ⟨_, rfl⟩
  have hdiag : ∀ c : Fin (Module.finrank k (ι → k)) → k, β (v.equivFun.symm c) (v.equivFun.symm c) = ∑ i, w i * c i ^ 2 := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [hw]; ring
    · intro j _ hji
      have : β (v j) (v i) = 0 := hv hji
      rw [this]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i hi
    apply v.ne_zero i
    have hall : ∀ y, β (v i) y = 0 := by
      intro y
      have hy := v.sum_equivFun y
      rw [← hy]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i
      · subst hj; rw [show β (v j) (v j) = w j by rw [hw], hi, mul_zero]
      · rw [show β (v i) (v j) = 0 from hv (Ne.symm hj), mul_zero]
    have hB0 : B *ᵥ v i = 0 := by
      have h' : ∀ y, (B *ᵥ v i) ⬝ᵥ y = 0 := by
        intro y
        have := hall y
        rw [hβapp, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq] at this
        rw [dotProduct_comm] at this ⊢
        simpa [dotProduct_comm] using this
      funext j
      have := h' (Pi.single j 1)
      simpa using this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hB0
  have hQ : ∀ (s : k) (c : Fin (Module.finrank k (ι → k)) → k), s * quadForm B (v.equivFun.symm c) = ∑ i, s * (2 : k)⁻¹ * w i * c i ^ 2 := by
    intro s c
    unfold quadForm
    rw [← hβapp, hdiag c, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hS : ∀ s : k, ∑ x, ψ (s * quadForm B x) = ∏ i, ∑ y : k, ψ (s * (2 : k)⁻¹ * w i * y ^ 2) := by
    intro s
    rw [← Fintype.sum_equiv v.equivFun.symm (fun c => ψ (s * quadForm B (v.equivFun.symm c)))
      (fun x => ψ (s * quadForm B x)) (fun _ => rfl)]
    simp_rw [hQ s, addChar_sum]
    rw [Fintype.prod_sum]
  rw [hS t, hS 1]
  have hfac : ∀ i, ∑ y : k, ψ (t * (2 : k)⁻¹ * w i * y ^ 2) =
      (quadraticChar k t : ℂ) * ∑ y : k, ψ (1 * (2 : k)⁻¹ * w i * y ^ 2) := by
    intro i
    have := sum_sq_scale hF ψ hψ ((2 : k)⁻¹ * w i) t (mul_ne_zero (inv_ne_zero h2) (hw0 i)) ht
    simp only [one_mul, mul_assoc] at this ⊢
    exact this
  have hsq : (quadraticChar k t : ℂ) ^ 2 = 1 := by exact_mod_cast quadraticChar_sq_one ht
  have hpow : (quadraticChar k t : ℂ) ^ Module.finrank k (ι → k) = 1 := by rw [hn2, pow_mul, hsq, one_pow]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hpow, one_mul]

theorem sharp (hF : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 := AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  set S1 : ℂ := ∑ x, ψ (1 * quadForm B x) with hS1
  have hrest : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = -S1 := by
    rw [Finset.sum_congr rfl (fun t ht => by
      rw [gauss_const hF ψ hψ1 hM B hB hdet t (Finset.ne_of_mem_erase ht)])]
    rw [← Finset.sum_mul]
    have hall : ∑ t : k, ψ (-(t * s)) = 0 := by
      have hp := AddChar.IsPrimitive.of_ne_one hψ1
      have := AddChar.sum_mulShift (-s) hp
      simp only [neg_eq_zero, hs, if_false] at this
      simpa [mul_neg] using this
    have hsplit : ψ (-((0 : k) * s)) + ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) =
        ∑ t, ψ (-(t * s)) := Finset.add_sum_erase Finset.univ (fun t : k => ψ (-(t * s))) (Finset.mem_univ (0 : k))
    have h0 : ψ (-((0 : k) * s)) = 1 := by simp
    rw [h0, hall] at hsplit
    have : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) = -1 := by
      linear_combination hsplit
    rw [this]
    ring
  rw [hrest] at hcount
  have hnorm : ‖S1‖ = (Fintype.card k : ℝ) ^ M := by
    have := norm_gauss ψ hψ1 h2 hB hdet hM (one_ne_zero)
    simpa [hS1] using this
  have hreal : (((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ) : ℂ) = -S1 := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| =
      (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, norm_neg, hnorm]
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowM : (Fintype.card k : ℝ) ^ M = (Fintype.card k : ℝ) ^ (M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq, hpowM] at habs
  exact le_of_eq (mul_right_cancel₀ hq.ne' habs)

end PositivityTheory.PfSWUS.HMass.SC

namespace PositivityTheory.PfSWUS.HMass

theorem sharpCount : SharpCount :=
  fun k _ _ hF ι _ _ M hM hM1 B hB hd s hs => by
    classical
    exact SC.sharp hF M hM hM1 B hB hd s hs

end PositivityTheory.PfSWUS.HMass
end
end

namespace PositivityTheory.PfSWUS.HMass

theorem oneVecBinaryMass : OneVecBinaryMass := oneVecBinaryMass_of sharpCount

theorem siegelDensitiesLowA_of_leaves (hE1 : OneVecBinary) (hB : SchwartzDensInf) : SiegelDensitiesLowA :=
  siegelDensitiesLowA_of hE1 oneVecBinaryMass hB

end PositivityTheory.PfSWUS.HMass
