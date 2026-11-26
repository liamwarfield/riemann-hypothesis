module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfUnipotentFibreIntegralsVanish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

theorem iota_int_cofinite {D : D7} (Z : LocDat D) (x : D.host.E) :
    {p : PlF D | (D.s.atP p).ιE x ∉ (Z.M p).L.O}.Finite := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.2 hy0
  have hint' : IsIntegral ℤ ((n : D.host.E) * x) := by
    rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h
    · have e : y • x = (n : D.host.E) * x := by
        rw [zsmul_eq_mul, h, Int.cast_natCast]
      rw [← e]; exact hint
    · have e : y • x = -((n : D.host.E) * x) := by
        rw [zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]
      have := hint.neg
      rw [e, neg_neg] at this
      exact this
  let w : 𝓞 D.host.E := ⟨(n : D.host.E) * x, hint'⟩
  have hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite := by
    have hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn0
    refine (Ideal.finite_factors hne).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, bt_natCast_mem_iff]
    exact hp
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hnd
  apply hp
  obtain ⟨_, w', hw'O, hw'⟩ := bt_nat_unit Z p n hnd
  have hwO := bt_iota_int Z p w
  have e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E) := by
    show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)
    rw [map_mul, map_natCast, ← mul_assoc, hw', one_mul]
  rw [e]
  exact Subring.mul_mem _ hw'O hwO

theorem tri_scaled : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g →
    ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧
      {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  intro D Z f g A hA hg
  refine ⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩
  · intro p
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
    · simp [hA.1 a b hab]
    · show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1
      rw [hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]
    · simp only [scaled]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hg b, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [baseChange_smul₂, smul_smul, smul_smul]
      congr 1
      have h := Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)
      linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h
  · have hD := locDiffC_holds D Z
    refine (Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨a, b, hab⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]
    refine ⟨(a, b), ?_⟩
    intro hι
    apply hab
    rcases lt_or_ge b a with h | h
    · simp [hA.1 a b h]
    · obtain ⟨k, hk, hkb⟩ := bt_frFac_step Z p hD a b h
      have e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) =
          k * (D.s.atP p).ιE (A a b) := by
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]
      rw [e]
      exact Subring.mul_mem _ hk hι

end GlobalTheory.LocOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalingsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitriangular_frame_change_local_scalings : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g → ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧ {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  first | exact @GlobalTheory.LocOver.tri_scaled | exact GlobalTheory.LocOver.tri_scaled | (intros; apply GlobalTheory.LocOver.tri_scaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableOfIntegrableProdOfContinuous
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.ProdFactor

theorem integrable_of_integrable_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℂ}
    (hm : ∀ i, AEStronglyMeasurable (f i) (μ i)) (h0 : ∀ i, ¬ f i =ᵐ[μ i] 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  by_contra hi
  have hn : ¬ Integrable (fun x => ‖f i x‖) (μ i) := fun h' => hi ((integrable_norm_iff (hm i)).1 h')
  have hprod : ∫ x : (∀ j, E j), ∏ j, ‖f j (x j)‖ ∂(Measure.pi μ) = 0 :=
    (integral_fintype_prod_eq_prod (μ := μ) (fun j (y : E j) => ‖f j y‖)).trans
      (Finset.prod_eq_zero (Finset.mem_univ i) (integral_undef hn))
  have hnorm : Integrable (fun x : ∀ j, E j => ∏ j, ‖f j (x j)‖) (Measure.pi μ) := by
    have h' := h.norm
    simp only [norm_prod] at h'
    exact h'
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.prod_nonneg fun j _ => norm_nonneg (f j (x j))) hnorm).1 hprod
  have hbox : Measure.pi μ (Set.univ.pi fun j => {y | f j y ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply]
    exact Finset.prod_ne_zero_iff.2 fun j _ => norm_ne_zero_iff.2 (hx j)
  rw [Measure.pi_pi] at hbox
  refine (Finset.prod_ne_zero_iff.2 fun j _ => ?_) hbox
  intro hz
  exact h0 j (ae_iff.2 (by simpa using hz))

theorem integrable_of_integrable_prod_of_continuous {ι : Type} [Fintype ι] {E : ι → Type}
    [∀ i, TopologicalSpace (E i)] {mE : ∀ i, MeasurableSpace (E i)} [∀ i, OpensMeasurableSpace (E i)]
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsOpenPosMeasure] {f : ∀ i, E i → ℂ}
    (hc : ∀ i, Continuous (f i)) (h0 : ∀ i, ∃ x, f i x ≠ 0)
    (h : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i)) (Measure.pi μ)) (i : ι) :
    Integrable (f i) (μ i) := by

  refine integrable_of_integrable_prod (fun j => (hc j).aestronglyMeasurable) (fun j hj => ?_) h i
  obtain ⟨x, hx⟩ := h0 j
  exact hx (congrFun (((hc j).ae_eq_iff_eq (μ j) continuous_zero).1 hj) x)

section Local

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem continuous_coefOn (hU : IsURepOn (UJset ε) σ) (v w : H) : Continuous (coefOn (ε := ε) σ v w) := by
  obtain ⟨-, -, hcont⟩ := hU
  have hσ : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
    (hcont v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => g.2
  exact continuous_const.inner hσ

theorem coefOn_one (hU : IsURepOn (UJset ε) σ) {w : H} (hw : ‖w‖ = 1) : coefOn (ε := ε) σ w w 1 = 1 := by
  obtain ⟨⟨h1, -⟩, -, -⟩ := hU
  have hu : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  show ⟪w, σ (umat (1 : Formalism.REAL.UJ ε)) w⟫_ℂ = 1
  rw [hu, h1, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hw]
  norm_num

theorem fdegOf_pos (hU : IsURepOn (UJset ε) σ) (hsq : IsSqIntOn ε σ) {w : H} (hw : ‖w‖ = 1) :
    0 < fdegOf (Formalism.REAL.muG ε) σ w := by

  show 0 < ‖w‖ ^ 4 / ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)
  rw [hw, one_pow]
  refine div_pos one_pos ?_
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => ‖coefOn (ε := ε) σ w w g‖ ^ 2 :=
    (continuous_coefOn hU w w).norm.pow 2
  have hint : Integrable (fun g => ‖coefOn (ε := ε) σ w w g‖ ^ 2) (Formalism.REAL.muG ε) :=
    (hsq w w).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hint]
  refine hcont.isOpen_support.measure_pos _ ⟨1, ?_⟩
  simp [Function.mem_support, coefOn_one hU hw]

end Local

theorem integrable_factor {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) (Measure.pi fun v => Formalism.REAL.muG (ε v)))
    (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by

  exact integrable_of_integrable_prod_of_continuous (E := fun v => Formalism.REAL.UJ (ε v))
    (μ := fun v => Formalism.REAL.muG (ε v))
    (f := fun v g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g))
    (fun v => continuous_const.mul (continuous_coefOn (hU v) (w v) (w v)).star)
    (fun v => ⟨1, by simp [coefOn_one (hU v) (hw v), hd v]⟩) h v

theorem integrable_factor' {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin n) (Fin n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (d : ι → ℝ)
    (hU : ∀ v, IsURepOn (UJset (ε v)) (σ v)) (hw : ∀ v, ‖w v‖ = 1) (hd : ∀ v, d v ≠ 0)
    (h : Integrable (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v)))
      (Measure.pi fun v => Formalism.REAL.muG (ε v))) (v : ι) :
    Integrable (fun g => (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) g)) (Formalism.REAL.muG (ε v)) := by
  have hfun : (fun g : ∀ v, Formalism.REAL.UJ (ε v) =>
      ((∏ v, d v : ℝ) : ℂ) * star (∏ v, coefOn (ε := ε v) (σ v) (w v) (w v) (g v))) =
      fun g => ∏ v, (d v : ℂ) * star (coefOn (ε := ε v) (σ v) (w v) (w v) (g v)) := by
    funext g
    rw [Complex.ofReal_prod, star_prod, Finset.prod_mul_distrib]
  rw [hfun] at h
  exact integrable_factor ε σ w d hU hw hd h v

end GlobalTheory.ProdFactor
end
end

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.ProdFactor

theorem integrable_phLoc_of_integrable_ph : ∀ (D : D7) (X : HidaSetting D), Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hX v
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hd : ∀ v, X.dv v ≠ 0 := fun v =>
    (fdegOf_pos (hU v) (X.ds v).2.2.2.2.1 (hw v)).ne'

  exact integrable_factor' X.B.I.ε X.B.σ X.B.w X.dv hU hw hd hX v

end GlobalTheory.ProdFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CapelliOfHC

open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

private theorem conj_blockW_exp_eq_exp_unitB {g : Mx k r} (hg : IsFrameW k r z g) (Z : Matrix (Fin k) (Fin k) ℂ) (t : ℝ) :
    g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) •
      ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b) := by
  have hunit : IsUnit g := by
    have hgg := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq ▸ hg.1)).2
    exact ⟨⟨g, g⁻¹, hgg.1, hgg.2⟩, rfl⟩
  have hs : ∀ a b : Fin k, Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := fun a b => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hu : ∀ a b : Fin k, Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b =
      g * incl k r * Matrix.single a b (1 : ℂ) * ((incl k r)ᴴ * g⁻¹) := fun a b => by
    rw [unitB_eq, co_eq hg.1]
  rw [blockW_eq, ← exp_corner (incl k r) (incl k r)ᴴ incl_incl, ← Matrix.exp_conj g _ hunit]
  congr 1
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [hu, hs, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, smul_smul]

theorem exists_eigen {u₀ : Fin k → ℝ} (hR : Qr.IsRepW k r z π) (h₀ : IsHCTypeW k r z u₀ π) :
    ∃ B : Fin k → (Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] B ∧ ∃ v : W, v ≠ 0 ∧
      ∀ Y : ℂ, Formalism.REAL.qdet (Qr.EB π B) (Y + ((k : ℂ) - 1) / 2) v = (∏ s, (Y + (u₀ s : ℂ))) • v := by
  obtain ⟨g, hg, hU⟩ := h₀
  have hB : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a)) := isFrameOf hg
  refine ⟨fun a => g *ᵥ bvec (bl k r a), hB, ?_⟩
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear W k r k z π _ hR hB).1
  refine qdet_eigen hU _ hgl ?_
  intro Z hZ v
  set X : Mx k r := ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b with hXdef
  have hadj : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
    simp only [hXdef, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Formalism.FourierDecayAlt.P.QrCap.unitB_adj]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrFun (congrFun hZ a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
    rw [h1, neg_smul]
  have hX1 : Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) X = X := by
    rw [Formalism.QuantumDeterminants.hpart1, hadj, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
    norm_num
  have hX2 : Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) X = 0 := by
    rw [Formalism.QuantumDeterminants.hpart2, hadj, add_neg_cancel, smul_zero]
  have hsum := Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum Formalism.FourierDecayAlt.P.elementary_lie_elements hR (Finset.univ : Finset (Fin k × Fin k))
    (fun p => Z p.1 p.2) (fun p => Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) p.1 p.2)
    (fun p => Formalism.FourierDecayAlt.P.QrD.frame_lie hB p.1 p.2) 0 (Formalism.FourierDecayAlt.P.SkewHermitianParts.inGl_zero z)
  rw [← Finset.univ_product_univ, Finset.sum_product] at hsum
  have hXlie : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X := by
    have h := hsum.1.1
    rwa [hX1] at h
  have hec : ∑ a, ∑ b, Z a b • Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) a b v = Formalism.FourierDecayAlt.P.QrD.dOp π X v := by
    have h := hsum.2
    have h' : Formalism.FourierDecayAlt.P.QrD.ecOp π X = Formalism.FourierDecayAlt.P.QrD.dOp π X := by
      rw [Formalism.FourierDecayAlt.P.QrD.ecOp, hX1, hX2, Formalism.FourierDecayAlt.P.SkewHermitianParts.dOp_zero, smul_zero, add_zero]
    rw [h'] at h
    rw [h]
    simp only [Finset.sum_product, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rfl
  have hexp : ∀ t : ℝ, g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) • X) :=
    fun t => conj_blockW_exp_eq_exp_unitB hg Z t
  have hd := Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hR.1 hR.2 hXlie
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (Formalism.FourierDecayAlt.P.QrD.dOp π X v) 0 := by
    have h2 := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using h2
  rw [hec]
  convert hd' using 1
  funext t
  rw [hexp t]

theorem exists_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u₀ : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u₀ π → ∃ u : ℕ → ℝ, Q.IsType k r z π u := by
  intro k r Wp _ _ _ z π u₀ hz hT h₀
  obtain ⟨h1, hmul, hnorm, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT h₀
  have hR : Qr.IsRepW k r z π := ⟨⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont⟩
  have ⟨g, hg, hU⟩ := h₀
  have hirr : ∀ S : Submodule ℂ Wp, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    refine hU.2.2.2.2.2.1 S le_top ?_
    intro h hh v hv
    have hh' : hᴴ * h = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hS _ (Formalism.FourierDecayAlt.P.QrCap.emb_uw hg.1 hg.2.1 _ hg.2.2 hh') v hv
  obtain ⟨B, hB, v0, hv0, heig⟩ := exists_eigen hR h₀
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π B hR hB).1
  have key : ∀ (w : ℂ) (v : Wp), Formalism.REAL.qdet (Qr.EB π B) w v =
      (∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ))) • v := by
    intro w
    set c : ℂ := ∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ)) with hc
    set S : Submodule ℂ Wp := LinearMap.ker (Formalism.REAL.qdet (Qr.EB π B) w - c • (1 : Module.End ℂ Wp)) with hSdef
    have hmem : ∀ v, v ∈ S ↔ Formalism.REAL.qdet (Qr.EB π B) w v = c • v := fun v => by
      rw [hSdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hv0S : v0 ∈ S := by
      rw [hmem]
      have := heig (w - ((k : ℂ) - 1) / 2)
      rwa [sub_add_cancel] at this
    have hstab : Qr.Stab (Qr.EB π B) S := by
      intro a b v hv
      rw [hmem] at hv ⊢
      have hcomm := Formalism.REAL.qDetCentral (Module.End ℂ Wp) k (Qr.EB π B) hgl w a b
      have := congrArg (fun T : Module.End ℂ Wp => T v) hcomm
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]
    have hUW := Formalism.FourierDecayAlt.P.lie_stabilizer Wp k r z π B hz hT hR hB S hstab
    rcases hirr S hUW with hbot | htop
    · exact absurd (by rw [hbot] at hv0S; exact (Submodule.mem_bot ℂ).1 hv0S) hv0
    · intro v
      exact (hmem v).1 (htop ▸ Submodule.mem_top)
  refine ⟨fun i => if h : i - 1 < k then u₀ ⟨i - 1, h⟩ else 0, hU.1, ⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont,
    hnorm, hirr, ?_⟩
  intro Bs hBs w v
  rw [(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π Bs hR hBs).2,
    GlobalTheory.capelli_det_frame_indep Wp k r z π Bs B hz hT hR hBs hB, key]
  congr 1
  refine Finset.prod_bij' (fun s _ => s.val + 1) (fun i hi => ⟨i - 1, by simp only [Finset.mem_Icc] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_Icc]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro s _
    exact Fin.ext (by simp)
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show i - 1 + 1 = i
    omega
  · intro s _
    simp only [Nat.add_sub_cancel, s.isLt, dite_true, Fin.eta]
    ring

end GlobalTheory.CapelliOfHC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKType
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem range_cuspidal_of_lowKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  intro B d h hD hK hh hL hB hF T hT y
  have hv := GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish B d h hD hK hL hh
  exact GlobalTheory.T.cuspidal_of_unipotent_fibre_integrals_vanish B d h hD hv hL hB hF T hT y

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionRangeCuspidalOfLowestKTypeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_range_cuspidal_of_lowestKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  first | exact @GlobalTheory.Dec.range_cuspidal_of_lowKType | exact GlobalTheory.Dec.range_cuspidal_of_lowKType | (intros; apply GlobalTheory.Dec.range_cuspidal_of_lowKType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

end GlobalTheory.Per.FJConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
noncomputable section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultTranslate

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem isCuspFun_rTr {φ : GA D V → ℂ} (h : IsCuspFun V φ) (x : GA D V) : IsCuspFun V (rTr V x φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * x)

theorem isMultMap_rTr {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J' χ' (postOn M (GlobalTheory.FinTranslate.rTrL V x) T) := by
  constructor
  · intro v
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V x hx _ (h.aut v)
  · intro v
    exact isCuspFun_rTr (h.cusp v) x
  · intro v k hk g
    change T v (g * k * x) = χ' k * T v (g * x)
    rw [(hJ k hk).2, ← h.lev v _ (hJ k hk).1]
    group
  · intro τ g hg v w hw
    funext y
    change T (Function.update v τ w) (y * x) = T v (y * atTau θ V τ g * x)
    rw [h.equiv τ g hg v w hw, mul_assoc,
      ← GlobalTheory.FinTranslate.comm_fin_real V hx (GlobalTheory.FinTranslate.atTau_mem θ V τ g), ← mul_assoc]
    rfl
  · intro τ v y
    exact h.cont τ v (y * x)

theorem postOn_mem_goodPart {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {L L' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}
    (hL : ∀ f, L' (rTr V x f) = rTr V x (L f)) {T : MMap M} (h : T ∈ goodPart θ M J χ L) :
    postOn M (GlobalTheory.FinTranslate.rTrL V x) T ∈ goodPart θ M J' χ' L' := by
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at h ⊢
  refine ⟨isMultMap_rTr hx hJ h.1, fun v => ?_⟩
  change L' (rTr V x (T v)) = rTr V x (T v)
  rw [hL, h.2]

end GlobalTheory.MultTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAll
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAll
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped nonZeroDivisors

namespace GlobalTheory.FrameFactorUnit

open Formalism.MainNotions.S.LocNG IsDedekindDomain
open scoped nonZeroDivisors

variable {D : D7}

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem one_mem_inv_pow (k : ℕ) : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ k := by
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ (ddS D)⁻¹ := by
    simpa using FractionalIdeal.inv_anti_mono ddS_ne_zero hle
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simpa using FractionalIdeal.mul_mem_mul ih (h1 (FractionalIdeal.one_mem_one _))

private theorem exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal {E : Type} [Field E] [NumberField E]
    (J : FractionalIdeal (𝓞 E)⁰ E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ y ∈ J, ∃ z : 𝓞 E, (N : E) * y = (z : E) := by
  obtain ⟨b, hb, hint⟩ := J.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · intro y hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨z, hz⟩ := hint y hy
    refine ⟨c * z, ?_⟩
    have hz' : (z : E) = (b : E) * y := by
      rw [Algebra.smul_def] at hz
      exact hz
    have hN : ((Ideal.absNorm (Ideal.span {b}) : 𝓞 E) : E) = (Ideal.absNorm (Ideal.span {b}) : E) := by
      push_cast
      rfl
    calc (Ideal.absNorm (Ideal.span {b}) : E) * y
        = ((c * b : 𝓞 E) : E) * y := by rw [hc, hN]
      _ = (c : E) * ((b : E) * y) := by push_cast; ring
      _ = (c : E) * (z : E) := by rw [hz']
      _ = ((c * z : 𝓞 E) : E) := by push_cast; ring

private theorem ιE_ringOfIntegers_mem_O (D : D7) (p : PlF D) (z : 𝓞 D.host.E) :
    (D.s.atP p).ιE (z : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h : IsIntegral ℤ ((D.s.atP p).ιE (z : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe z).map ((D.s.atP p).ιE.toIntAlgHom)
  exact h.tower_top

private theorem finite_setOf_not_isUnit_natCast_atP (D : D7) (N : ℕ) (hN : N ≠ 0) :
    {p : PlF D | ¬ ∃ w ∈ (D.s.atP p).O, (D.s.atP p).ιE (N : D.host.E) * w = 1}.Finite := by
  have hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation D.host.F (N : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (K := D.host.F) (v := p)).mpr hmem
    simpa using this
  have hle : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val]
    simp [map_inv₀, hv]
  rw [map_one] at hle
  have hint : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp) := by
    rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff]
    exact hle
  have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((N : D.host.F)⁻¹)), ?_, ?_⟩
  · rw [(D.s.atP p).O_def]
    exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)) (A := (D.s.atP p).Ep) (x := ⟨_, hint⟩)
  · rw [← (D.s.atP p).compat, ← map_mul, map_inv₀, map_natCast, mul_inv_cancel₀ hNE, map_one]

end GlobalTheory.FrameFactorUnit


open GlobalTheory.FrameFactorUnit in
theorem GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  intro D Z a
  have hL := Formalism.L2.SG.Pf.locDiffC_holds D Z
  unfold Formalism.L2.SG.Pf.LocDiffC at hL
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal (ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))))
  refine (finite_setOf_not_isUnit_natCast_atP D N hN0).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hgood
  apply hp
  obtain ⟨w, hwO, hw1⟩ := hgood
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) ∈ (D.s.atP p).O := by
    have := Formalism.L2.SG.Pf.LocFacts.lf_mem_pow p Formalism.L2.SG.Pf.dualLoc_holds Z (D.R.rS - a.val) 1
      (one_mem_inv_pow _)
    simpa using this
  have hunit : IsUnit (Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val)) :=
    (Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow _
  have hinv : frFac Z.δ p a * Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) = 1 := by
    unfold frFac
    exact Ring.inverse_mul_cancel _ hunit
  have hmem : frFac Z.δ p a ∈ (Z.M p).L.O := by
    have hs := Submodule.mem_span_singleton_self (R := (Z.M p).L.O) (frFac Z.δ p a)
    rw [← hL p a] at hs
    revert hs
    generalize frFac Z.δ p a = f
    intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz⟩ := hN y hy
      rw [hO]
      have hy' : (D.s.atP p).ιE y = w * (D.s.atP p).ιE (z : D.host.E) := by
        rw [← hz, map_mul, ← mul_assoc, mul_comm w, hw1, one_mul]
      rw [hy']
      exact mul_mem hwO (ιE_ringOfIntegers_mem_O D p z)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [Subring.smul_def]
      exact mul_mem r.2 hx
  show frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ y ∈ (Z.M p).L.O, frFac Z.δ p a * y = 1
  exact ⟨hmem, _, hO ▸ hc, hinv⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAllStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_factors_local_units_almost_all : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  first | exact @GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | exact GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | (intros; apply GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite <;> assumption)
end
end
