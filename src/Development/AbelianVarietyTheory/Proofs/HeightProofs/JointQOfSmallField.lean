module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩


end GlobalTheory.FieldSize
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open scoped IntermediateField

theorem scale_le_rank {D : D7} {L : SizeData₂ D} (S : SizesAt L) : L.sc.x ≤ (D.R.r : ℝ) := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
  exact (h1.trans S.2.2.1.1).trans (Pm.k_le_r D)

theorem hostSz_of_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (_Tp : ParamsT D L Pm), SizesAt L →
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x →
    HostSz D.host L.sc.L ∧ (Sz (FO D) (poR D.R L.sc.L) (poR D.R L.sc.L) → FieldSmall D L) := by
  intro D L P _ S hg hx
  have hL := Pm.one_le_L L
  have h6 := Pm.six_le_r D
  have hf := Pm.two_le_f D
  refine ⟨⟨?_, ?_, ?_, hg, P.pde_log, ?_⟩, fun h => h.2⟩
  · have h : ((62 : ℕ) : ℝ) ≤ D.R.r := le_trans (by norm_num) (hx.trans (scale_le_rank S))
    exact_mod_cast h
  · have h1 := Pm.log_r_le P
    have h2 : Real.log 2 ≤ Real.log (D.R.r : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  · linarith [Pm.log_f_le P]
  · have h : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * L.sc.L := logdE_le_two_f_L P
    rw [div_le_iff₀ (by linarith)]
    nlinarith

end GlobalTheory.FieldSize
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem exists_hostK : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  intro R H
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hb : (H.φ₀ H.sqrtMinusD) ^ 2 = -(H.d : ℂ) := by
    have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
    rw [← map_pow, h, map_neg, map_natCast]
  let σ : H.K →ₐ[ℚ] ℂ := H.φ₀.toRatAlgHom.comp H.K.val
  let e : H.K ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have hNF : NumberField σ.fieldRange := NumberField.mk
  have h2 : Module.finrank ℚ σ.fieldRange = 2 :=
    e.toLinearEquiv.finrank_eq.symm.trans
      (Formalism.FrobeniusOrbits.SplitK.finrank_K hd.pos (H.sqd_sq))
  let r : σ.fieldRange := ⟨H.φ₀ H.sqrtMinusD, ⟨Formalism.FrobeniusOrbits.SplitK.bK H.sqrtMinusD, rfl⟩⟩
  have hr : r ^ 2 = -(H.d : σ.fieldRange) := by
    apply Subtype.ext
    simpa [r] using hb
  have h4 : H.d % 4 = 3 := by omega
  have hD : discr σ.fieldRange = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 hd.squarefree h4 hr
  have hTC : IsTotallyComplex σ.fieldRange := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    let ψ := InfinitePlace.embedding_of_isReal hv
    have h1 : ψ r ^ 2 = -(H.d : ℝ) := by rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg (ψ r)]
  obtain ⟨x, -, hx, -, hgen, -⟩ := ringOfIntegers_sqrt_neg_three_mod_four H.d hd.squarefree h4 σ.fieldRange h2 r hr
  have hx' : ((x : σ.fieldRange) : ℂ) = (1 + H.φ₀ H.sqrtMinusD) / 2 := by
    have := congrArg (fun y : σ.fieldRange => (y : ℂ)) hx
    simp only [r] at this
    push_cast at this
    have e2 : ((2 : σ.fieldRange) : ℂ) = 2 := rfl
    rw [e2] at this
    linear_combination this / 2
  have hc : ∀ m n : ℤ, ((((m : 𝓞 σ.fieldRange) + n * x : 𝓞 σ.fieldRange) : σ.fieldRange) : ℂ) =
      m + n * ((1 + H.φ₀ H.sqrtMinusD) / 2) := fun m n => by
    rw [← hx']
    simp
  refine ⟨σ.fieldRange, hNF, hTC, h2, hD, by omega, ?_, fun z => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : H.E), rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, hc s.1 s.2⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    exact ⟨(m, n), hc m n⟩
  · rw [H.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExp
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem FamGrowth.bdd_of_isCompact {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hG : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {K : Set (Mx n)} (hK : IsCompact K) (hKU : K ⊆ UJset ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖F w y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hG w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_hs.continuousOn
  refine ⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩
  have h1 : hs y ≤ max M 0 := (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have h0 : 0 ≤ hs y := hs_nonneg y
  calc ‖F w y‖ ≤ C * (1 + hs y) ^ N := hC y (hKU hy)
    _ ≤ |C| * (1 + hs y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + max M 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg C)

noncomputable def expSweep (K : Set (Mx n)) (X : Mx n) : Set (Mx n) :=
  (fun p : Mx n × ℝ => p.1 * NormedSpace.exp (p.2 • X)) '' (K ×ˢ Set.Icc (-1 : ℝ) 1)

theorem isCompact_expSweep {K : Set (Mx n)} (hK : IsCompact K) (X : Mx n) : IsCompact (expSweep K X) :=
  (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))
theorem expSweep_sub {K : Set (Mx n)} (hKU : K ⊆ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    expSweep K X ⊆ UJset ε := by
  rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
  exact mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)

theorem mem_expSweep {K : Set (Mx n)} {z : Mx n} (hz : z ∈ K) (X : Mx n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    z * NormedSpace.exp (s • X) ∈ expSweep K X := ⟨(z, s), ⟨hz, hs⟩, rfl⟩

theorem exp_zero_smul_mx (X : Mx n) : NormedSpace.exp ((0 : ℝ) • X) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

theorem IsDerFam.norm_sub_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z‖ ≤ B * |t| := by
  have h := norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X)))
    (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)
  simpa only [exp_zero_smul_mx, Matrix.mul_one] using h

theorem IsDerFam.norm_taylor_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z‖ ≤ B * t ^ 2 := by
  have hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hw Y hY]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t| := by
    intro s hs
    have hs1 : |s| ≤ |t| := abs_le.2 hs
    exact (hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)
  have hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z)
      (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s := by
    intro s
    have := (hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))
    simpa only [id, one_smul] using this
  have h := norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩
  simp only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h
  have e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z =
      F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z := by abel
  rw [e]
  calc _ ≤ B * |t| * |t| := h
    _ = B * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem lie_cons {Y : Mx n} {w : List (Mx n)} (hY : Y ∈ lieSet ε) (hw : ∀ Z ∈ w, Z ∈ lieSet ε) :
    ∀ Z ∈ Y :: w, Z ∈ lieSet ε := by
  intro Z hZ
  rcases List.mem_cons.1 hZ with rfl | hZ
  exacts [hY, hw Z hZ]

theorem IsDerFam.taylor_prod {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) (hG : FamGrowth ε N F)
    {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : ∀ (d : ℕ) (b : Fin d → Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ K : Set (Mx n), IsCompact K → K ⊆ UJset ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ t : Fin d → ℝ, ‖t‖ ≤ 1 →
      ‖F l (z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod) - F l z - ∑ i, t i • F (b i :: l) z‖ ≤
        C * ‖t‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro b hb K hK hKU
    refine ⟨0, le_rfl, fun z _ t _ => ?_⟩
    simp
  | succ d ih =>
    intro b hb K hK hKU
    have hX := hb 0
    have hK' := isCompact_expSweep hK (b 0)
    have hK'U := expSweep_sub hKU hX
    obtain ⟨C', hC'0, hC'⟩ := ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U
    obtain ⟨B0, hB00, hB0⟩ := hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U
    have hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B :=
      fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U
    choose B hBnn hB using hBi
    have hBs : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBnn i
    refine ⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩
    have hzU := hKU hz
    have hti : ∀ i, |t i| ≤ ‖t‖ := fun i => by simpa using norm_le_pi_norm t i
    have ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ((hti 0).trans ht)
    have ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ
    have hz1 := mem_expSweep hz (b 0) ht0
    have hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod =
        z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]
    rw [hprod, Fin.sum_univ_succ]
    set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def
    have h1 := hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)
    have h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hd := hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU
        (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
      calc |t i.succ| * ‖F (b i.succ :: l) z1 - F (b i.succ :: l) z‖ ≤ ‖t‖ * (B i * ‖t‖) :=
            mul_le_mul (hti _) (hd.trans (mul_le_mul_of_nonneg_left (hti 0) (hBnn i))) (norm_nonneg _)
              (norm_nonneg _)
        _ = B i * ‖t‖ ^ 2 := by ring
    have h3 := hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
    have h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hB00
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2
    have h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0
    have e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z -
        (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) =
        (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 -
          ∑ i : Fin d, t i.succ • F (b i.succ :: l) z1) +
        ∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z) +
        (F l z1 - F l z - t 0 • F (b 0 :: l) z) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    have : (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2 := by ring
    rw [this]
    exact add_le_add_three (h1.trans h1') h2 (h3.trans h3')

theorem hasFDerivAt_derFam_prodExp : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  intro n ε N F hF hG l hl d b hb g hg
  obtain ⟨C, -, hC⟩ := hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1 := by
    simp [List.prod_ofFn]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  simp only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]
  exact hC g rfl h hh

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExpStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  first | exact @GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | exact GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | (intros; apply GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem exists_hom_of_ann {R V M : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R V] {d : ℕ} (w : Fin d → V) (m₀ : M) (h : ∀ α : R, α • w = 0 → α • m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[R] M), ∑ a, T a (w a) = m₀ ∧ ∀ a v, ∃ α : R, T a v = α • m₀ := by
  classical
  let f : R →ₗ[R] (Fin d → V) := LinearMap.toSpanSingleton R _ w
  let g : R →ₗ[R] M := LinearMap.toSpanSingleton R _ m₀
  have hk : LinearMap.ker f ≤ LinearMap.ker g := fun α hα => h α hα
  let φ : LinearMap.range f →ₗ[R] M := (LinearMap.ker f).liftQ g hk ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ α : R, φ ⟨f α, α, rfl⟩ = α • m₀ := by
    intro α
    have : f.quotKerEquivRange.symm ⟨f α, α, rfl⟩ = Submodule.Quotient.mk α := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f).liftQ g hk (f.quotKerEquivRange.symm ⟨f α, α, rfl⟩) = _
    rw [this]; rfl
  obtain ⟨P, hP⟩ := IsSemisimpleModule.extension_property (LinearMap.range f).subtype
    (LinearMap.range f).injective_subtype LinearMap.id
  refine ⟨fun a => φ ∘ₗ P ∘ₗ LinearMap.single R (fun _ => V) a, ?_, fun a v => ?_⟩
  · have e : ∑ a, Pi.single a (w a) = (LinearMap.range f).subtype ⟨f 1, 1, rfl⟩ := by
      rw [Finset.univ_sum_single]
      exact (one_smul R w).symm
    have e2 := LinearMap.congr_fun hP ⟨f 1, 1, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_single]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum, e]
    rw [LinearMap.comp_apply] at e2
    rw [e2, LinearMap.id_apply, hφ, one_smul]
  · obtain ⟨α, hα⟩ := (P (Pi.single a v)).2
    refine ⟨α, ?_⟩
    rw [← hφ]
    exact congrArg φ (Subtype.ext hα.symm)

theorem exists_words {L : Type} (α : FreeAlgebra ℂ L) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), α = ∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod := by
  have h1 : α ∈ (Algebra.adjoin ℂ (Set.range (FreeAlgebra.ι ℂ : L → _))).toSubmodule := by
    rw [FreeAlgebra.adjoin_range_ι]; trivial
  rw [Algebra.adjoin_eq_span] at h1
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h1
  have : ∀ x ∈ Submonoid.closure (Set.range (FreeAlgebra.ι ℂ : L → _)),
      ∃ u : List L, (u.map (FreeAlgebra.ι ℂ)).prod = x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨y, rfl⟩ := hx; exact ⟨[y], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u ++ v, by simp⟩
  choose u hu using fun i => this _ (g i).2
  exact ⟨m, c, u, by rw [← e]; simp only [hu]⟩

theorem lift_words {L M : Type} [AddCommGroup M] [Module ℂ M] (τ : L → Module.End ℂ M) {m : ℕ} (c : Fin m → ℂ)
    (u : Fin m → List L) (x : M) :
    FreeAlgebra.lift ℂ τ (∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod) x =
      ∑ i, c i • (u i).foldr (fun y => τ y) x := by
  have : ∀ l : List L, FreeAlgebra.lift ℂ τ (l.map (FreeAlgebra.ι ℂ)).prod x = l.foldr (fun y => τ y) x := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]; simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, this]

theorem exists_intertwiner {L V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : L → Module.End ℂ V) (hρ : ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤)
    (τ : L → Module.End ℂ M) {d : ℕ} (w : Fin d → V) (m₀ : M)
    (h : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), (∀ a, ∑ i, c i • (u i).foldr (fun y => ρ y) (w a) = 0) →
      ∑ i, c i • (u i).foldr (fun y => τ y) m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[ℂ] M), (∀ a v x, T a (ρ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), T a v = ∑ i, c i • (u i).foldr (fun y => τ y) m₀ := by
  letI : Module (FreeAlgebra ℂ L) V := Module.compHom V (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module (FreeAlgebra ℂ L) M := Module.compHom M (FreeAlgebra.lift ℂ τ).toRingHom
  have eV : ∀ (α : FreeAlgebra ℂ L) (v : V), α • v = FreeAlgebra.lift ℂ ρ α v := fun _ _ => rfl
  have eM : ∀ (α : FreeAlgebra ℂ L) (v : M), α • v = FreeAlgebra.lift ℂ τ α v := fun _ _ => rfl
  have cV : ∀ (c : ℂ) (v : V), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eV, AlgHom.commutes]; rfl
  have cM : ∀ (c : ℂ) (v : M), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eM, AlgHom.commutes]; rfl
  have hs : ∀ N : Submodule (FreeAlgebra ℂ L) V, N = ⊥ ∨ N = ⊤ := by
    intro N
    let W : Submodule ℂ V :=
      { carrier := N
        add_mem' := N.add_mem
        zero_mem' := N.zero_mem
        smul_mem' := fun c v hv => by rw [← cV]; exact N.smul_mem _ hv }
    by_cases h0 : W = ⊥
    · left
      rw [eq_bot_iff] at h0 ⊢
      exact fun v hv => h0 (show v ∈ W from hv)
    · right
      have := hρ W (fun x v hv => by
        have := N.smul_mem (FreeAlgebra.ι ℂ x) hv
        rwa [eV, FreeAlgebra.lift_ι_apply] at this) h0
      rw [eq_top_iff] at this ⊢
      exact fun v _ => (show v ∈ W from this trivial)
  haveI : IsSemisimpleModule (FreeAlgebra ℂ L) V := by
    refine (isSemisimpleModule_iff _ _).2 ⟨fun N => ?_⟩
    rcases hs N with rfl | rfl
    exacts [⟨⊤, isCompl_bot_top⟩, ⟨⊥, isCompl_top_bot⟩]
  obtain ⟨T, h1, h2⟩ := exists_hom_of_ann (R := FreeAlgebra ℂ L) w m₀ (by
    intro α hα
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    rw [eM, lift_words]
    refine h m c u fun a => ?_
    rw [← lift_words, ← eV]
    exact congrFun hα a)
  refine ⟨fun a =>
    { toFun := T a
      map_add' := (T a).map_add
      map_smul' := fun c v => by rw [← cV, map_smul, cM]; rfl }, fun a v x => ?_, h1, fun a v => ?_⟩
  · have := (T a).map_smul (FreeAlgebra.ι ℂ x) v
    rwa [eV, eM, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at this
  · obtain ⟨α, hα⟩ := h2 a v
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    exact ⟨m, c, u, hα.trans (by rw [eM, lift_words])⟩

theorem exists_maps_of_relations : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  intro hHC n ε H _ _ _ σ hσ d w hw M _ _ τ m₀ h
  have hmem : ∀ (x : Ltr ε) v, IsKFin ε σ v → IsKFin ε σ (ltrV σ x v) := by
    rintro (X | k) v hv
    exacts [isKFin_dRep n ε H σ hσ v hv X.1 X.2, isKFin_translate hv k.2]
  let ρ : Ltr ε → Module.End ℂ (kfin ε σ) := fun x =>
    { toFun := fun v => ⟨ltrV σ x v.1, hmem x v.1 v.2⟩
      map_add' := fun a b => Subtype.ext (by
        rcases x with X | k
        · exact Dw_add hσ.1 (l := [X.1]) (by simpa using X.2) (hσ.2.2.1 _ a.2) (hσ.2.2.1 _ b.2)
        · exact map_add (σ k.1) _ _)
      map_smul' := fun c a => Subtype.ext (by
        rcases x with X | k
        · exact Dw_smul hσ.1 (l := [X.1]) (by simpa using X.2) c (hσ.2.2.1 _ a.2)
        · exact map_smul (σ k.1) _ _) }
  have hword : ∀ (u : List (Ltr ε)) (v : kfin ε σ), (u.foldr (fun y => ρ y) v : kfin ε σ).1 = wordV σ u v.1 := by
    intro u v
    induction u with
    | nil => rfl
    | cons x u ih =>
      show ltrV σ x (u.foldr (fun y => ρ y) v : kfin ε σ).1 = ltrV σ x (wordV σ u v.1)
      rw [ih]
  have hρ : ∀ W : Submodule ℂ (kfin ε σ), (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW h0
    have k1 : ∀ v ∈ W.map (kfin ε σ).subtype, IsKFin ε σ v := by
      rintro _ ⟨v, -, rfl⟩; exact v.2
    have k2 : ∀ (x : Ltr ε), ∀ v ∈ W.map (kfin ε σ).subtype, ltrV σ x v ∈ W.map (kfin ε σ).subtype := by
      rintro x _ ⟨v, hv, rfl⟩; exact ⟨ρ x v, hW x v hv, rfl⟩
    have k3 : ∀ k ∈ Kset ε, ∀ v ∈ W.map (kfin ε σ).subtype, σ k v ∈ W.map (kfin ε σ).subtype :=
      fun k hk => k2 (Sum.inr ⟨k, hk⟩)
    have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hσ.1 hσ.2.1 k1 (fun X hX => k2 (Sum.inl ⟨X, hX⟩)) k3
      (fun e => h0 (Submodule.map_injective_of_injective (kfin ε σ).injective_subtype
        (e.trans (Submodule.map_bot _).symm)))
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, e⟩ := GlobalTheory.HCModIrred.mem_of_dense hσ hd k1 k3 v.2
    exact (Subtype.ext e : y = v) ▸ hy
  obtain ⟨T, h1, h2, h3⟩ := exists_intertwiner ρ hρ τ (fun a => (⟨w a, hw a⟩ : kfin ε σ)) m₀ (by
    intro m c u hu
    refine h m c u fun a => ?_
    have := congrArg Subtype.val (hu a)
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, hword, Submodule.coe_zero] using this)
  choose T' hT' using fun a => LinearMap.exists_extend (T a)
  have e : ∀ a v (hv : IsKFin ε σ v), T' a v = T a ⟨v, hv⟩ := fun a v hv => LinearMap.congr_fun (hT' a) ⟨v, hv⟩
  refine ⟨T', fun a v hv x => ?_, ?_, fun a v hv => ?_⟩
  · rw [e a _ (hmem x v hv), e a v hv]
    exact h1 a ⟨v, hv⟩ x
  · rw [← h2]
    exact Finset.sum_congr rfl fun a _ => e a _ (hw a)
  · rw [e a v hv]
    exact h3 a _

end GlobalTheory.TypeSum.CoefClos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maps_of_relations_alt : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  first | exact @GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | exact GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | (intros; apply GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations <;> assumption)
end
end
