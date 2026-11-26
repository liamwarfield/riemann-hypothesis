module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.PhiMul
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.GapNorm
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.FdAllOf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DiscreteSeriesSU.GapInv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCover
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HcFormalDegreeOfDiscreteSeriesFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CoefPow
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.ExplicitFunctionSquareIntegrable

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.KTypeRanges.KmapZero
noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem sigLam_coe' (hS : HlamStable) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hP : IsPsiFor ε lam T Ψ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x : Hlam ε Ψ T.w) :
    ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
  have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hS n ε lam T Ψ hP g hg x x.2
  show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))

theorem isKTypeOf_range {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (φ : T.V →ₗ[ℂ] Hlam ε Ψ T.w) (hφ : Function.Injective φ)
    (hint : ∀ (k : KG ε) (v : T.V), φ (T.op k v) = sigLam ε Ψ T.w (toMK k) (φ v)) :
    Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) (Formalism.QuantumDeterminants.lowK ε lam) ((⊤ : Submodule ℂ T.V).map φ) := by
  obtain ⟨σ, hσk, -, hKT⟩ := HW.KType.exists_rep T
  have hint' : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (σ g x) = sigLam ε Ψ T.w g (φ x) := by
    intro g hg x
    have e : g = toMK (pdA_kg g hg) := (pdA_toMK_kg g hg).symm
    rw [e, hσk, hint]
  exact (isKTypeOf_map_iff φ hφ hint' (Formalism.QuantumDeterminants.lowK ε lam) ⊤).1 hKT

theorem kmapZero_of (hS : HlamStable) : KmapZero := by
  intro n ε lam T Ψ hl hP hDS B hB hr horth
  have hw : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  rcases T.irred (LinearMap.ker B) (fun k v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      show B (T.op k v) = 0
      rw [hB, hv, map_zero]) with h0 | h0
  swap
  · exact LinearMap.ker_eq_top.1 h0
  have hBinj : Function.Injective B := LinearMap.ker_eq_bot.1 h0
  let j' : T.V →ₗ[ℂ] Hlam ε Ψ T.w :=
    { toFun := fun v => ⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩
      map_add' := fun v v' => Subtype.ext (datumEmbedding_add hP T.w v v')
      map_smul' := fun c v => Subtype.ext (datumEmbedding_smul hP T.w c v) }
  let B' : T.V →ₗ[ℂ] Hlam ε Ψ T.w := B.codRestrict (Hlam ε Ψ T.w) hr
  have hj'inj : Function.Injective j' := fun a b h =>
    uniformisationL2_injective hP hw (congrArg Subtype.val h)
  have hB'inj : Function.Injective B' := fun a b h => hBinj (congrArg Subtype.val h)
  have hjint : ∀ (k : KG ε) (v : T.V), j' (T.op k v) = sigLam ε Ψ T.w (toMK k) (j' v) := by
    intro k v
    refine Subtype.ext ?_
    rw [sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]
    exact (rightRegular_datumEmbedding hP T.w v k).symm
  have hBint : ∀ (k : KG ε) (v : T.V), B' (T.op k v) = sigLam ε Ψ T.w (toMK k) (B' v) := by
    intro k v
    refine Subtype.ext ?_
    rw [sigLam_coe' hS hP (show toMK k ∈ UJset ε from k.1.2)]
    exact hB k v
  have hEq := CompanionTheory.D.LK.low_K_type_multiplicity_one n ε lam (Hlam ε Ψ T.w) (sigLam ε Ψ T.w)
    ((mir_isHCParam_iff lam).2 hl) hDS _ _ (isKTypeOf_range B' hB'inj hBint) (isKTypeOf_range j' hj'inj hjint)
  refine LinearMap.ext fun v => ?_
  have hmem : B' v ∈ (⊤ : Submodule ℂ T.V).map j' := by
    rw [← hEq]
    exact Submodule.mem_map_of_mem Submodule.mem_top
  obtain ⟨u, -, hu⟩ := hmem
  have hu' : uniformisationL2 ε Ψ T.w u = B v := congrArg Subtype.val hu
  have h2 := horth u v
  rw [hu'] at h2
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 h2

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.PhiCont
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem continuous_pP (ε : Fin n → Bool) : Continuous fun g : UJ ε => pP (toM g) := by
  have h : Continuous fun g : UJ ε => PolarDecomposition.polar_L (toM g) :=
    (lcA_polarL_continuousOn ε).comp_continuous (continuous_toM ε) (fun g => g.2)
  exact continuous_matrix_exp_alt.comp h

theorem pP_posDef {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef :=
  exp_noncompactPart_posDef (PolarDecomposition.polar_L_inP (ε := ε) g.2)

theorem phiCont : PhiCont := by
  intro n ε μ
  have hY : Continuous fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 :=
    ((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul ((continuous_pP ε).comp continuous_fst)).matrix_mul
      (Ps1.continuous_toMK'.comp continuous_snd)
  refine continuous_iff_continuousAt.2 fun z => ?_
  have hpd := posDef_conj_toMK z.2 (pP_posDef z.1)
  have hΩ : toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 ∈ OmegaSet n := posSet_subset_omega hpd
  have hc : ContinuousAt (PhiM μ) (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) :=
    ((phiM_differentiableOn μ).continuousOn).continuousAt (isOpen_omega.mem_nhds hΩ)
  show ContinuousAt (fun z : UJ ε × KG ε => (PhiM μ (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2)).re) z
  exact Complex.continuous_re.continuousAt.comp
    (hc.comp (f := fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) hY.continuousAt)

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CKContinuous
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Continuous (cK T) :=
  (continuous_const.inner ((CompactHaarProbability.cont_op T).clm_apply continuous_const)).norm

theorem op_norm {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) : ‖T.op k v‖ = ‖v‖ := by
  have h : T.op k⁻¹ * T.op k = 1 := CompactHaarProbability.op_inv_mul T k
  have hs : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).prop
  have h2 : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    congr 1
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hs, ContinuousLinearMap.one_apply]
  have := h
  nlinarith [norm_nonneg (T.op k v), norm_nonneg v, sq_nonneg (‖T.op k v‖ - ‖v‖), sq_nonneg (‖T.op k v‖ + ‖v‖)]

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  unfold cK
  calc ‖⟪T.w, T.op k T.w⟫_ℂ‖ ≤ ‖T.w‖ * ‖T.op k T.w‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [op_norm, T.w_norm, one_mul]

abbrev CPair (ε : Fin n → Bool) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ε p.1 = ε p.2}

theorem prod_cpair (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b = ∏ p : CPair ε, f p.1.1 p.1.2 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.1 x.2)]

theorem kNull_of (hW : MomW) (hP : CoefPow) : KNull := by
  intro n ε lam hl T TD
  classical
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  set F : ℝ := (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) with hF
  have hFpos : 0 < F := by positivity
  let α : CPair ε → ℝ := fun p => lam p.1.1 - lam p.1.2 + (nab ε p.1.1 p.1.2 : ℝ)
  let β : CPair ε → ℝ := fun p => ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)
  have hα : ∀ p, 0 < α p := fun p => by
    have := hl.1 p.2.1
    have : (0 : ℝ) ≤ nab ε p.1.1 p.1.2 := Nat.cast_nonneg _
    simp only [α]; linarith
  have hβ : ∀ p, 0 ≤ β p := fun p => by
    have : ((p.1.1 : ℕ) : ℝ) < ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.1
    simp only [β]; linarith

  have hmom : ∀ t : ℕ, ∫⁻ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) ∂(dk ε) =
      ENNReal.ofReal (F / ∏ p, (α p + t * β p)) := by
    intro t
    obtain ⟨Tt⟩ := kType_exists ε (lamT lam t) (isHCParam_lamT hl t)
    have e : ∀ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) = ENNReal.ofReal (cK Tt k ^ 2) := by
      intro k
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hP n ε lam hl T TD t Tt k]
      ring_nf
    simp_rw [e]
    have hint : Integrable (fun k => cK Tt k ^ 2) (dk ε) :=
      ((cK_continuous Tt).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun k => sq_nonneg _)]
    congr 1
    have hs := kschur_coef Tt Tt.w Tt.w
    rw [Tt.w_norm] at hs
    have h7 := lemma7 Tt
    have hd : (0 : ℝ) < Module.finrank ℂ Tt.V := by
      have : Nontrivial Tt.V := ⟨⟨Tt.w, 0, fun h => by have := Tt.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
      exact_mod_cast Module.finrank_pos
    have hI : ∫ k, cK Tt k ^ 2 ∂(dk ε) = (Module.finrank ℂ Tt.V : ℝ)⁻¹ := by
      unfold cK
      field_simp
      linarith
    rw [hI, h7, prod_cpair ε (fun a b => lamT lam t a - lamT lam t b + (nab ε a b : ℝ))]
    have e2 : ∀ p : CPair ε, lamT lam t p.1.1 - lamT lam t p.1.2 + (nab ε p.1.1 p.1.2 : ℝ) = α p + t * β p := by
      intro p
      simp only [lamT_apply, Dvec, α, β]
      ring
    simp_rw [e2]
    rw [inv_div]
  have h0 := hmom 0
  simp only [pow_zero, ENNReal.ofReal_one, mul_one, Nat.cast_zero, zero_mul, add_zero] at h0
  have hpos := hW (KG ε) (dk ε) (fun k => ENNReal.ofReal (cK T k ^ 2)) (fun k => cK TD k ^ 2) (CPair ε) α β F 0
    ((cK_continuous T).pow 2).measurable.ennreal_ofReal ((cK_continuous TD).pow 2).measurable
    (fun k => ⟨sq_nonneg _, by have h1 := cK_le_one TD k; have h2 : 0 ≤ cK TD k := norm_nonneg _; nlinarith⟩) hα hβ hFpos.le
    (fun t _ => hmom t)
  set s : Set (KG ε) := {k | 0 < cK TD k ^ 2} with hs
  have hsm : MeasurableSet s := measurableSet_lt measurable_const ((cK_continuous TD).pow 2).measurable
  have hsum := lintegral_add_compl (fun k => ENNReal.ofReal (cK T k ^ 2)) (μ := dk ε) hsm
  rw [hpos, h0] at hsum
  have hz : ∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε) = 0 := by
    have hne : ENNReal.ofReal (F / ∏ p, α p) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc _ = ENNReal.ofReal (F / ∏ p, α p) + (∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε)) -
          ENNReal.ofReal (F / ∏ p, α p) := by rw [ENNReal.add_sub_cancel_left hne]
      _ = 0 := by rw [hsum, tsub_self]
  have hmeas : Measurable fun k => ENNReal.ofReal (cK T k ^ 2) := by
    exact ((cK_continuous T).pow 2).measurable.ennreal_ofReal
  replace hz := (lintegral_eq_zero_iff hmeas).1 hz
  rw [Filter.EventuallyEq, ae_restrict_iff' hsm.compl] at hz
  apply hz.mono
  intro k hk h0k
  have hk' := hk (by simp [hs, h0k])
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hk'
  nlinarith [sq_nonneg (cK T k), norm_nonneg (⟪T.w, T.op k T.w⟫_ℂ)]

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.HsOpOpMul
noncomputable section

open Finset Matrix

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polar_pP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ k : KG ε, g = toMK k * pP g := by
  obtain ⟨u, hu⟩ := exists_toMK (PolarDecomposition.polar_k_mem hg)
  refine ⟨u, ?_⟩
  rw [hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]

theorem hsOp_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    hsOp (T.op k * A) = hsOp A := by
  unfold hsOp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_apply, KType_norm_op_apply]

theorem hsPol : HsPol := by
  intro n ε g hg
  refine ⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩
  obtain ⟨k, hk⟩ := polar_pP hg
  have hL := PolarDecomposition.polar_L_inP hg
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X' :=
    ⟨k, PolarDecomposition.polar_L g, hL, hk⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  have hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose :=
    hk.symm.trans hEq
  obtain ⟨-, h2⟩ := polar_unique hL hP hEq'
  rw [hsOp_op_mul, ← h2]
  rfl

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.DzSubMuNextNonneg
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inP_entry_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n}
    (h : ε a = ε b) : X a b = 0 := by
  have h1 : (Matrix.diagonal (fun c => if ε c = true then (1 : ℂ) else -1) * X *
      Matrix.diagonal (fun c => if ε c = true then (1 : ℂ) else -1)) a b = (-X) a b :=
    congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.S7.inP_JXJ hX) a) b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h1
  rw [h] at h1
  split_ifs at h1 <;> linear_combination h1 / 2

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := ReciprocityTheory.ChartRestriction.DS.S7.isHermitian_of_mem_noncompactPart' hX
  ext a b
  show (if h : b < a ∧ ε a ≠ ε b then X a b else if h' : a < b ∧ ε b ≠ ε a then star (X b a) else 0) = X a b
  split_ifs with h1 h2
  · rfl
  · have h3 := congrFun (congrFun hH a) b
    simpa [Matrix.conjTranspose_apply] using h3
  · symm
    apply inP_entry_zero hX
    by_contra hne
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact h2 ⟨hlt, fun e => hne e.symm⟩
    · exact hne (by rw [heq])
    · exact h1 ⟨hgt, hne⟩

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, hz⟩ := exists_pmat hX
  have h0 := ReciprocityTheory.ChartRestriction.DS.fi_nonneg z i
  rw [hz] at h0
  have hpos : 0 < (lead i (NormedSpace.exp X)).re := by
    have hsub := (ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef hX).submatrix (Fin.castLE_injective hi)
    show 0 < (if h : i ≤ n then ((NormedSpace.exp X).submatrix (Fin.castLE h) (Fin.castLE h)).det else 0).re
    rw [dite_eq_left hi]
    exact (Complex.pos_iff.1 hsub.det_pos).1
  exact (Real.log_nonneg_iff hpos).1 h0

theorem dz_sub_muNext_nonneg (i : Fin n) : 0 ≤ Dz n i - muNext (Dz n) i := by
  have hi := i.isLt
  show (0 : ℤ) ≤ ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) -
    (if h : (i : ℕ) + 1 < n then ((n : ℤ) - 1 - (((⟨(i : ℕ) + 1, h⟩ : Fin n) : ℕ) : ℤ)) else 0)
  split_ifs with h
  · simp only [Fin.val_mk]
    omega
  · omega

theorem phiLe : PhiLe := by
  intro n ε X hX k
  show (ReciprocityTheory.ChartRestriction.DS.S7.PhiM (Dz n)
    (ReciprocityTheory.ChartRestriction.DS.S7.toMK k⁻¹ * NormedSpace.exp X * ReciprocityTheory.ChartRestriction.DS.S7.toMK k)).re ≤ 1
  have hc := ReciprocityTheory.ChartRestriction.DS.S7.inP_conj k⁻¹ hX
  rw [inv_inv] at hc
  obtain ⟨hY, hexp⟩ := hc
  rw [← hexp]
  generalize ReciprocityTheory.ChartRestriction.DS.S7.toMK k⁻¹ * X * ReciprocityTheory.ChartRestriction.DS.S7.toMK k = Y at hY ⊢
  have hreal : ∀ j : ℕ, j ≤ n → ReciprocityTheory.ChartRestriction.DS.S7.lead j (NormedSpace.exp Y) =
      ((ReciprocityTheory.ChartRestriction.DS.S7.lead j (NormedSpace.exp Y)).re : ℂ) := by
    intro j hj
    have hPD := (ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef hY).submatrix (Fin.castLE_injective hj)
    have hp := Complex.pos_iff.1 hPD.det_pos
    show (if h : j ≤ n then ((NormedSpace.exp Y).submatrix (Fin.castLE h) (Fin.castLE h)).det else 0) =
      (((if h : j ≤ n then ((NormedSpace.exp Y).submatrix (Fin.castLE h) (Fin.castLE h)).det else 0).re : ℝ) : ℂ)
    rw [dite_eq_left hj]
    apply Complex.ext
    · simp
    · simp [← hp.2]
  have hge1 : ∀ i : Fin n, 1 ≤ (ReciprocityTheory.ChartRestriction.DS.S7.lead (↑i + 1) (NormedSpace.exp Y)).re :=
    fun i => one_le_lead_exp hY (↑i + 1) i.isLt
  have hprod : ReciprocityTheory.ChartRestriction.DS.S7.PhiM (Dz n) (NormedSpace.exp Y) =
      ((∏ i : Fin n, ((ReciprocityTheory.ChartRestriction.DS.S7.lead (↑i + 1) (NormedSpace.exp Y)).re) ^
        (-(Dz n i - ReciprocityTheory.ChartRestriction.DS.S7.muNext (Dz n) i)) : ℝ) : ℂ) := by
    show (∏ i : Fin n, ReciprocityTheory.ChartRestriction.DS.S7.lead (↑i + 1) (NormedSpace.exp Y) ^
      (-(Dz n i - ReciprocityTheory.ChartRestriction.DS.S7.muNext (Dz n) i))) = _
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← hreal (↑i + 1) i.isLt]
  rw [hprod, Complex.ofReal_re]
  apply Finset.prod_le_one₀
  · intro i _
    exact zpow_nonneg (le_trans zero_le_one (hge1 i)) _
  · intro i _
    apply zpow_le_one_of_nonpos₀ (hge1 i)
    have h4 := dz_sub_muNext_nonneg i
    linarith

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.KTypeRanges.FormFOf
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS

theorem formF_of (hS : HlamStable) (hZ : KmapZero) : FormF := by
  intro n ε lam T Ψ hl hP hDS g hg v v'
  have hv₀ : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1
    (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP T.w)) (rreg ε g (uniformisationL2 ε Ψ T.w v)))
  have hxo : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ (LinearMap.range (ffaJ hP T.w))ᗮ := by
    rw [← ffaJ_apply hP T.w q, hq]
    exact Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP T.w)) _
  have hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) (uniformisationL2 ε Ψ T.w w) = 0 := fun w =>
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP T.w) w) hxo
  have hfH : rreg ε g (uniformisationL2 ε Ψ T.w v) ∈ Hlam ε Ψ T.w := hS n ε lam T Ψ hP g hg _ (datumEmbedding_mem_Hlam hP v)
  have hxH : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ Hlam ε Ψ T.w :=
    Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)
  have hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∈ Hlam ε Ψ T.w :=
    fun k => hS n ε lam T Ψ hP _ (ffa_toMK_mem k) _ hxH
  have horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) v'')
      (uniformisationL2 ε Ψ T.w u) = 0 := by
    intro u v''
    have h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ T.w u)
        (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q)) = 0 := by
      intro k
      rw [← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]
      exact inner_eq_zero_symm.1 (hxj _)
    rw [← inner_conj_symm, ffaB_inner]
    simp only [h0, mul_zero, integral_zero, map_zero]
  have hB0 := hZ n ε lam T Ψ hl hP hDS (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q))
    (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ T.w) hRH) horth
  have hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) T.w •
      rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∂(dk ε) = 0 := by
    have := LinearMap.congr_fun hB0 T.w
    rwa [ffaB_apply, LinearMap.zero_apply] at this
  obtain ⟨yg, hyg⟩ := ffa_UJ_lift hg
  have hxae : ((rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun y => jfun Ψ T.w v (Formalism.MainNotions.S.umat y * g) - jfun Ψ T.w q (Formalism.MainNotions.S.umat y) := by
    have e1 := rreg_umat_ae ε yg (uniformisationL2 ε Ψ T.w v)
    have e2 := (measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP T.w v)
    filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ T.w v)) (uniformisationL2 ε Ψ T.w q), e1, e2, uniformisationL2_ae_eq_jfun hP T.w q]
      with y h0 h1 h2 h3
    rw [h0, Pi.sub_apply, h3, ← hyg, h1]
    congr 1
  have hFc : ContinuousOn (fun y => jfun Ψ T.w v (y * g) - jfun Ψ T.w q y) (UJset ε) :=
    ((ffa_jfun_cont hP T.w v).comp (continuousOn_id.mul continuousOn_const)
      (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP T.w q)
  have hev := ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) T.w) hBv
  have hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε →
      Ψ (S7.toMK k * h) = T.op k * Ψ h := by
    intro k h hh
    have e := hP.1 k 1 h hh
    rwa [show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one] at e
  have hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k := by
    intro k
    have e := hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))
    rwa [mul_one, hP.2.1, mul_one] at e
  have hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) T.w *
      (jfun Ψ T.w v (S7.toMK k * g) - jfun Ψ T.w q (S7.toMK k)) =
        ((‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    show inner ℂ (T.op k (Ψ g v - q)) T.w *
      (inner ℂ T.w (Ψ (S7.toMK k * g) v) - inner ℂ T.w (Ψ (S7.toMK k) q)) = _
    rw [hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub,
      ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hI : ∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0 := by
    have e2 : ((∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      refine Eq.trans ?_ hev
      congr 1
      funext k
      exact (hint k).symm
    exact_mod_cast e2
  have hD : Ψ g v - q = 0 := by
    have hk := kschur_coef T T.w (Ψ g v - q)
    rw [hI, mul_zero] at hk
    have hv0 : ‖T.w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)
    have h2 : ‖Ψ g v - q‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hk.symm with h | h
      · exact h
      · exact absurd h hv0
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hqv : q = Ψ g v := (sub_eq_zero.1 hD).symm
  have hdec : rreg ε g (uniformisationL2 ε Ψ T.w v) =
      (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) + uniformisationL2 ε Ψ T.w q := (sub_add_cancel _ _).symm
  rw [hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.KTypeRanges.HlamStable
noncomputable section

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem hlamStable : HlamStable := by
  intro n ε lam T Ψ hP g hg x hx
  have hw : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hK := datumV_isKIrrHW hP hw
  exact closure_genSub_stable (rreg_isURepOn ε) (isDerivedOn_smE (rreg_isURepOn ε)) hK.1 hK.2.1
    (datumV_casimir hP T.w) g hg x hx

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.OperatorNormSigns.ExplicitFunctionSquareIntegrable
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pl_opNorm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : ‖A‖ ^ 2 ≤ (Module.finrank ℂ V : ℝ) * hsOp A := _root_.CompanionTheory.RgFd.pl_opNorm_le (V := V) A

theorem square_integrable_of_norm : PsiNorm → PositivityTheory.RgDs.ExplicitFunctionSquareIntegrable := by
  intro hN n ε lam T μ hl hμ ν hν
  have hfin := hN n ε lam hl T μ hμ
  haveI : (show Measure (UJ ε) from muCD ε).IsHaarMeasure := muCD_isHaar ε
  set f : UJ ε → (T.V →L[ℂ] T.V) := fun g => PsiM T μ (toM g) with hf
  have hcont : Continuous f :=
    (psiM_continuousOn T μ hμ).comp_continuous (continuous_toM ε) (fun g => g.2)
  have hmCD : MemLp f 2 (muCD ε) := by
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ g : Formalism.REAL.UJ ε, ‖‖f g‖ ^ 2‖ₑ ≤
        ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) * ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) := by
      intro g
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.eNorm_eq_ofReal (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pl_opNorm_le _)
    calc ∫⁻ g, ‖‖f g‖ ^ 2‖ₑ ∂(muCD ε) ≤ ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) := lintegral_mono hle
      _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := by rw [hfin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have heq := Measure.isMulLeftInvariant_eq_smul ν (show Measure (UJ ε) from muCD ε)
  rw [heq]
  exact hmCD.smul_measure_nnreal

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.OperatorNormSigns.NormDef
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem nd_const_sign {ε : Fin n → Bool} (hq : q0 ε = 0) : ∃ s : Bool, ∀ a, ε a = s := by
  unfold q0 at hq
  rcases Nat.min_eq_zero_iff.1 hq with h | h
  · refine ⟨false, fun a => ?_⟩
    unfold pOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this
  · refine ⟨true, fun a => ?_⟩
    unfold qOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this

theorem nd_Jm {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) :
    Jm ε = (if s then (1 : ℂ) else -1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Jm, hs]
  · simp [Jm, h]

theorem nd_mem_Kset {ε : Fin n → Bool} (hq : q0 ε = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g ∈ Kset ε := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  set c : ℂ := if s then 1 else -1 with hc
  have hc0 : c ≠ 0 := by simp only [hc]; split_ifs <;> norm_num
  have hJ := nd_Jm hs
  rw [← hc] at hJ
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg'
  have hu : gᴴ * g = 1 := smul_right_injective _ hc0 hg'
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact hu), ?_⟩
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem nd_hsOp_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    hsOp (T.op k) = (Module.finrank ℂ T.V : ℝ) := _root_.CompanionTheory.RgFd.nd_hsOp_op (ε := ε) (Λ := Λ) T k

theorem nd_psiM_K {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) :
    PsiM T μ (toMK k) = T.op k := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have e := psiM_equiv T μ k 1 h1
  rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.mul_one, Matrix.mul_one, psiM_one] at e
  rw [e]
  simp [KType.op, map_one]

theorem nd_pev_zero {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : pev z = 0 := by
  have h0 : pmat z = 0 := by
    ext a b
    simp [pmat, hs]
  exact (pmat_isHermitian z).eigenvalues_eq_zero_iff.2 h0

theorem nd_jac_one {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : Jac z = 1 := by
  unfold Jac
  refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
  rw [nd_pev_zero hs z]
  simp [shc]

theorem nd_isEmpty {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) : IsEmpty (PCoord ε) :=
  ⟨fun ab => ab.2.2 (by rw [hs, hs])⟩

theorem nd_counts {ε : Fin n → Bool} (hq : q0 ε = 0) :
    (pOf ε = n ∧ qOf ε = 0) ∨ (pOf ε = 0 ∧ qOf ε = n) := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  cases s
  · right
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]
  · left
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]

theorem nd_cPQ {ε : Fin n → Bool} (hq : q0 ε = 0) : cPQ ε = 1 := by
  unfold cPQ
  have hpos : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rcases nd_counts hq with ⟨hp, hq'⟩ | ⟨hp, hq'⟩ <;> rw [hp, hq'] <;> simp [hpos.ne']

theorem nd_muCD_univ {ε : Fin n → Bool} (hq : q0 ε = 0) : muCD ε Set.univ = 1 := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  have : IsEmpty (PCoord ε) := nd_isEmpty hs
  have hvol : (volume : Measure (PCoord ε → ℂ)) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_empty_univ]
  simpa only [nd_cPQ hq, nd_jac_one hs, ENNReal.ofReal_one, lintegral_const, hvol,
    measure_univ, one_mul, mul_one] using lintegral_muCD ε (fun _ => 1) measurable_const

theorem nd_finrank {ε : Fin n → Bool} (hq : q0 ε = 0) {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (T : KType ε (lowK ε lam)) : (Module.finrank ℂ T.V : ℝ) = dimVlam lam := _root_.CompanionTheory.RgFd.nd_finrank (ε := ε) (lam := lam) hq hl T

theorem normDef : NormDef := by
  intro n ε hq lam hl T μ hμ
  have hK : ∀ g : Formalism.REAL.UJ ε, hsOp (PsiM T μ (Formalism.MainNotions.S.umat g)) = (Module.finrank ℂ T.V : ℝ) := by
    intro g
    have hg : inUJ ε (Formalism.MainNotions.S.umat g) := by
      have h := g.2
      unfold inUJ Jm
      exact h
    obtain ⟨u, hu⟩ := exists_toMK (nd_mem_Kset hq hg)
    rw [← hu, nd_psiM_K, nd_hsOp_op]
  simp only [hK, lintegral_const, nd_muCD_univ hq, mul_one]
  rw [← nd_finrank hq hl.1 T]
  congr 1
  have hpos : (0 : ℝ) < Module.finrank ℂ T.V := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by simpa [h] using T.w_norm⟩⟩
    exact_mod_cast Module.finrank_pos
  field_simp

end PositivityTheory.RgFd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.MomentRecursion.MomStep
open MeasureTheory Set

namespace PositivityTheory.RgFd

theorem mom_step {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := _root_.CompanionTheory.RgFd.mom_step (Ω := Ω) (Ω' := Ω') (ν := ν) (ν' := ν') (V := V) (V' := V') hV hV' h0 h0' he hf M

theorem mom_sum {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := _root_.CompanionTheory.RgFd.mom_sum (A := A) (W := W) m hW h

theorem momA : MomA := by
  intro Ω Ω' _ _ ν ν' U U' t0 hU hU' h h' ht he hf
  have p : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → {x | 0 < W x} = {x | 0 < W x ^ t0} := fun W h => by
    ext x
    show 0 < W x ↔ 0 < W x ^ t0
    exact ⟨fun a => pow_pos a _, fun a => (h x).1.lt_of_ne fun b => by
      rw [← b, zero_pow (by omega)] at a; exact lt_irrefl _ a⟩
  have q : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → ∀ x, 0 ≤ W x ^ t0 ∧ W x ^ t0 ≤ 1 := fun W h x =>
    ⟨pow_nonneg (h x).1 _, pow_le_one₀ (h x).1 (h x).2⟩
  rw [p U h, p U' h', mom_sum ν (hU.pow_const t0) (q U h), mom_sum ν' (hU'.pow_const t0) (q U' h')]
  refine tsum_congr fun M => mom_step (hU.pow_const t0) (hU'.pow_const t0) (q U h) (q U' h') (fun j hj => ?_)
    (fun j hj => ?_) M 1 le_rfl
  · simpa only [← pow_mul, mul_comm t0] using he j hj
  · simpa only [← pow_mul, mul_comm t0] using hf j hj

theorem momB : MomB := by
  intro I _ α β c hα hβ hc
  refine ⟨(Measure.pi fun _ : I => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
    fun y => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|)), fun y => ∏ i, Real.exp (-β i * |y i|), by fun_prop,
    fun y => ⟨Finset.prod_pos fun i _ => Real.exp_pos _, Finset.prod_le_one₀ (fun i _ => (Real.exp_pos _).le) fun i _ =>
      Real.exp_le_one_iff.2 (by have := hβ i; have := abs_nonneg (y i); nlinarith)⟩, fun t => ?_⟩
  have hp : ∀ i, 0 < α i + t * β i := fun i => by have := hα i; have := hβ i; positivity
  have e1 : ∀ i, EqOn (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (fun x => Real.exp (-(α i + t * β i) * x)) (Ioi 0) :=
    fun i x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)]
  have hi : ∀ i, Integrable (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hp i)) 0).congr_fun (e1 i).symm measurableSet_Ioi
  have hv : ∀ i, ∫ x in Ioi (0 : ℝ), Real.exp (-(α i + t * β i) * |x|) = (α i + t * β i)⁻¹ := fun i => by
    rw [setIntegral_congr_fun measurableSet_Ioi (e1 i), integral_exp_mul_Ioi (neg_neg_of_pos (hp i))]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have e2 : ∀ y : I → ℝ, ((fun y : I → ℝ => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|))) *
      fun y : I → ℝ => ENNReal.ofReal ((∏ i, Real.exp (-β i * |y i|)) ^ t)) y =
      ENNReal.ofReal (c * ∏ i, Real.exp (-(α i + t * β i) * |y i|)) := fun y => by
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [lintegral_congr e2, ← ofReal_integral_eq_lintegral_ofReal ((Integrable.fintype_prod hi).const_mul c)
    (.of_forall fun y => by positivity), integral_const_mul,
    integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Real.exp (-(α i + t * β i) * |x|))]
  simp only [hv, Finset.prod_inv_distrib, div_eq_mul_inv]

theorem momW_of : MomA → MomB → MomW := by
  intro hA hB Ω _ P h U I _ α β c t0 hh hU h01 hα hβ hc hm
  obtain ⟨ν', U', m', p', e'⟩ := hB I α β c hα hβ hc
  have e : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * (t0 + 1))) ∂(P.withDensity h) =
      ENNReal.ofReal (c / ∏ i, (α i + (j * (t0 + 1) : ℕ) * β i)) := fun j hj => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    exact hm _ (by nlinarith)
  have r := hA Ω _ (P.withDensity h) ν' U U' (t0 + 1) hU m' h01 (fun y => ⟨(p' y).1.le, (p' y).2⟩) (by omega)
    (fun j hj => (e j hj).trans (e' _).symm) fun j hj => by rw [e j hj]; exact ENNReal.ofReal_ne_top
  rw [withDensity_apply _ (measurableSet_lt measurable_const hU)] at r
  rw [r, show {y | 0 < U' y} = univ from eq_univ_of_forall fun y => (p' y).1]
  simpa using e' 0

theorem momW : MomW := momW_of momA momB

end PositivityTheory.RgFd
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.NormIndOfSteps
noncomputable section

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs

theorem hsInt : HsInt := GlobalTheory.CompanionTheory.RgFd.hsInt GlobalTheory.CompanionTheory.HsPsProof.hsPs hsPol phiMul phiCont

theorem psiNorm_of (hI : NormInd) : PsiNorm := by
  intro n ε lam hl
  by_cases h : S7.q0 ε = 0
  · exact normDef n ε h lam hl
  · have h1 : 1 ≤ min (pOf ε) (qOf ε) := Nat.one_le_iff_ne_zero.2 h
    exact hI n ε (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _)) lam hl

theorem modelDS_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : ModelDS := by
  intro n ε lam T μ hl hμ
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
      fun g hg => S7.psiM_casimir T μ hμ hg, hL n ε lam T μ hl hμ⟩
  exact ⟨hP, (hH n ε lam T _ hl hP (hK n ε lam T μ hl hμ hP)).1⟩

theorem realMetaplectic_of_forall (h : FdAll) : GlobalTheory.Published.FormalDegreeCompactDual := by
  intro cd sc hc N ε lam hl H _ _ σ w hσ hw
  have h1 := h N ε lam hl H σ hσ
  rw [GlobalTheory.FdegGap.muCD_eq_scaled cd sc hc ε] at h1
  exact fdegOf_of_isFdeg' h1 hw

theorem fdAll_of_norm (hN : PsiNorm) (hK : Key) (hH : Hilb) : FdAll :=
  have hM := modelDS_of (square_integrable_of_norm hN) hK hH
  fdAll_of hM (fdModel_of degPsi hlamStable (formF_of hlamStable (kmapZero_of hlamStable)) hN hM)

theorem normInd_of_steps (hP : CoefPow)
    (h : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd) : NormInd :=
  h momW hP (kNull_of momW hP) hsPol phiMul phiLe phiCont hsInt (gapNorm_of degPsi)

end PositivityTheory.RgFd
end
end

namespace PositivityTheory.RgFd

open PositivityTheory.RgDs

theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

theorem fdAll_of_key (hK : Key) (hH : Hilb) : FdAll := fdAll_of_norm psiNorm hK hH

end PositivityTheory.RgFd
