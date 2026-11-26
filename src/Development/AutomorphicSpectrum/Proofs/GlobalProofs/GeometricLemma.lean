module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetOfInducedFiltration

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
namespace GlobalTheory.CompanionTheory.GeoLink

theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := GlobalTheory.T.induced_cell_semisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzeroStatement
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι], ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_test : ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero F ι

theorem selfDual_eq (G : Matrix ι ι F) (hs : G.IsSymm) (hG : G.det ≠ 0) (ν : Measure (ι → 𝔸[F]))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual ν (chiG G)) : ν = adeleMeasurePi F := by
  obtain ⟨f0, hf0, hcs, h0⟩ := exists_test (F := F) (ι := ι)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hNM : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hMN : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hu
  set Gm := G.map (algebraMap F 𝔸[F]) with hGm
  have hH := h.1
  have e : ν = Measure.addHaarScalarFactor ν (adeleMeasurePi F) • adeleMeasurePi F :=
    Measure.isAddLeftInvariant_eq_smul ν (adeleMeasurePi F)
  set c : NNReal := Measure.addHaarScalarFactor ν (adeleMeasurePi F) with hcdef

  have hT0 : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂(adeleMeasurePi F) = adelicFourierPi F g (Gm *ᵥ y) := fun g y => rfl
  have hT : ∀ (g : (ι → 𝔸[F]) → ℂ) y, ∫ x, g x * chiG G x y ∂ν = (c : ℂ) * adelicFourierPi F g (Gm *ᵥ y) := by
    intro g y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hT0]
  set g1 : (ι → 𝔸[F]) → ℂ := fun y => adelicFourierPi F f0 (Gm *ᵥ y) with hg1
  have hg1m : g1 ∈ schwartzBruhatPi (K := F) (ι := ι) :=
    comp_mulVec_mem_schwartzBruhatPi G G⁻¹ hNM hMN (adelicFourierPi_mem_schwartzBruhatPi hf0)
  have hI : Integrable (fun y => ∫ x, f0 x * chiG G x y ∂ν) ν := by
    simp only [hT]
    rw [e]
    exact ((integrable_of_mem_schwartzBruhatPi hg1m).const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := h.2 f0 (continuous_of_mem_schwartzBruhatPi hf0) hcs hI 0
  simp only [hT] at h2
  have h3 : adelicFourierPi F (fun x => (c : ℂ) * adelicFourierPi F f0 (Gm *ᵥ x)) (Gm *ᵥ 0) =
      (c : ℂ) * adelicFourierPi F g1 (Gm *ᵥ 0) :=
    congrFun (adelicFourierPi_smul (c : ℂ) g1) _
  have h4 : adelicFourierPi F g1 (Gm *ᵥ 0) = f0 0 := by
    rw [Matrix.mulVec_zero, hg1, adelicFourierPi_comp_mulVec G G⁻¹ hNM hMN, Matrix.mulVec_zero,
      adelicFourierPi_adelicFourierPi hf0]
    simp
  rw [h3, h4, neg_zero, ← mul_assoc] at h2
  have h5 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ h0 (by rw [h2, one_mul])
  have h6 : c * c = 1 := by exact_mod_cast h5
  have h7 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h6
    have h8 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h8
  rw [e, h7, one_smul]

theorem selfDual_transport {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ V') (he : ∀ x y, e (x + y) = e x + e y)
    (χ : V → V → ℂ) (χ' : V' → V' → ℂ) (hχ : ∀ x y, χ' (e x) (e y) = χ x y) (μ : Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ χ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual (μ.map e) χ' := by
  have hμ := h.1
  let a : V ≃+ V' := AddEquiv.mk' e.toEquiv he
  have ha : ∀ x, a x = e x := fun _ => rfl
  refine ⟨a.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  have hemb := e.measurableEmbedding
  set Φ0 : V → ℂ := fun x => Φ (e x) with hΦ0
  have hT : ∀ y, ∫ x, Φ x * χ' x (e y) ∂(μ.map e) = ∫ x, Φ0 x * χ x y ∂μ := by
    intro y
    rw [hemb.integral_map]
    simp only [hΦ0, hχ]
  have hI' : Integrable (fun y => ∫ x, Φ0 x * χ x y ∂μ) μ := by
    have h1 := (hemb.integrable_map_iff).1 hI
    exact h1.congr (Filter.Eventually.of_forall fun y => by simp only [Function.comp_apply, hT])
  have h2 := h.2 Φ0 (hc.comp e.continuous) (hs.comp_homeomorph e) hI' (e.symm z)
  rw [hemb.integral_map]
  have h3 : Φ0 (-e.symm z) = Φ (-z) := by
    simp only [hΦ0]
    rw [← ha, map_neg, ha, e.apply_symm_apply]
  rw [← h3, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [hT y, ← hχ y (e.symm z), e.apply_symm_apply]

end Gen

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.CoordMat
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Link

section Main
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

end Main
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemUnipOfArchFrame
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.GoodPos

open GlobalTheory.StdPar GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {r : ℕ}

theorem pow_support (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) (k : ℕ) :
    ∀ i j, (Q ^ (k + 1)) i j ≠ 0 → P i j ∧ i.val + k + 1 ≤ j.val := by
  induction k with
  | zero =>
    intro i j h
    rw [zero_add, pow_one] at h
    have := hQ i j h
    exact ⟨this, by have := hPlt i j this; rw [Fin.lt_def] at this; omega⟩
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have h2 := hQ l j (right_ne_zero_of_mul hl)
    refine ⟨hPt i l j h1.1 h2, ?_⟩
    have := hPlt l j h2
    rw [Fin.lt_def] at this
    omega

theorem exists_inv_pattern (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) :
    ∃ Q' : Matrix (Fin r) (Fin r) A, (∀ i l, Q' i l ≠ 0 → P i l) ∧ (1 + Q) * (1 + Q') = 1 := by
  have hQn : ∀ i l, (-Q) i l ≠ 0 → P i l := fun i l h => hQ i l (by simpa using h)
  have hnil : (-Q) ^ (r + 1) = 0 := by
    ext i j
    by_contra h
    have := (pow_support P hPt hPlt (-Q) hQn r i j h).2
    have := j.2
    omega
  refine ⟨∑ t ∈ Finset.range r, (-Q) ^ (t + 1), fun i l h => ?_, ?_⟩
  · rw [Matrix.sum_apply] at h
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (pow_support P hPt hPlt (-Q) hQn t i l ht).1
  · have e := mul_neg_geom_sum (-Q) (r + 1)
    rw [hnil, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix _ _ _)] at e
    exact e

end Lin

section Main

theorem mem_unip_of_arch_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (Xf : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)) (u : GAd σ J), u ∈ infPts σ J →
    (∀ w : InfinitePlace F, ∃ N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E),
      (matHom _ σ J (projArch σ J w u)).1 * Xf.map (inclR (F := F) w.Completion) =
        Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
      (∀ i j, N i j ≠ 0 → ∃ k ∈ S, i ≤ k ∧ k < j) ∧
      (∀ v : Fin n → w.Completion ⊗[F] E,
        (∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ v) i = 0) →
        ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → ∃ k ∈ S, i ≤ k) ∧
          (matHom _ σ J (projArch σ J w u)).1 *ᵥ v - v = Xf.map (inclR (F := F) w.Completion) *ᵥ a)) →
    u ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  intro F E _ _ _ _ _ σ n J r Xf S u hu hN
  classical
  choose Nw hM hQw hPw using hN
  let ψ : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  let N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun i v => glueInf F E (fun w => Nw w i v)
  have hcN : ∀ w, N.map (compInf F E w) = Nw w := fun w => Matrix.ext fun i v => compInf_glueInf _ w
  have hsN : N.map ψ = 0 := Matrix.ext fun i v => sndA_glueInf _
  have hcZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E) (w : InfinitePlace F),
      (adMat F Z).map (compInf F E w) = Z.map (inclR (F := F) w.Completion) := fun Z w =>
    Matrix.ext fun i j => by
      show compInf F E w ((1 : AF F) ⊗ₜ[F] Z i j) = (1 : w.Completion) ⊗ₜ[F] Z i j
      simp [compInf]
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u).1 with hMdef
  have hcM : ∀ w, M.map (compInf F E w) = (matHom _ σ J (projArch σ J w u)).1 := fun w =>
    Matrix.ext fun a b => by rw [matHom_projArch]; rfl
  have hsM : M.map ψ = 1 := Matrix.ext fun a b =>
    congrArg (fun g => (g : GL (Fin n) _).1 a b) hu
  set C := adMat F Xf with hC
  have hMat : M * C = C + C * N := by
    ext a b
    apply tens_ext
    · intro w
      have e1 : compInf F E w ((M * C) a b) = ((M * C).map (compInf F E w)) a b := rfl
      have e2 : compInf F E w ((C + C * N) a b) = ((C + C * N).map (compInf F E w)) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hcM, hcN, hC, hcZ, hM w]
    · show ψ _ = ψ _
      have e1 : ψ ((M * C) a b) = ((M * C).map ψ) a b := rfl
      have e2 : ψ ((C + C * N) a b) = ((C + C * N).map ψ) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hsM, hsN, Matrix.one_mul,
        Matrix.mul_zero, add_zero]
  let P : Fin r → Fin r → Prop := fun i j => ∃ k ∈ S, i ≤ k ∧ k < j
  have hPt : ∀ i l j, P i l → P l j → P i j := fun i l j ⟨k, hk, h1, h2⟩ ⟨k', hk', h1', h2'⟩ =>
    ⟨k', hk', h1.trans (h2.le.trans h1'), h2'⟩
  have hPlt : ∀ i l, P i l → i < l := fun i l ⟨k, _, h1, h2⟩ => lt_of_le_of_lt h1 h2
  have hQ : ∀ i l, N i l ≠ 0 → P i l := by
    intro i l h
    by_contra hc
    apply h
    have : (fun w => Nw w i l) = fun _ => 0 := funext fun w => by
      by_contra h'
      exact hc (hQw w i l h')
    show glueInf F E _ = 0
    rw [this, glueInf_zero]
  obtain ⟨N', hQ', hinv⟩ := exists_inv_pattern P hPt hPlt N hQ
  set M' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u⁻¹).1 with hM'def
  have hM'M : M' * M = 1 := by
    rw [hM'def, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hMC : M * C = C * (1 + N) := by rw [hMat, Matrix.mul_add, Matrix.mul_one]
  have hM'C : M' * C = C * (1 + N') := by
    calc M' * C = M' * (C * ((1 + N) * (1 + N'))) := by rw [hinv, Matrix.mul_one]
      _ = M' * (M * C) * (1 + N') := by rw [hMC]; simp only [Matrix.mul_assoc]
      _ = C * (1 + N') := by rw [← Matrix.mul_assoc, hM'M, Matrix.one_mul]
  have hsupp : ∀ (D : Set (Fin r)) (Q : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)), (∀ i l, Q i l ≠ 0 → P i l) →
      (∀ i l, P i l → l ∈ D → i ∈ D) → ∀ a : Fin r → AF F ⊗[F] E, (∀ l, l ∉ D → a l = 0) →
      ∀ l, l ∉ D → ((1 + Q) *ᵥ a) l = 0 := by
    intro D Q hq hD a ha i hi
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, ha i hi, zero_add]
    show ∑ l, Q i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : Q i l = 0
    · rw [h, zero_mul]
    · rw [ha l (fun hl => hi (hD i l (hq i l h) hl)), mul_zero]
  have hstab : ∀ D : Set (Fin r), (∀ i l, P i l → l ∈ D → i ∈ D) →
      ∀ y, y ∈ colSpan F Xf D ↔ M *ᵥ y ∈ colSpan F Xf D := by
    intro D hD y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := (mem_span_cols_iff C D y).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N) *ᵥ a, hsupp D N hQ hD a ha, ?_⟩
      rw [mulVec_mulVec, mulVec_mulVec, hMC]
    · intro hy
      obtain ⟨a, ha, hay⟩ := (mem_span_cols_iff C D _).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N') *ᵥ a, hsupp D N' hQ' hD a ha, ?_⟩
      rw [mulVec_mulVec, ← hM'C, ← mulVec_mulVec, hay, mulVec_mulVec, hM'M, one_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨fun y => hstab _ (fun i l h hl => hPt i l j h hl) y, fun y hy => ?_⟩,
    hstab _ (fun i l ⟨k, hk, h1, _⟩ _ => ⟨k, hk, h1⟩), fun y hy => ?_⟩
  · rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    show M *ᵥ _ - _ ∈ _
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ((mem_span_cols_iff C _ _).2 ⟨fun i => N i j, fun l hl => ?_, ?_⟩)
    · by_contra h
      exact hl (hQ l j h)
    · have e : M *ᵥ Cᵀ j = fun i => (M * C) i j := by
        funext i
        simp [mulVec, dotProduct]
        rfl
      rw [e, hMat]
      funext i
      show (C *ᵥ fun i => N i j) i = (C + C * N) i j - C i j
      rw [Matrix.add_apply, add_sub_cancel_left]
      rfl
  · have hy' : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ y) i = 0 := fun i hi =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy i) hi
    have hyw : ∀ w : InfinitePlace F, ∀ i : Fin r, (∃ k ∈ S, i ≤ k) →
        ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ (compInf F E w ∘ y)) i = 0 := by
      intro w i hi
      have := congrArg (compInf F E w) (hy' i hi)
      rwa [RingHom.map_mulVec, hcZ, map_zero] at this
    choose a ha hA using fun w => hPw w (compInf F E w ∘ y) (hyw w)
    let A : Fin r → AF F ⊗[F] E := fun i => glueInf F E (fun w => a w i)
    have hcA : ∀ w, compInf F E w ∘ A = a w := fun w => funext fun i => compInf_glueInf _ w
    have hsA : ψ ∘ A = 0 := funext fun i => sndA_glueInf _
    refine (mem_span_cols_iff C _ _).2 ⟨A, fun l hl => ?_, ?_⟩
    · have : (fun w => a w l) = fun _ => 0 := funext fun w => by
        by_contra h'
        exact hl (ha w l h')
      show glueInf F E _ = 0
      rw [this, glueInf_zero]
    · funext i
      apply tens_ext
      · intro w
        have e1 : compInf F E w ((M *ᵥ y - y) i) =
            ((matHom _ σ J (projArch σ J w u)).1 *ᵥ (compInf F E w ∘ y) - compInf F E w ∘ y) i := by
          rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, hcM]
          rfl
        rw [e1, congrFun (hA w) i, RingHom.map_mulVec, hC, hcZ, hcA]
      · show ψ _ = ψ _
        rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hsM, one_mulVec, hsA, mulVec_zero]
        simp

end Main

end GlobalTheory.CompanionTheory.GoodPos
end
end
