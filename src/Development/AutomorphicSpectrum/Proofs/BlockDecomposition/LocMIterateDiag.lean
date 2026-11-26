module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcB.F (LF)

namespace GlobalTheory.CompanionTheory.TailLocPow

theorem hint_fun_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_smul {H : Type} [Group H] (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    rStab (fun x => c * u x) = rStab u := by
  ext k
  show (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
  exact forall_congr' fun x => mul_right_inj' hc

theorem hint_smul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (u : H → ℂ) :
    hint K (fun x => c * u x) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simpa using hint_fun_zero K
  · have key : ∀ S : Subgroup H, S = rStab u →
        (((S ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (S ⊓ K), c * u q.out =
          c * ((((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out) := by
      rintro S rfl
      have h : (∑ᶠ q : H ⧸ (rStab u ⊓ K), c * u q.out) = c * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out := by
        simpa only [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)).symm
      rw [h]
      ring
    exact key _ (rStab_smul c hc u)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {k : Type} [Fintype k]

end GlobalTheory.CompanionTheory.TailLocPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProduct
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  rw [Set.ncard_le_one_iff_subsingleton]
  intro e₁ h₁ e₂ h₂
  ext a
  have i₁ := dec_injective hA Δ (h₁ a)
  have i₂ := dec_injective hA Δ (h₂ a)
  rw [← i₁, ← i₂]

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.SegSocle

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProductStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_socle_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  first | exact @GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | exact GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | (intros; apply GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLt
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLt
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem rank_fromBlocks_ge {K : Type*} [Field K] {ρ p : ℕ} (a : Matrix (Fin ρ) (Fin ρ) K)
    (ha : a.det ≠ 0) (c : Matrix (Fin p) (Fin p) K) (hc : c ≠ 0) :
    ρ + 1 ≤ (Matrix.fromBlocks a 0 0 c).rank := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Matrix.ext h)
  have hsub : (Matrix.fromBlocks a 0 0 c).submatrix
      (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j) =
      Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> rfl
  have hdet : (Matrix.fromBlocks a 0 0
      (Matrix.of fun _ _ : Unit => c i j)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using ⟨ha, hij⟩
  have hrank := Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hle := Matrix.rank_submatrix_le (Matrix.fromBlocks a 0 0 c)
    (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j)
  rw [hsub, hrank] at hle
  simpa using hle

theorem rank_dsum_ge : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  intro D n ρ p hn b₀ hb β' hβ
  have h := rank_fromBlocks_ge b₀.1 hb β'.1 hβ
  have e : (dsum hn b₀ β').1.rank = (Matrix.fromBlocks b₀.1 0 0 β'.1).rank :=
    Matrix.rank_submatrix _ (finSumFinEquiv.trans (finCongr hn)).symm
      (finSumFinEquiv.trans (finCongr hn)).symm
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.PcFc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLtStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_direct_sum_hermitian_lt : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | exact GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | (intros; apply GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Field
variable {E : Type} [Field E] {c : E →+* E}

theorem exists_congr_diag_rank (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t) {n ρ p : ℕ} (hn : ρ + p = n)
    {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, c (G a b) = G b a) (hr : ρ ≤ G.rank) :
    ∃ (a : Matrix (Fin n) (Fin n) E) (d₁ : Fin ρ → E) (d₂ : Fin p → E), a.det ≠ 0 ∧
      (a.map c).transpose * G * a = bl hn (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂) ∧
      (∀ i, c (d₁ i) = d₁ i) ∧ (∀ i, c (d₂ i) = d₂ i) ∧ ∀ i, d₁ i ≠ 0 := by
  classical
  obtain ⟨P, d, hP, hPG, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG
  have hQ : (P.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero c).mpr hP
  have hrk : (Matrix.diagonal d).rank = G.rank := by
    rw [← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (hr.trans hrk.ge)
  let e : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A : Finset (Fin n) := Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩
  have hAc : A.card = ρ := by simp [A]
  let e' : {x // x ∈ A} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])
  let σ : Equiv.Perm (Fin n) := e'.extendSubtype
  have hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0 := by
    intro i
    have hm : σ (e (Sum.inl i)) ∈ T := Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hTS hm
  refine ⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_,
    fun i => hd _, fun j => hd _, hσ⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hQ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ
        = (P.transpose * G * P.map c).submatrix σ σ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]
    rw [hmc, hPG, Matrix.submatrix_diagonal_equiv]
    unfold PositivityTheory.Rg.Rsw.bl
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y <;> simp [e]

end Field

theorem exists_cg_dsum {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n) (hr : ρ ≤ β.1.rank) :
    ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  obtain ⟨G, hG⟩ := β
  have hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t := fun t => star_star t
  obtain ⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩ := exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn
    (G := G) (fun i j => congrFun (congrFun hG j) i) hr
  have hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) →
      ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d := by
    intro m d hd
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact hd i
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩,
    ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · exact Subtype.ext hEq

end GlobalTheory.CompanionTheory.PcFc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalFormStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_diagonal_normal_form : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n), ρ ≤ β.1.rank → ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | exact GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | (intros; apply GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]


open scoped Pointwise in
theorem mean_add_left (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] {s : Set G}
    (hs : IsAddFundamentalDomain Γ s μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (t : G) :
    ∫ y in s, f (t + y) ∂μ = ∫ y in s, f y ∂μ := by
  have hFD : IsAddFundamentalDomain Γ (t +ᵥ s) μ := hs.vadd_of_comm t
  have h1 : ∫ y in (t +ᵥ s), f y ∂μ = ∫ y in s, f (t + y) ∂μ := by
    have hemb : MeasurableEmbedding (fun y : G => t + y) := (Homeomorph.addLeft t).measurableEmbedding
    exact (measurePreserving_add_left μ t).setIntegral_image_emb hemb f s
  rw [← h1]
  exact hFD.setIntegral_eq hs (fun g x => hf g.1 g.2 x)

theorem exists_bound_of_periodic (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    (f : G → ℂ) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov x
  rw [← hf γ hγ x]
  exact hC _ hk

theorem const_of_coefficients (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) (A : Type) [AddCommGroup A] (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a))
    (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y) (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1)
    (hn : ∀ a x, ‖χ a x‖ = 1) (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ∞) (φ : G → ℂ) (hφ : Continuous φ)
    (hper : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) (hco : ∀ a, a ≠ 0 → ∫ x in 𝓕, χ a x * φ x ∂μ = 0) (y : G) : φ y = φ 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨C, hC⟩ := exists_bound_of_periodic Γ hK hcov φ hφ hper
  have hint : ∀ (a : A) (f : G → ℂ), Continuous f → (∀ x, ‖f x‖ ≤ C) → IntegrableOn (fun x => χ a x * f x) 𝓕 μ := by
    intro a f hf hb
    refine Measure.integrableOn_of_bounded (M := C) hfin ((hc a).mul hf).aestronglyMeasurable (.of_forall fun x => ?_)
    rw [norm_mul, hn, one_mul]
    exact hb x
  have hshift : ∀ a, ∫ x in 𝓕, χ a x * φ (y + x) ∂μ = ∫ x in 𝓕, χ a x * φ x ∂μ := by
    intro a
    by_cases h : a = 0
    · subst h
      simp only [h0, one_mul]
      exact mean_add_left Γ μ h𝓕 φ hper y
    · have hp : ∀ γ ∈ Γ, ∀ x, χ a (γ + x) * φ (γ + x) = χ a x * φ x := fun γ hγ x => by
        rw [hper γ hγ, hx, (hker γ).2 hγ a, one_mul]
      have h1 := mean_add_left Γ μ h𝓕 (fun x => χ a x * φ x) hp y
      rw [hco a h] at h1 ⊢
      have h2 : ∫ x in 𝓕, χ a (y + x) * φ (y + x) ∂μ = χ a y * ∫ x in 𝓕, χ a x * φ (y + x) ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x => by simp only [hx, mul_assoc])
      rw [h2] at h1
      have hne : χ a y ≠ 0 := fun e => by simpa [e] using hn a y
      exact (mul_eq_zero.1 h1).resolve_left hne
  have hφy : Continuous fun x => φ (y + x) := hφ.comp (continuous_const.add continuous_id)
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha h0 hn hker μ 𝓕 hμ h𝓕
    (fun x => φ (y + x) - φ x) (hφy.sub hφ)
    (fun γ hγ x => by
      show φ (y + (γ + x)) - φ (γ + x) = φ (y + x) - φ x
      rw [add_left_comm, hper γ hγ, hper γ hγ])
    (fun a => by
      have e : ∀ x, χ a x * (φ (y + x) - φ x) = χ a x * φ (y + x) - χ a x * φ x := fun x => mul_sub _ _ _
      simp only [e]
      rw [integral_sub (hint a _ hφy fun x => hC _) (hint a _ hφ hC), hshift a, sub_self])
  have h := congrFun key 0
  simp only [add_zero, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Abstract


set_option synthInstance.maxHeartbeats 400000 in
theorem const_of_coeff : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p →
    ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ →
    (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  intro D p lp 𝓖p hC ψ hψ φ hφ hper hco y
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D p) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D p) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := p)
  refine const_of_coefficients (ratHerm D p) K hK hcov (GlobalTheory.CompanionTheory.FourierN.hermSub D p) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩), fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lp 𝓖p hlam hFD (by rw [h1]; exact ENNReal.one_ne_top) φ hφ hper
    (fun a ha => (integral_congr_ae (.of_forall fun x => mul_comm _ _)).trans
      (hco ⟨a.1, a.2⟩ (fun e => ha (Subtype.ext e)))) y

end GlobalTheory.CompanionTheory.PcFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZeroStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_const_of_fourier_coefficients_zero : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p → ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ → (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.const_of_coeff | exact GlobalTheory.CompanionTheory.PcFc.const_of_coeff | (intros; apply GlobalTheory.CompanionTheory.PcFc.const_of_coeff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishing
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisZero

open GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks (pairing gramQ mmul)

variable {D : D7} {m : ℕ}

theorem heis_zy (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {n : ℕ} (y : Mx D V.rank n) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : EC.Heisenberg₂ ψ V (zy y) Φ z = pairing V.gram ψ z y * Φ z := by
  have hx : xPart (zy y) = 0 := by
    ext i j
    simp only [xPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.zero_apply]
  have hy : yPart (zy y) = y := by
    ext i j
    simp only [yPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  have hin : ∀ x : Mx D V.rank n, GlobalTheory.StdUnn.inner V x y = gramQ V.gram x y := fun x => by
    unfold GlobalTheory.StdUnn.inner gramQ mmul
    rw [Matrix.mul_assoc]
    rfl
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner]
  unfold EC.Heisenberg₂
  have htr0 : GlobalTheory.StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [hx, hy, h0, add_zero, Matrix.trace_zero, halfTr, htr0, mul_zero, add_zero, hin]
  rfl

theorem pairing_add_right (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (x y y' : Mx D m n) : pairing T ψ x (y + y') = pairing T ψ x y * pairing T ψ x y' := by
  unfold pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA gramQ mmul
  rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]

theorem continuous_pairing (T : Matrix (Fin m) (Fin m) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {n : ℕ} (x : Mx D m n) : Continuous (pairing T ψ x) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold pairing gramQ mmul
  exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)

theorem pairing_zero_left (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (y : Mx D m n) : pairing T ψ 0 y = 1 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj (0 : Mx D m n) = 0 := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj, Formalism.UG.cT]
  simp [pairing, gramQ, mmul, h, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA]


open Classical in
theorem char_integral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {n : ℕ}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ∫ y in 𝓕, pairing V.gram ψ (ξ.map (incA D)) y ∂μ = if ξ = 0 then 1 else 0 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram (isHermND_gram V) ψ hψ
  split_ifs with hξ
  · subst hξ
    have h0 : (0 : Matrix (Fin V.rank) (Fin n) D.host.E).map (incA D) = 0 := by
      ext i j
      simp
    simp only [h0, pairing_zero_left, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hμ.2.2]
  · set ξ' : Mx D V.rank n := ξ.map (incA D) with hξ'
    have hrat : ξ' ∈ ratMx D V.rank n := ⟨ξ, rfl⟩
    have hne : ξ' ≠ 0 := by
      intro h
      apply hξ
      exact Matrix.ext fun i j => incA_injective ((congrFun (congrFun h i) j).trans (map_zero (incA D)).symm)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, pairing V.gram ψ ξ' y₀ ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (h2 ξ' hrat hc)
    have hper : ∀ γ ∈ ratMx D V.rank n, ∀ a, pairing V.gram ψ ξ' (γ + a) = pairing V.gram ψ ξ' a := by
      intro γ hγ a
      rw [pairing_add_right, (h1 γ).2 hγ ξ' hrat, one_mul]
    have key := GlobalTheory.TowerRestrict.setIntegral_add_right hμ (pairing V.gram ψ ξ') hper y₀
    simp only [pairing_add_right, integral_mul_const] at key
    have : (∫ y in 𝓕, pairing V.gram ψ ξ' y ∂μ) * (pairing V.gram ψ ξ' y₀ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hy₀)


open Classical in
theorem zero : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  intro D ψ hψ θ hθ V n μ 𝓕 hμ Φ hΦ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI i6 : DiscreteTopology (ratMx D V.rank n) := i5
  haveI i7 : SecondCountableTopology (ratMx D V.rank n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D V.rank n) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) := by
    let g : Matrix (Fin V.rank) (Fin n) D.host.E → ratMx D V.rank n := fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩
    have hg : Function.Injective g := by
      intro a b h
      have h' := congrArg Subtype.val h
      exact Matrix.ext fun i j => incA_injective (congrFun (congrFun h' i) j)
    exact hg.countable
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; exact ENNReal.one_ne_top)
  simp only [heis_zy]
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → Mx D V.rank n → ℂ :=
    fun ξ y => pairing V.gram ψ (ξ.map (incA D)) y * Φ (ξ.map (incA D)) with hF
  have hnorm : ∀ ξ y, ‖F ξ y‖ = ‖Φ (ξ.map (incA D))‖ := by
    intro ξ y
    simp only [hF, norm_mul, pairing, hψ.2.1, one_mul]
  have hint : ∀ ξ, Integrable (F ξ) (μ.restrict 𝓕) := fun ξ =>
    (integrable_const ‖Φ (ξ.map (incA D))‖).mono'
      ((continuous_pairing V.gram hψ _).mul continuous_const).aestronglyMeasurable
      (ae_of_all _ fun y => (hnorm ξ y).le)
  have hsum : Summable fun ξ => ∫ y, ‖F ξ y‖ ∂(μ.restrict 𝓕) := by
    simp only [hnorm, integral_const, smul_eq_mul]
    have hr : (μ.restrict 𝓕).real Set.univ = 1 := by simp [Measure.real, hμ.2.2]
    simp only [hr, one_mul]
    exact GlobalTheory.SiegelWeilLitCompare.summable_rat hθ ⟨Φ, hΦ⟩
  show Φ 0 = ∫ y in 𝓕, ∑' ξ, F ξ y ∂μ
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [hF, integral_mul_const, char_integral hψ V hμ]
  rw [tsum_eq_single 0]
  · simp
  · intro b hb
    simp [hb]

end GlobalTheory.CompanionTheory.EisZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_vanishing : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  first | exact @GlobalTheory.CompanionTheory.EisZero.zero | exact GlobalTheory.CompanionTheory.EisZero.zero | (intros; apply GlobalTheory.CompanionTheory.EisZero.zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugation
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc GlobalTheory.CompanionTheory.FourierN
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n : ℕ}

theorem adj_mul_sq (x y : Mx D n n) : adj (x * y) = adj y * adj x := adj_mul x y

theorem rat_mul_sq (x y : Matrix (Fin n) (Fin n) D.host.E) : (rat (x * y) : Mx D n n) = rat x * rat y := rat_mul x y

theorem rat_one_sq : (rat (1 : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n) = 1 :=
  Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))

theorem adj_one_sq : adj (1 : Mx D n n) = 1 := by
  rw [← rat_one_sq, ← rat_conjTranspose, Matrix.conjTranspose_one]

theorem rat_gl_mul_inv (a : GL (Fin n) D.host.E) : (rat a.1 * rat (a⁻¹).1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show a.1 * (a⁻¹).1 = 1 from by simp, rat_one_sq]

theorem rat_gl_inv_mul (a : GL (Fin n) D.host.E) : (rat (a⁻¹).1 * rat a.1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show (a⁻¹).1 * a.1 = 1 from by simp, rat_one_sq]

def congH (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) : hermA D n :=
  ⟨rat u * b.1 * adj (rat u), by
    show adj (rat u * b.1 * adj (rat u)) = _
    have hb : adj b.1 = b.1 := b.2
    rw [adj_mul_sq, adj_mul_sq, adj_adj, hb, mul_assoc]⟩

theorem congH_val (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) :
    (congH u b).1 = rat u * b.1 * adj (rat u) := rfl

theorem congH_cancel {u v : Matrix (Fin n) (Fin n) D.host.E} (h : (rat u * rat v : Mx D n n) = 1) (b : hermA D n) :
    congH u (congH v b) = b := by
  apply Subtype.ext
  have h' : (adj (rat v) * adj (rat u) : Mx D n n) = 1 := by rw [← adj_mul_sq, h, adj_one_sq]
  rw [congH_val, congH_val]
  calc rat u * (rat v * b.1 * adj (rat v)) * adj (rat u)
      = (rat u * rat v) * b.1 * (adj (rat v) * adj (rat u)) := by simp only [mul_assoc]
    _ = b.1 := by rw [h, h', one_mul, mul_one]

theorem continuous_congH (u : Matrix (Fin n) (Fin n) D.host.E) : Continuous (congH (D := D) u) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem congH_rat (u : Matrix (Fin n) (Fin n) D.host.E) {b : hermA D n} (hb : b ∈ ratHerm D n) : congH u b ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ := hb
  have hη' : b.1 = rat η := hη.symm
  refine ⟨u * η * uᴴ, ?_⟩
  show rat (u * η * uᴴ) = rat u * b.1 * adj (rat u)
  rw [rat_mul_sq, rat_mul_sq, rat_conjTranspose, hη']

def tauH (a : GL (Fin n) D.host.E) : hermA D n ≃ₜ+ hermA D n where
  toFun := congH (a⁻¹).1
  invFun := congH a.1
  left_inv := congH_cancel (rat_gl_mul_inv a)
  right_inv := congH_cancel (rat_gl_inv_mul a)
  map_add' b c := by
    apply Subtype.ext
    show rat (a⁻¹).1 * (b.1 + c.1) * adj (rat (a⁻¹).1) = rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1) + rat (a⁻¹).1 * c.1 * adj (rat (a⁻¹).1)
    rw [mul_add, add_mul]
  continuous_toFun := continuous_congH _
  continuous_invFun := continuous_congH _

theorem tauH_apply (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b = congH (a⁻¹).1 b := rfl

theorem tauH_rat (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b ∈ ratHerm D n ↔ b ∈ ratHerm D n := by
  refine ⟨fun h => ?_, fun h => congH_rat _ h⟩
  have := congH_rat a.1 h
  rwa [tauH_apply, congH_cancel (rat_gl_mul_inv a)] at this

theorem exists_levi_rat (a : GL (Fin n) D.host.E) :
    ∃ q : G D n, q ∈ GF D n ∧ mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
  obtain ⟨q, hq⟩ := exists_levi (D := D) (n := n) (Matrix.GeneralLinearGroup.map (incA D) a)
  have hq' : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    rw [hq, ← map_inv]
    rfl
  refine ⟨q, ?_, hq'⟩
  have e1 : a.1 * (a⁻¹).1 = 1 := by simp
  have e2 : (a⁻¹).1 * a.1 = 1 := by simp
  have e3 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e4 : a.1ᴴ * ((a⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  let x : GL (Fin (n + n)) D.host.E := ⟨blk4 a.1 0 0 ((a⁻¹).1)ᴴ, blk4 (a⁻¹).1 0 0 a.1ᴴ,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e3]; exact block_matrix_one,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e2, e4]; exact block_matrix_one⟩
  have hm : x.1.map (incA D) = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    simp only [x, blk4_map_alt]
    rw [Matrix.map_zero _ (map_zero _)]
    rfl
  refine ⟨x, ?_, Units.ext (hm.trans hq'.symm)⟩
  apply rat_injective (D := D)
  have h2 : adj (mat q) * JR (AF D.host.F) (Jst D n) * mat q = JR (AF D.host.F) (Jst D n) := q.2
  rw [hq', ← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

theorem nb_levi {nb : hermA D n → G D n} (hnb : IsNMap nb) (a : GL (Fin n) D.host.E) {q : G D n}
    (hq : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))) (b : hermA D n) : nb b * q = q * nb (tauH a b) := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb b) * mat q = mat q * mat (nb (tauH a b))
  rw [hnb, hnb, hq, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, tauH_apply, congH_val]
  have e : rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = b.1 * adj (rat (a⁻¹).1) := by
    rw [← mul_assoc, ← mul_assoc, rat_gl_mul_inv, one_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e]

theorem trace_cg (a : GL (Fin n) D.host.E) (β : HermE D n) (b : hermA D n) :
    Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) := by
  have h1 : ((cg a β).1.map (incA D) : Mx D n n) = adj (rat a.1) * rat β.1 * rat a.1 := by
    show rat (_ * β.1 * a.1) = _
    rw [rat_mul_sq, rat_mul_sq]
    rfl
  have h2 : (adj (rat (a⁻¹).1) * adj (rat a.1) : Mx D n n) = 1 := by rw [← adj_mul_sq, rat_gl_mul_inv, adj_one_sq]
  show Matrix.trace ((cg a β).1.map (incA D) * (tauH a b).1 : Mx D n n) = Matrix.trace (rat β.1 * b.1 : Mx D n n)
  rw [h1, tauH_apply, congH_val]
  have e : adj (rat a.1) * rat β.1 * rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) =
      adj (rat a.1) * ((rat β.1 * b.1) * adj (rat (a⁻¹).1)) := by
    calc _ = adj (rat a.1) * rat β.1 * (rat a.1 * rat (a⁻¹).1) * b.1 * adj (rat (a⁻¹).1) := by simp only [mul_assoc]
      _ = _ := by rw [rat_gl_mul_inv]; simp only [mul_assoc, mul_one]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h2, mul_one]


set_option synthInstance.maxHeartbeats 400000 in
theorem fc_levi : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F →
    LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 →
    ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  intro D n ψ hψ F _ hinv nb lam 𝓖 hC a β
  obtain ⟨hnb, hlam, hFD, hvol⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨q, hqF, hq⟩ := exists_levi_rat (D := D) a
  refine ⟨q, fun g => ?_⟩
  let f : hermA D n → ℂ := fun c =>
    F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))
  have hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x := by
    intro γ hγ x
    have e1 : F (nb (γ + x) * g) = F (nb x * g) := by
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1) := by
      rw [show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]
    show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)
    rw [e1, e2]
  have key := mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf
  unfold fc
  refine Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key
  show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) =
    F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))
  rw [trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]

end GlobalTheory.CompanionTheory.PcFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugationStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_conjugation : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 → ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.fc_levi | exact GlobalTheory.CompanionTheory.PcFc.fc_levi | (intros; apply GlobalTheory.CompanionTheory.PcFc.fc_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrability
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrability
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

theorem integral_nonneg_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0 := by
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal
    exact Complex.ext (by simp) (by simp [(hn x).2])
  rw [e2]
  exact ⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩

theorem lintegral_enorm_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : ∫⁻ x, ‖f x‖ₑ ∂μ = ‖∫ x, f x ∂μ‖ₑ := by
  have e : ∀ x, f x = ((f x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [(hn x).2])
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have h0 : 0 ≤ ∫ x, (f x).re ∂μ := integral_nonneg fun x => (hn x).1
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    exact Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal
  have e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re := fun x => by
    conv_lhs => rw [e x]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]
  rw [lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2,
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

variable {D : D7}

theorem integrable_ik {θ : InfFam D} (hθ : IsInfFam θ) {T T' : HSp D} {t n : ℕ} (d : HypDec T T' t)
    (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure] {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n)
    (a : Mx D T'.rank n) : Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact (GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

theorem integrable_K {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)} (hK : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] {Φ : Mx D T.rank n → ℂ} (hΦ : Continuous Φ) (x : Mx D T.rank n) :
    Integrable (fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)) ν := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hB : BorelSpace (GA D T) := ⟨rfl⟩
  have hKB : BorelSpace K := Subtype.borelSpace _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x) :=
    hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting


open IkLintProof in
theorem ikLint : IkLint := by
  intro D n t B W d I θ hθ M hM hn a
  haveI := I.probK
  obtain ⟨𝓕, hμ⟩ := I.cov₁
  haveI := hμ.1
  have hK := (GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2
  have hP : projS I.νK M ∈ schwartzA θ B.rank n := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK _ hM
  have hc : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hi := fun x => integrable_K hK I.νK hc x
  have inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ :=
    fun x => lintegral_enorm_eq (hi x) fun k => hn _
  have pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0 :=
    fun x => integral_nonneg_real fun k => hn _
  rw [lintegral_congr fun U => inner _]
  exact lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrabilityStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_section_local_integrability : IkLint := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | exact GlobalTheory.CompanionTheory.ColumnSplitting.ikLint | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.ikLint <;> assumption)
end
end
