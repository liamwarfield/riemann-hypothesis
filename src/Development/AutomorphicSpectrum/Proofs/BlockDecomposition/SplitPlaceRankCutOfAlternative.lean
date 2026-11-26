module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizer
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizerStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_valuation_uniformizer : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  first | exact @GlobalTheory.CompanionTheory.Jp.nvOK_nvL | exact GlobalTheory.CompanionTheory.Jp.nvOK_nvL | (intros; apply GlobalTheory.CompanionTheory.Jp.nvOK_nvL <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompact
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RhoSplit

theorem exists_lift {A B C : Type} [Group A] [Group B] [Group C] (φ : A →* C) (ι : B →* C)
    (hι : Function.Injective ι) (h : ∀ a, φ a ∈ ι.range) : ∃ ρ : A →* B, ∀ a, φ a = ι (ρ a) := by
  refine ⟨((MonoidHom.ofInjective hι).symm.toMonoidHom).comp (φ.codRestrict ι.range h), fun a => ?_⟩
  have := (MonoidHom.ofInjective hι).apply_symm_apply (φ.codRestrict ι.range h a)
  exact (congrArg Subtype.val this).symm

theorem inL_injective {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L]
    (h : Function.Injective (algebraMap O L)) {n : ℕ} :
    Function.Injective (inL (O := O) (L := L) (n := n)) := by
  intro a b e
  apply Units.ext
  ext i j
  apply h
  have := congrArg (fun g : GL (Ix n) L => g.1 i j) e
  simpa using this

theorem mem_level_square_congruence_iff {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (ϖ : O) (κ : GL (Ix n) O) :
    κ ∈ Gam2 (n := n) ϖ ↔
      ∀ i j, κ.1 i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ Ideal.span {ϖ ^ 2} := by
  have h1 : (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) =
      (1 : Matrix (Ix n) (Ix n) O).map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  unfold Gam2
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, h1]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact Ideal.Quotient.eq.1 (by simpa using this)
  · intro h
    ext i j
    simpa using Ideal.Quotient.eq.2 (h i j)

theorem isOpen_ideal (D : D7) (v : Pl D) (ϖ : Ov D v) (h : ϖ ≠ 0) :
    IsOpen {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} := by
  have hc : algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) ≠ 0 := by
    intro e
    exact pow_ne_zero 2 h (Subtype.val_injective (by simpa using e))
  set c := algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) with hcdef
  have hO : IsOpen ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) :=
    Valued.isOpen_valuationSubring _
  have hs : {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} =
      (fun x => c⁻¹ * x) ⁻¹' ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have : c⁻¹ * algebraMap (Ov D v) (Lv D v) (z * ϖ ^ 2) = algebraMap (Ov D v) (Lv D v) z := by
        rw [map_mul, ← hcdef]; field_simp
      simp only [Set.mem_preimage, this]
      exact z.2
    · intro hx
      refine ⟨⟨c⁻¹ * x, hx⟩ * ϖ ^ 2, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [map_mul, ← hcdef]
      have : algebraMap (Ov D v) (Lv D v) ⟨c⁻¹ * x, hx⟩ = c⁻¹ * x := rfl
      rw [this]; field_simp
  rw [hs]
  exact hO.preimage (continuous_const.mul continuous_id)

theorem continuous_entry (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Ix n) :
    Continuous fun k : KAt D n v => (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j := by
  have h1 : Continuous fun k : KAt D n v =>
      splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k) :=
    (continuous_splitHom τ).comp ((continuous_proj _ _ v).comp continuous_subtype_val)
  have h2 : Continuous fun k : KAt D n v =>
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k)).1 :=
    Units.continuous_val.comp h1
  exact h2.matrix_elem (finSumFinEquiv i) (finSumFinEquiv j)

theorem exists_rho (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v),
      (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧
      Function.Surjective ρ ∧
      ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  have hinj : Function.Injective (inL (O := Ov D v) (L := Lv D v) (n := n)) :=
    inL_injective Subtype.val_injective
  have hmem : ∀ k : KAt D n v, ((thU D n v τ).comp ((proj D.sp.cm.sig (Jst D n) v).comp (KAt D n v).subtype)) k ∈
      (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
    intro k
    have hk : (k : G D n) ∈ GlobalTheory.LocIntw.KUpAd D.sp.cm.sig (Jst D n) := (Subgroup.mem_inf.1 k.2).1
    exact (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ _).1 ((GlobalTheory.LocIntw.mem_KUpAd.1 hk).1 v)
  obtain ⟨ρ, hρ⟩ := exists_lift _ _ hinj hmem
  have hρ' : ∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k) := hρ
  refine ⟨ρ, hρ', ?_, ?_⟩
  · intro κ
    obtain ⟨g, hg⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL (L := Lv D v) κ)
    have hK := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ g).2 ⟨κ, hg.symm⟩
    have h1 : emb D.sp.cm.sig (Jst D n) v g ∈ KAt D n v :=
      Subgroup.mem_inf.2 ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hK, by rw [← range_emb]; exact ⟨g, rfl⟩⟩
    refine ⟨⟨_, h1⟩, hinj ?_⟩
    rw [← hρ', proj_emb_self, hg]
  · intro ϖ hϖ
    have hU := isOpen_ideal D v ϖ hϖ.ne_zero
    set U := {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} with hUdef
    have hs : ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v))) =
        ⋂ i : Ix n, ⋂ j : Ix n, (fun k : KAt D n v =>
          (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j - (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j) ⁻¹' U := by
      ext k
      have he : ∀ i j, (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j -
          (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
          algebraMap (Ov D v) (Lv D v) ((ρ k).1 i j - (1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
        intro i j
        have h1 : (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
            algebraMap (Ov D v) (Lv D v) ((1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
          by_cases h : i = j
          · subst h
            rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
          · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
        rw [hρ', map_sub, h1]
        rfl
      simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, mem_level_square_congruence_iff, he, hUdef, Set.mem_setOf_eq]
      constructor
      · exact fun h i j => ⟨_, h i j, rfl⟩
      · intro h i j
        obtain ⟨y, hy, e⟩ := h i j
        have hA : Function.Injective (algebraMap (Ov D v) (Lv D v)) := Subtype.val_injective
        have e' := hA e
        rw [← e']
        exact hy
    rw [hs]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_)
    exact (continuous_entry D n v τ i j).sub continuous_const

end GlobalTheory.CompanionTheory.Jp.RhoSplit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompactStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_reduction_maximal_compact : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v), (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧ Function.Surjective ρ ∧ ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho | exact GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGeneric
namespace GlobalTheory.CompanionTheory.Jp

theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGenericStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_residue_le_rank_generic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L] [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O), (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | exact GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | (intros; apply GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLattice
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.DualInt

private theorem trace_single_one_mul {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R)
    (T : Matrix (Fin n) (Fin n) R) : (Matrix.single j i c * T).trace = c * T i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem mem_of_dual_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  intro D ψ v hψ n T hT i j
  by_contra hx
  set O := v.adicCompletionIntegers D.host.F with hO
  have hx0 : T i j ≠ 0 := by
    intro h
    exact hx (h ▸ O.zero_mem)
  have hy : (T i j)⁻¹ ∈ O := (O.mem_or_inv_mem (T i j)).resolve_left hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : v.adicCompletion D.host.F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hw : (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) ∈ O := by
    rcases O.mem_or_inv_mem ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)) with h | h
    · exact h
    · have h' : (ϖ : v.adicCompletion D.host.F) / (T i j)⁻¹ ∈ O := by
        simpa [inv_div] using h
      have hfac : ϖ = (⟨(T i j)⁻¹, hy⟩ : O) * ⟨_, h'⟩ := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        field_simp
      rcases hϖ.isUnit_or_isUnit hfac with hu | hu
      · exfalso
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = T i j := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          field_simp at h1
          simpa using h1
        exact heq ▸ hmem
      · obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          simp only at h1
          rw [eq_div_iff hϖ0]
          rw [div_inv_eq_mul, ← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        exact heq ▸ hmem
  obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
  have hb2 : (b : v.adicCompletion D.host.F) ∈ O := b.2
  apply hb
  have hX := hT (Matrix.single j i ((b : v.adicCompletion D.host.F) * ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)))) (by
    intro k l
    rw [Matrix.single_apply]
    split_ifs
    · exact mul_mem hb2 hw
    · exact O.zero_mem)
  rw [trace_single_one_mul] at hX
  convert hX using 2
  field_simp

end GlobalTheory.CompanionTheory.Jp.DualInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLatticeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_character_trivial_on_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  first | exact @GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | exact GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | (intros; apply GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem block_unipotent_map {A B : Type} {m : ℕ} [Zero A] [One A] [Zero B] [One B] [DecidableEq (Fin m)] (f : A → B) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (x : Matrix (Fin m) (Fin m) A) :
    (blk4 (1 : Matrix (Fin m) (Fin m) A) x 0 1).map f = blk4 1 (x.map f) 0 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite f, f0, f1]

theorem splitHom_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      blk4 1 (tauC τ x.1) 0 1 := by
  have e1 := GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [GlobalTheory.LocIntw.matR_adele, h x] at e1
  have e2 : (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
        (proj D.sp.cm.sig (Jst D n) v (nb x))).map (splitProj τ) := rfl
  have e3 : (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
      (proj D.sp.cm.sig (Jst D n) v (nb x))) = (blk4 1 x.1 0 1).map (cv D v) := e1
  rw [e2, e3, block_unipotent_map _ (map_zero _) (map_one _), block_unipotent_map _ (map_zero _) (map_one _)]
  rfl

theorem thU_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  have e := splitHom_proj_nMap D n nb h v τ x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e' : (thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 i j =
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1
        (finSumFinEquiv i) (finSumFinEquiv j) := rfl
  rw [e', e]
  change (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _)
    (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j)) =
      (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _) i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElementStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_image_of_unipotent_element : ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n), thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | exact GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_proj_nMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatrices
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatrices
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem coY_sum_mul_eq_zero : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 →
    ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β →
      ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  intro k _ _ n ψ₀ hψ β T hne
  classical
  let χ : AddChar (Matrix (Fin n) (Fin n) k) ℂ :=
    { toFun := fun Y => ψ₀ (Matrix.trace (Y * (T - β)))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun X Y => by
        rw [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul] }
  have hχ : χ ≠ 1 := by
    have hA : T - β ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i, j, hij⟩ : ∃ i j, (T - β) i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hA (Matrix.ext h)
    obtain ⟨a, ha⟩ := (AddChar.ne_one_iff).1 hψ
    refine (AddChar.ne_one_iff).2 ⟨Matrix.single j i (a / (T - β) i j), ?_⟩
    have htr : Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β)) = a := by
      rw [Matrix.trace_single_mul]
      exact div_mul_cancel₀ a hij
    change ψ₀ (Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β))) ≠ 1
    rw [htr]
    exact ha
  have hterm : ∀ Y : Matrix (Fin n) (Fin n) k,
      coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * χ Y := by
    intro Y
    have hχY : χ Y = ψ₀ (Matrix.trace (Y * (T - β))) := rfl
    rw [coY, hχY, ← AddChar.map_neg_eq_conj, mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub,
      Matrix.trace_sub]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun Y _ => hterm Y), ← Finset.mul_sum, AddChar.sum_eq_zero_of_ne_one hχ, mul_zero]

end GlobalTheory.CompanionTheory.Jp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatricesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_character_orthogonality_matrices : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β → ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | exact GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductor
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.ResChar

theorem local_component_additive_character_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have h1 : singleV F v (r + s) = singleV F v r + singleV F v s := by
    classical
    unfold singleV
    first
    | exact Subtype.ext (Pi.single_add v r s)
    | (apply Subtype.ext
       exact Pi.single_add v r s)
    | (apply Subtype.ext
       funext w
       show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
       rw [Pi.single_add]
       rfl)
  have h2 : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [h1]
    show ((0 : Ainf F), singleV F v r + singleV F v s) = ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  simp only [psiV]
  rw [h2, AddChar.map_add_eq_mul]

theorem dvd_of_nonunit {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {p x : R}
    (hp : Irreducible p) (hx : ¬ IsUnit x) : p ∣ x := by
  rcases ValuationRing.dvd_total p x with h | ⟨c, hc⟩
  · exact h
  · rcases hp.isUnit_or_isUnit hc with h | h
    · exact absurd h hx
    · exact ⟨↑h.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  intro D ψ v hψ ϖ hϖ w hw
  classical
  set f : Ov D v → ℂ := fun c => psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) with hf
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, map_add (f := _), mul_add]
    exact local_component_additive_character_add ψ v _ _
  have hker : ∀ d, f (ϖ * d) = 1 := by
    intro d
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (ϖ * d) = algebraMap (Ov D v) (Lv D v) d := by
      rw [map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hf, e]
    exact hψ.1 _ d.2
  have hwd : ∀ a b, IsLocalRing.residue (Ov D v) a = IsLocalRing.residue (Ov D v) b → f a = f b := by
    intro a b h
    have h0 : IsLocalRing.residue (Ov D v) (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨d, hd⟩ := dvd_of_nonunit hϖ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
    have e : a = b + ϖ * d := by rw [← hd]; ring
    rw [e, hadd, hker, mul_one]
  have hf0 : f 0 = 1 := by simpa using hker 0
  let g : kv D v → Ov D v := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have hg : ∀ z, IsLocalRing.residue (Ov D v) (g z) = z := fun z =>
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let ψ₀ : AddChar (kv D v) ℂ :=
    { toFun := fun z => f (g z)
      map_zero_eq_one' := by
        show f (g 0) = 1
        rw [hwd (g 0) 0 (by rw [hg, map_zero]), hf0]
      map_add_eq_mul' := by
        intro z z'
        show f (g (z + z')) = f (g z) * f (g z')
        rw [← hadd]
        exact hwd _ _ (by rw [hg, map_add (f := _), hg, hg]) }
  have hψ₀ : ∀ c, ψ₀ (IsLocalRing.residue (Ov D v) c) = f c := fun c => by
    show f (g _) = f c
    exact hwd _ _ (hg _)
  refine ⟨ψ₀, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
    intro h1
    apply hb
    have e1 : ψ₀ (IsLocalRing.residue (Ov D v) b) = 1 := by rw [h1]; exact AddChar.one_apply _
    rw [hψ₀] at e1
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) b = (b : Fv D.host.F v) / (ϖ : Fv D.host.F v) := by
      rw [Units.val_inv_eq_inv_val, hw, div_eq_inv_mul]; rfl
    rw [← e]
    exact e1
  · intro c
    exact (hψ₀ c).symm

end GlobalTheory.CompanionTheory.Jp.ResChar

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_character_of_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.ResChar.main | exact GlobalTheory.CompanionTheory.Jp.ResChar.main | (intros; apply GlobalTheory.CompanionTheory.Jp.ResChar.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocal
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.UpTri

theorem transpose_block_matrix {A : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.StdUnn.blk4 a b c d)ᵀ = GlobalTheory.StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  ext i j
  simp only [GlobalTheory.StdUnn.blk4, Matrix.transpose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blocks_of_unitary {K : Type} [CommRing K] {n : ℕ} (a : GL (Fin n) K) (b d a' b' c' d' : Matrix (Fin n) (Fin n) K)
    (h : (GlobalTheory.StdUnn.blk4 a' b' c' d')ᵀ * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 a.1 b 0 d =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0) : c' = 0 ∧ a'ᵀ * d = 1 := by
  rw [transpose_block_matrix, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  have e1 : c'ᵀ * a.1 = 0 := by simpa using h1
  have e2 : c'ᵀ = 0 := by
    have := congrArg (· * (a⁻¹).1) e1
    simpa [Matrix.mul_assoc, -Matrix.coe_units_inv] using this
  have e3 : c' = 0 := by simpa using congrArg Matrix.transpose e2
  subst e3
  exact ⟨rfl, by simpa using h2⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem upperParabolic_height_of_split (h : IsCMExt F E σ) (hQ : Q = GlobalTheory.StdUnn.blk4 0 1 (-1) 0) (τ : E →ₐ[F] Fv F v)
    (y : GLoc σ Q v) (a d : GL (Fin n) (Fv F v)) (b : Matrix (Fin n) (Fin n) (Fv F v))
    (hy : (splitHom σ Q τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1) :
    ∃ hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q,
      absEv F E v (GlobalTheory.LocIntw.aUp (Fv F v) σ Q ⟨y, hm⟩) = ‖a.1.det‖₊ / ‖d.1.det‖₊ := by
  obtain ⟨A, B, C, D', e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR (Fv F v) σ y)
  have key : ∀ ρ : E →ₐ[F] Fv F v, (splitHom σ Q ρ y).1 =
      GlobalTheory.StdUnn.blk4 (A.map (splitProj ρ)) (B.map (splitProj ρ)) (C.map (splitProj ρ)) (D'.map (splitProj ρ)) := by
    intro ρ
    rw [splitHom_val]
    change (GlobalTheory.LocIntw.matR (Fv F v) σ y).map (splitProj ρ : Fv F v ⊗[F] E →+* Fv F v) = _
    rw [e]
    exact GlobalTheory.LocIntw.blockMatrix_map _ _ _ _ _
  obtain ⟨ha, -, hc, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective ((key τ).symm.trans hy)
  have hQτ : Q.map τ = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    subst hQ
    have := GlobalTheory.LocIntw.blockMatrix_map (τ : E →+* Fv F v) (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have u := splitHom_unitary τ y
  rw [key (τ.comp σ), hQτ, hy] at u
  obtain ⟨hc', hd'⟩ := blocks_of_unitary a b d.1 _ _ _ _ u
  have hC : C = 0 := splitMat_ext h τ
    (by rw [hc]; exact (Matrix.map_zero _ (map_zero _)).symm)
    (by rw [hc']; exact (Matrix.map_zero _ (map_zero _)).symm)
  have hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q := (GlobalTheory.LocIntw.mem_siegelParabolic_iff_lowerLeft_eq_zero hQ).2 fun i j => by
    rw [e, hC, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp
  refine ⟨hm, ?_⟩
  have hA : GlobalTheory.StdUnn.blkA (GlobalTheory.LocIntw.matR (Fv F v) σ y) = A := by rw [e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  have d1 : splitProj τ A.det = a.1.det := by
    rw [← ha]
    exact RingHom.map_det (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) A
  have d2 : splitProj (τ.comp σ) A.det * d.1.det = 1 := by
    have : splitProj (τ.comp σ) A.det = (A.map (splitProj (τ.comp σ))).det :=
      RingHom.map_det (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v) A
    rw [this, ← Matrix.det_transpose, ← Matrix.det_mul, hd', Matrix.det_one]
  rw [absEv_apply, GlobalTheory.LocIntw.coe_aUp, hA, GlobalTheory.SplitInterDet.norm_eq_split h τ, nnnorm_mul, d1,
    eq_inv_of_mul_eq_one_left d2, nnnorm_inv, div_eq_mul_inv]

end General

theorem upperParabolic_height (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v))
    (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (H : thU D n v τ y = pM a d b) :
    ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n),
      absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) =
        nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  have hy : (splitHom D.sp.cm.sig (Jst D n) τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1 := by
    have e : ((splitHom D.sp.cm.sig (Jst D n) τ y).1).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks a.1 b 0 d.1 := congrArg Units.val H
    rw [GlobalTheory.StdUnn.blk4, ← e]
    ext i j
    simp
  exact upperParabolic_height_of_split (isCMExt_host D) (GlobalTheory.LocIntw.Jst_eq D n) τ y a d b hy

end GlobalTheory.CompanionTheory.Jp.UpTri

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocalStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_upper_parabolic_local : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v)) (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)), thU D n v τ y = pM a d b → ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n), absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) = nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | exact GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | (intros; apply GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem hU_thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    hU D n v τ (thU D n v τ g) = GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
      (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) g := by
  unfold hU
  rw [Function.leftInverse_invFun (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).1 g]

theorem hU_isHgt (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsHgt (O := Ov D v) (nvL D v) (hU D n v τ) := by
  intro a d b κ
  obtain ⟨y, hy⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (pM a d b)
  obtain ⟨k, hk⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL κ)
  have hkK : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ k).2 ⟨κ, hk.symm⟩
  obtain ⟨hyP, hab⟩ := GlobalTheory.T.modulus_upper_parabolic_local D n v τ y a d b hy
  rw [← hy, ← hk, ← map_mul, hU_thU]
  exact (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) ⟨y, hyP⟩ hkK).trans hab

theorem rank_beta0 {k : Type} [Field k] {n r t : ℕ} (h : r + t = n) :
    (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : k) else 0).rank = r := by
  classical
  rw [Matrix.rank_diagonal]
  have hr : r ≤ n := by omega
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

theorem psiV_lift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) (w : (Lv D v)ˣ) (ψ₀ : AddChar (kv D v) ℂ)
    (h : ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) =
      ψ₀ (IsLocalRing.residue (Ov D v) c))
    (ℓ : kv D v → Ov D v) (hℓ : ∀ a, IsLocalRing.residue (Ov D v) (ℓ a) = a) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (kv D v)) (T₀ : Matrix (Fin n) (Fin n) (Ov D v)) :
    psiV D.host.F ψ v (Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))) =
      ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
  have key : Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))
      = ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have key2 : Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v))) =
      IsLocalRing.residue (Ov D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, hℓ]
  rw [key, h, key2]

theorem split_place_rank_cut_of_local_computation : JpCondition → SplitPlaceRankCutEigenvalue := by
  intro hA D n r t hrt hr ψ hψ nb hnb v hgood τ
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov D v)
  have hϖ0 : algebraMap (Ov D v) (Lv D v) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Ov D v) (Lv D v))]
    exact hϖ.ne_zero
  obtain ⟨w, hw⟩ : ∃ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ := ⟨Units.mk0 _ hϖ0, rfl⟩
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := GlobalTheory.T.exists_residue_character_of_conductor D ψ v hgood ϖ hϖ w hw
  have hok := GlobalTheory.T.normalized_valuation_uniformizer D v ϖ hϖ w hw
  choose ℓ hℓ using fun a : kv D v => IsLocalRing.residue_surjective (R := Ov D v) a
  have hβ : (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0).rank = r := rank_beta0 hrt
  obtain ⟨ρ, hρ, hρs, hρm⟩ := GlobalTheory.T.surjective_reduction_maximal_compact D n v τ
  obtain ⟨c, hcd, hct, hcint⟩ := hA (Ov D v) (Lv D v) n r t hrt hr ψ₀ hψ₀ _ hβ
  choose f hinf hoff hfX _ using fun Y : Matrix (Fin n) (Fin n) (kv D v) =>
    GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ (((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y)
  have hfinj : Function.Injective f := by
    intro Y Y' hYY
    have h1 : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y =
        ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y' := by
      rw [← hfX Y, ← hfX Y', hYY]
    funext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply] at h2
    have h3 := IsFractionRing.injective (Ov D v) (Lv D v) (mul_left_cancel₀ (Units.ne_zero _) h2)
    rw [← hℓ (Y i j), ← hℓ (Y' i j), h3]
  have hsinf : ∀ x ∈ Finset.univ.image f, ∀ (w' : NumberField.InfinitePlace D.host.F) (i j : Fin n),
      (GlobalTheory.AdelicU.compInf D.host.F D.host.E w') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinf Y
  have hsoff : ∀ x ∈ Finset.univ.image f, ∀ (v' : Pl D), v' ≠ v → ∀ (i j : Fin n),
      (PositivityTheory.Rg.Rsw.L.cv D v') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hoff Y
  refine ⟨⟨Finset.univ.image f, fun x => coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
    (Function.invFun f x), hsinf, hsoff⟩, c, ?_, hcd, hct, ?_⟩
  · intro β' hβ' hint
    have hTint : ∀ i j, (β'.1.map τ) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v := by
      apply GlobalTheory.T.integral_of_character_trivial_on_lattice D ψ v hgood n
      intro X hX
      obtain ⟨x, hinf', hoff', htx, hint'⟩ := GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ X
      rw [← htx, ← GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ x hinf' hoff' β']
      apply hint
      unfold PositivityTheory.Rg.Rsw.L.IntAt
      exact ⟨hinf', hoff', hint' hX⟩
    let T₀ : Matrix (Fin n) (Fin n) (Ov D v) := fun i j => ⟨(β'.1.map τ) i j, hTint i j⟩
    have hT : (β'.1.map τ : Matrix (Fin n) (Fin n) (Lv D v)) = T₀.map (algebraMap (Ov D v) (Lv D v)) := rfl
    have hne : T₀.map (IsLocalRing.residue (Ov D v)) ≠
        Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0 := by
      intro heq
      have h1 := GlobalTheory.T.rank_residue_le_rank_generic (Ov D v) (Lv D v) n T₀
      have h2 := GlobalTheory.Core.Rk.rank_map_field (τ : D.host.E →+* Fv D.host.F v) β'.1
      rw [heq, hβ] at h1
      have h3 : (T₀.map (algebraMap (Ov D v) (Lv D v))).rank = (β'.1.map τ).rank := by rw [← hT]
      exact absurd (h1.trans (h3.trans h2).le) (not_le.2 hβ')
    have hpch : ∀ Y, PositivityTheory.Rg.Rsw.L.pch ψ (f Y).1 (GlobalTheory.MixModel.rat β'.1) =
        ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
      intro Y
      rw [GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ (f Y) (hinf Y) (hoff Y) β', hfX Y, hT]
      exact psiV_lift D ψ v w ψ₀ hψ₀c ℓ hℓ Y T₀
    show ∑ x ∈ Finset.univ.image f, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
      (Function.invFun f x) * PositivityTheory.Rg.Rsw.L.pch ψ x.1 (GlobalTheory.MixModel.rat β'.1) = 0
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    calc _ = ∑ Y, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0) Y *
          ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Function.leftInverse_invFun hfinj Y, hpch Y]
      _ = 0 := GlobalTheory.T.sum_character_orthogonality_matrices (kv D v) n ψ₀ hψ₀ _ _ hne
  · intro νv hH hP z
    have e1 : ∀ g, GlobalTheory.CompanionTheory.Jp.sphV D n v z g =
        GlobalTheory.Doubling.npow (hU D n v τ (thU D n v τ g)) (z + (n : ℂ) / 2) := by
      intro g
      rw [hU_thU]
      rfl
    rw [← hcint ϖ hϖ w hw ℓ hℓ (nvL D v) hok (hU D n v τ) (hU_isHgt D n v τ) _ νv ρ hρs (hρm ϖ hϖ) z]
    dsimp only
    congr 1
    funext k
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Function.leftInverse_invFun hfinj Y, e1, map_mul, map_mul, hρ k, GlobalTheory.T.local_image_of_unipotent_element D n nb hnb v τ (f Y), hfX Y]
    rfl

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternativeStatement
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_rank_cut_of_alternative : GlobalTheory.CompanionTheory.Jp.JpCondition → GlobalTheory.CompanionTheory.Jp.SplitPlaceRankCutEigenvalue := by
  first | exact @GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | exact GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | (intros; apply GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation <;> assumption)
end
