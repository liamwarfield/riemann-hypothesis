module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelA
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIkSch
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIkSch

theorem isCompact_K {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    IsCompact (l.K : Set (GA D T)) := by
  exact (GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c (fun v hv => GlobalTheory.Core.Rk.IP.Model.isSplit_two v hv) hl.2.2) l hl).2.1

end PositivityTheory.Rg.Rsw.L.LIkSch

namespace PositivityTheory.Rg.Rsw.L

theorem ikSch : IkSch := by
  intro D n t B W d I θ hθ Φ hΦ
  have hK : IsCompact (I.l.K : Set (GA D B)) := LIkSch.isCompact_K d I.good
  have h1 := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK Φ hΦ
  refine ⟨h1, ?_⟩
  obtain ⟨𝓕, h𝓕⟩ := I.cov₁
  exact GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz D θ hθ B W t n d I.μ₁ 𝓕 h𝓕 _ h1

end PositivityTheory.Rg.Rsw.L
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFourierPt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFourierPt

variable {D : D7} {n : ℕ}

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : Matrix (Fin n) (Fin n) D.host.E)
    (x : Mx D n n) : conj (pch ψ x (rat a)) = ψ (-GlobalTheory.CompanionTheory.FourierN.pr a x) := by
  have e : pch ψ x (rat a) = ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) := by
    rw [pch, GlobalTheory.CompanionTheory.FourierN.pr]
    congr 2
    exact Matrix.trace_mul_comm _ _
  rw [e, AddChar.map_neg_eq_inv]
  have hn : ‖ψ (GlobalTheory.CompanionTheory.FourierN.pr a x)‖ = 1 := hψ.2.1 _
  have hne : ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

end PositivityTheory.Rg.Rsw.L.LFourierPt

namespace PositivityTheory.Rg.Rsw.L

open LFourierPt

set_option synthInstance.maxHeartbeats 400000 in
theorem fourierPt : FourierPt := by
  intro D n ψ hψ lam 𝓖 hC f hf hper hco
  obtain ⟨hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) :=
    GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (hermA D n) (ratHerm D n) K hK hcov
    (GlobalTheory.CompanionTheory.FourierN.hermSub D n) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
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
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩),
      fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lam 𝓖 hlam hFD f hf hper
    (fun a => by
      have h := hco ⟨a.1, a.2⟩
      refine (integral_congr_ae (.of_forall fun x => ?_)).trans h
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1) * f x = f x * conj (pch ψ x.1 (rat a.1))
      rw [conj_pch hψ, mul_comm])

end PositivityTheory.Rg.Rsw.L

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MatGExt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L


open UnitaryGroupMatrix in
theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelC
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set GlobalTheory.Eis GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

variable {D : D7} {n : ℕ}

theorem law_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  simp only [fam]
  rw [hH.2.2 q hq a ha g, h q hq a ha g, npow_mul]
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add (hom_pos _ _)]; congr 1; ring
  rw [e]; ring

theorem cont_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  simp only [fam, npow_eq_exp (hH.2.1 _)]
  have h1 : Continuous fun u : ℂ × G D n => Real.log (H u.2 : ℝ) :=
    (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)).log fun u => (NNReal.coe_pos.2 (hH.2.1 _)).ne'
  exact (((Complex.continuous_ofReal.comp h1).mul (continuous_fst.sub continuous_const)).cexp).mul
    (hφ.comp continuous_snd)

def cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : Set (G D n) :=
  ⋃ x ∈ C.s, (fun k => g * k * nb x) '' (K D n : Set (G D n))

theorem isCompact_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : IsCompact (cset nb C g) :=
  C.s.isCompact_biUnion fun _ _ => isCompact_K.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) (u : KAt D n v) {x : hermA D n}
    (hx : x ∈ C.s) : g * (u : G D n) * nb x ∈ cset nb C g :=
  mem_biUnion hx ⟨u, (Subgroup.mem_inf.1 u.2).1, rfl⟩

theorem farRight {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g)
    {z : ℂ} (hz : (n : ℝ) / 2 < z.re) (g : G D n) :
    ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv = c z * eisS (fam H φ s₀ z) g := by
  have := t2Space_adeleRing' (F := D.host.F)
  have hcont := cont_fam hH hφc s₀
  have hz' : Continuous (fam H φ s₀ z) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w, hw, hwb⟩ := exists_majorant (P := P D n) (Γ := GF D n) (χ := χ.comp detP) (ρ := (n : ℝ) / 2)
    (σ := (n : ℝ) / 2) (Φ := fam H φ s₀) isIwasawa isCompact_K hcont.continuousOn
    (fun s _ q g => by
      have := law_fam hH hφl s q q.2 (leviBlock (D := D) (n := n) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ hτ) isCompact_singleton (singleton_subset_iff.2 hz) (isCompact_cset nb C g)
  have hb : ∀ q (u : KAt D n v) x, x ∈ C.s →
      ‖fam H φ s₀ z (((q.out : GF D n) : G D n) * g * u * nb x)‖ ≤ w q := fun q u x hx => by
    have := hwb q z rfl _ (mem_cset nb C g u hx)
    simpa only [term, mul_assoc] using this
  have hterm : ∀ u : KAt D n v, cutR nb C (eisS (fam H φ s₀ z)) (g * u) =
      ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) := by
    intro u
    simp only [cutR, eisS, cosetSum]
    rw [Summable.tsum_finsetSum fun x hx => (Summable.of_norm_bounded hw fun q => by
      simpa only [term, mul_assoc] using hwb q z rfl _ (mem_cset nb C g u hx)).mul_left (C.co x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_left]
    simp only [term, mul_assoc]
  calc ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv
      = ∫ u, ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        congr 1; funext u; exact hterm u
    _ = ∑' q : Cosets (P D n) (GF D n), ∫ u, cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        refine integral_tsum_dom νv _ (fun q => (∑ x ∈ C.s, ‖C.co x‖) * w q) (hw.mul_left _) (fun q u => ?_)
          fun q => ?_
        · simp only [cutR]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hb q u x hx) (norm_nonneg _)
        · refine Continuous.aestronglyMeasurable ?_
          simp only [cutR]
          exact continuous_finsetSum _ fun x _ => continuous_const.mul
            (hz'.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    _ = ∑' q : Cosets (P D n) (GF D n), c z * fam H φ s₀ z (((q.out : GF D n) : G D n) * g) := by
        congr 1; funext q; exact hrel z _
    _ = c z * eisS (fam H φ s₀ z) g := by
        rw [tsum_mul_left]; rfl

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCore
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCoreA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open PositivityTheory.Rg.Rsw.L.LResCore

theorem resCore : Polar → CfFJ → IdemEx → GoodEv → FixW → WMaj → JPos → CfRel → CfInv → CutLow → CutId → ThBdd → ThCoef →
    IkSch → IkEq → ResCore := by
  classical
  intro hPolar hCfFJ hIdem hGoodEv hFixW hWMaj hJPos hCfRel hCfInv hCutLow hCutId hThBdd hThCoef hIkSch hIkEq
    D n t B W hd hn hbig hlt hpos ψ hψ χ hχ hη θ hθ μB μW hμB hμW ωB ωW hωB hωW H hH hHlev Φ U d E σ hcont ε hrad
  obtain ⟨dd⟩ := hd
  have hBr : B.rank = n + t := by have := dd.rank_add; omega
  have hηB : ResEta D χ B.rank := GlobalTheory.HeckeCharsOfSquare.resEta_of_mod hη (by omega)
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hφlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := isLaw_sw hBr hωB Φ
  obtain ⟨-, hP2, -⟩ := hPolar D n W.rank t hn hbig ψ hψ χ hχ hη (fun h0 => absurd h0 (by omega)) θ hθ H hH _ hφc hφlaw
    U d E σ hcont ε hrad
  obtain ⟨UH, hUHo, hUH⟩ := hHlev
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) UH hUHo
  obtain ⟨S₂, hS₂⟩ := hFixW D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB
  obtain ⟨S₃, hS₃⟩ := hGoodEv D θ hθ B.rank n Φ.1 Φ.2
  obtain ⟨nb, lam, 𝓖, hnb, hlam⟩ := GlobalTheory.CompanionTheory.SWCoef.coefDataExists D n
  obtain ⟨v, hvS, C, cc, hKill, hcd, hc0, hcut⟩ := hJPos D n W.rank t hn hpos ψ hψ χ hχ hη nb hnb (S₁ ∪ S₂ ∪ S₃)
  obtain ⟨e, he⟩ := (hIdem D (S₁ ∪ S₂ ∪ S₃)).1
  have hsub2 : S₂ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hsub3 : S₃ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hv1 : v ∉ S₁ := fun h => hvS (by simp [h])
  have hgood : Good (S₁ ∪ S₂ ∪ S₃) e Φ.1 := hS₃ _ hsub3 e he
  have hKΦ : ∀ k ∈ KAt D n v, ωB k Φ = Φ := fun k hk => hS₂ _ hsub2 e he Φ hgood k (kAt_le_kOff hvS hk)
  have hKH : ∀ k ∈ KAt D n v, ∀ g, H (g * k) = H g := fun k hk g =>
    hUH k (hS₁ (kAt_le_kOff hv1 hk)) (mem_atPts.1 (Subgroup.mem_inf.1 hk).2).1 g
  have hKφ : ∀ k ∈ KAt D n v, ∀ g, (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0 := fun k hk g => by
    rw [map_mul, Module.End.mul_apply, hKΦ k hk]
  obtain ⟨νv, hνH, hνP⟩ := exists_haar_prob (KAt D n v) (isCompact_kAt v)
  have hfam : ∀ z g, ∫ k, cutR nb C (fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z) (g * k) ∂νv =
      cc z * fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z g := by
    intro z g
    refine hcut νv hνH hνP z _ (GlobalTheory.CompanionTheory.RswPolar.continuous_fam hH hφc _ z) (GlobalTheory.CompanionTheory.RswPolar.isLaw_fam hH hφlaw z) ?_ g
    intro k hk g'
    simp only [fam, hKH k hk g', hKφ k hk g']
  have hrel := hCfRel D n χ hχ H hH _ _ hφc hφlaw U d E σ hcont ε hrad nb hnb v C cc hcd νv hνP hfam
  obtain ⟨hcfCA, ⟨N, hN⟩, -⟩ := hCfFJ D n H _ _ U d E σ hcont ε hrad
  have hcfK : ∀ k, ∀ u ∈ KAt D n v, ∀ g, cf d E ((t : ℂ) / 2) ε k (g * u) = cf d E ((t : ℂ) / 2) ε k g :=
    fun k u hu g => hCfInv D n H _ _ U d E σ hcont ε hrad u (hKH u hu) (hKφ u hu) k g
  have hhigh : ∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0 := by
    have key : ∀ m k, 2 ≤ k → N < k + m → cf d E ((t : ℂ) / 2) ε k = 0 := by
      intro m
      induction m with
      | zero => intro k _ hk; exact hN k (by omega)
      | succ m ih =>
        intro k hk2 hkm
        have hj : ∀ j, k < j → cf d E ((t : ℂ) / 2) ε j = 0 := fun j hj => ih j (by omega) (by omega)
        have h1 := hrel k (by omega) hj
        have h2 := (hCutLow D n W.rank ψ hψ nb hnb v C hKill (cf d E ((t : ℂ) / 2) ε k) (hcfCA k).1 (hcfCA k).2
          (fun u hu g => hcfK k u hu g)).1 (hP2 k hk2)
        funext g
        have h3 := h1 g
        simp only [h2, Pi.zero_apply, integral_zero] at h3
        exact (mul_eq_zero.1 h3.symm).resolve_left hc0
    intro k hk
    exact key (N + 1) k hk (by omega)
  refine ⟨hhigh, ?_⟩
  intro X _ π _ cX κ hcX hcomp hκ hkill
  obtain ⟨a, ha⟩ := GlobalTheory.RegSch.exists_good_frameLat D B
  obtain ⟨νK, hνK, hνK1⟩ := exists_haar_prob _ ha.isCompact_K
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t n
  have : LocallyCompactSpace (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  let I : IkD dd n := IkD.mk _ ha νK hνK hνK1 μ₁ ⟨𝓕₁, hμ₁⟩ Measure.haar inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D W I.m I.haar
  let Ψ : schwartzA θ W.rank n := ⟨ikp I Φ.1, (hIkSch D n t B W dd I θ hθ Φ.1 Φ.2).2⟩
  let Ψ' : schwartzA θ W.rank n := ∑ x ∈ C.s, C.co x • ωW (nb x) Ψ
  have hStg : Stg dd hn ψ χ θ μB μW ωB ωW := ⟨hbig, hlt, hpos, hψ, hχ, hη, hθ, hμB, hμW, hωB, hωW⟩
  obtain ⟨κ', hκ'⟩ := hCutId D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I H hH Φ U d E σ hcont ε hrad nb hnb v C hKill
    (fun k hk => ⟨hKΦ k hk, hKH k hk⟩) 𝓕 h𝓕 Ψ Ψ' rfl rfl
  have hΨinv : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I Φ Ψ rfl k, hKΦ k hk])
  obtain ⟨hθc, -, -, hθb, -⟩ := hThBdd D n W ψ hψ χ hχ hη θ hθ μW hμW ωW hωW nb hnb v C hKill Ψ Ψ' hΨinv rfl
  have h𝓕fin : I.m 𝓕 ≠ ⊤ := (hThCoef D n W ψ hψ θ hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hlam Ψ.1 Ψ.2).1
  have : IsFiniteMeasure (I.m.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕fin
  obtain ⟨b, hb⟩ := hθb _ (hcomp.mul (isCompact_kAt (n := n) v))
  have hbound : ∀ x (p : KAt D n v × GA D W), ‖theta ωW Ψ' (cX x * p.1) p.2‖ ≤ b := fun x p =>
    hb _ (Set.mul_mem_mul (subset_closure (Set.mem_range_self x)) p.1.2) p.2
  have hmeas : Measurable (fun q : X × (KAt D n v × GA D W) => theta ωW Ψ' (cX q.1 * q.2.1) q.2.2) :=
    hθc.measurable.comp (((hcX.comp measurable_fst).mul
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  have hintx : ∀ x, Integrable (fun p : KAt D n v × GA D W => theta ωW Ψ' (cX x * p.1) p.2)
      (νv.prod (I.m.restrict 𝓕)) := fun x =>
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable b
      (ae_of_all _ (hbound x))
  have hint : Integrable (Function.uncurry fun (x : X) (p : KAt D n v × GA D W) =>
      theta ωW Ψ' (cX x * p.1) p.2 * κ x) (π.prod (νv.prod (I.m.restrict 𝓕))) := by
    refine Integrable.mono' ((hκ.norm.const_mul b).comp_fst (νv.prod (I.m.restrict 𝓕)))
      (hmeas.aestronglyMeasurable.mul hκ.aestronglyMeasurable.comp_fst) (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound q.1 q.2) (norm_nonneg _)
  have hpt : ∀ x, cf d E ((t : ℂ) / 2) ε 1 (cX x) * κ x =
      (cc ((t : ℂ) / 2))⁻¹ * κ' * ∫ p, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂(νv.prod (I.m.restrict 𝓕)) := by
    intro x
    have h1 := hrel 1 le_rfl (fun j hj => hhigh j hj) (cX x)
    simp only [hκ'] at h1
    rw [integral_const_mul] at h1
    have e2 : ∫ p, theta ωW Ψ' (cX x * p.1) p.2 ∂(νv.prod (I.m.restrict 𝓕)) =
        ∫ u, ∫ h in 𝓕, theta ωW Ψ' (cX x * u) h ∂I.m ∂νv := integral_prod _ (hintx x)
    rw [integral_mul_const, e2, (eq_inv_mul_iff_mul_eq₀ hc0).2 h1.symm]
    ring
  have hzero : ∀ p : KAt D n v × GA D W, ∫ x, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂π = 0 := by
    intro p
    simp only [theta_mul]
    exact hkill (ωW p.1 Ψ') p.2
  simp only [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  simp only [hzero, integral_zero, mul_zero]

end PositivityTheory.Rg.Rsw.L

end
end
