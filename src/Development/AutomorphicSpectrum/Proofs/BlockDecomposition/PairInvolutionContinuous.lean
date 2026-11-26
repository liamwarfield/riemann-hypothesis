module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuousStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_involution_continuous : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | exact GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtRightTranslate

theorem height_mul_le : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H →
    (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  rintro D n H hH ⟨C₀, hC₀, hcov⟩ C hC
  have hcont : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
  have hpos : ∀ g, 0 < (H g : ℝ) := fun g => by exact_mod_cast hH.2.1 g
  have hF : Continuous fun p : G D n × G D n => (H (p.1 * p.2) : ℝ) / (H p.1 : ℝ) :=
    (hcont.comp (continuous_fst.mul continuous_snd)).div (hcont.comp continuous_fst)
      fun p => (hpos p.1).ne'
  obtain ⟨M, hM⟩ := (hC₀.prod hC).bddAbove_image hF.continuousOn
  refine ⟨max M 1, le_max_right _ _, fun c hc x => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := hcov x
  have hb : (H (k * c) : ℝ) / (H k : ℝ) ≤ max M 1 :=
    (hM ⟨(k, c), ⟨hk, hc⟩, rfl⟩).trans (le_max_left _ _)
  have hb' : (H (k * c) : ℝ) ≤ max M 1 * (H k : ℝ) := (div_le_iff₀ (hpos k)).1 hb
  have hl := hH.2.2 q hq (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  rw [mul_assoc, hl (k * c), hl k]
  push_cast
  have hd : (0 : ℝ) ≤ (absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩)) : ℝ) :=
    NNReal.coe_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hb' hd]

end GlobalTheory.CompanionTheory.HtRightTranslate
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_right_translate_compact_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | exact GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | (intros; apply GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def radN : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b}
  mul_mem' := by
    rintro x y ⟨c, b, hx⟩ ⟨c', b', hy⟩
    refine ⟨c + c' + cComm W b b', b + b', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, HypDec.nC_add, HypDec.nC_add]
    calc d.nC c * d.nB b * (d.nC c' * d.nB b')
        = d.nC c * (d.nB b * d.nC c') * d.nB b' := by group
      _ = d.nC c * (d.nC c' * d.nB b) * d.nB b' := by rw [d.nC_mul_nB]
      _ = d.nC c * d.nC c' * (d.nB b * d.nB b') := by group
      _ = d.nC c * d.nC c' * (d.nB (b + b') * d.nC (cComm W b b')) := by rw [d.nB_mul_nB]
      _ = d.nC c * d.nC c' * (d.nC (cComm W b b') * d.nB (b + b')) := by rw [d.nC_mul_nB]
      _ = _ := by group
  one_mem' := ⟨0, 0, by simp [d.nC_zero, d.nB_zero]⟩
  inv_mem' := by
    rintro x ⟨c, b, hx⟩
    refine ⟨-c, -b, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, d.nB_inv, d.nC_inv, d.nC_mul_nB]

def levM : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a}
  mul_mem' := by
    rintro x y ⟨g, a, hx⟩ ⟨g', a', hy⟩
    refine ⟨g * g', a * a', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, map_mul, map_mul]
    calc d.emb0 g * d.levi a * (d.emb0 g' * d.levi a')
        = d.emb0 g * (d.levi a * d.emb0 g') * d.levi a' := by group
      _ = d.emb0 g * (d.emb0 g' * d.levi a) * d.levi a' := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group
  one_mem' := ⟨1, 1, by simp⟩
  inv_mem' := by
    rintro x ⟨g, a, hx⟩
    refine ⟨g⁻¹, a⁻¹, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, map_inv, map_inv, ← map_inv, ← map_inv, d.wittHyperbolic_anisotropic_commute_levi]

theorem mem_radN {q : GlobalTheory.RegSW.stab d} :
    q ∈ radN d ↔ ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b := Iff.rfl

theorem mem_levM {q : GlobalTheory.RegSW.stab d} :
    q ∈ levM d ↔ ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a := Iff.rfl

theorem exists_radN_mul_levM (q : GlobalTheory.RegSW.stab d) : ∃ n ∈ radN d, ∃ m ∈ levM d, q = n * m := by
  obtain ⟨b, c, g, e⟩ := GlobalTheory.GodementSectionReduction.exists_decomp d q
  refine ⟨⟨d.nC c * d.nB b, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d c) (GlobalTheory.GodementSectionReduction.nB_mem d b)⟩, ⟨c, b, rfl⟩,
    ⟨d.emb0 g * d.levi (GlobalTheory.RegSW.onX d q), mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d g) (GlobalTheory.RegSW.levi_mem d _)⟩, ⟨g, _, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, e, ← d.nC_mul_nB]
  simp only [mul_assoc]

theorem conj_coord (g : GA D W) (a : GL (Fin t) (AE D)) (c : skewA D t) (b : Mx D t W.rank) :
    (d.emb0 g * d.levi a) * (d.nC c * d.nB b) * (d.emb0 g * d.levi a)⁻¹ =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) := by
  have h : d.emb0 g * d.levi a * (d.nC c * d.nB b) =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) * (d.emb0 g * d.levi a) := by
    calc d.emb0 g * d.levi a * (d.nC c * d.nB b)
        = d.emb0 g * (d.levi a * d.nC c) * d.nB b := by group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.levi a * d.nB b) := by rw [d.levi_mul_nC]; group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.nB (a.1 ⬝ b) * d.levi a) := by rw [d.levi_mul_nB]
      _ = d.nC (skewConj a.1 c) * (d.emb0 g * d.nB (a.1 ⬝ b)) * d.levi a := by rw [d.wittHyperbolic_anisotropic_commute_nC]; group
      _ = _ := by rw [d.wittHyperbolic_anisotropic_conj_nB]; group
  rw [h, mul_inv_cancel_right]

instance radN_normal : (radN d).Normal := by
  refine ⟨fun n hn q => ?_⟩
  obtain ⟨n₁, hn₁, m, ⟨g, a, hm⟩, rfl⟩ := exists_radN_mul_levM d q
  obtain ⟨c, b, hc⟩ := hn
  have h : m * n * m⁻¹ ∈ radN d := ⟨skewConj a.1 c, a.1 ⬝ b ⬝ mt W g⁻¹, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hm, hc, conj_coord]⟩
  have e : n₁ * m * n * (n₁ * m)⁻¹ = n₁ * (m * n * m⁻¹) * n₁⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hn₁ h) (inv_mem hn₁)

end GlobalTheory.CompanionTheory.QKAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.EllLoc

theorem map_csr_left {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    (C (c (P.coeff 0)) * P).map φ = C (c' ((P.map φ).coeff 0)) * P.map φ := by
  rw [Polynomial.map_mul, Polynomial.map_C, h, Polynomial.coeff_map]

theorem map_csr_right {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    ((P.map c).reverse).map φ = ((P.map φ).map c').reverse := by
  have hcomp : φ.comp c = c'.comp φ := RingHom.ext h
  have hd : (P.map c).natDegree = ((P.map φ).map c').natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, Polynomial.natDegree_map]
  rw [Polynomial.reverse, Polynomial.reverse, ← hd, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map]

theorem csr_linear (a : ℂ) (ha : ‖a‖ = 1) :
    C (starRingEnd ℂ ((X - C a : ℂ[X]).coeff 0)) * (X - C a) = ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse := by
  have hmul : starRingEnd ℂ a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.reverse, Polynomial.natDegree_X_sub_C,
    Polynomial.reflect_sub, Polynomial.reflect_C]
  have hX : reflect 1 (X : ℂ[X]) = 1 := by
    simpa [revAt] using Polynomial.reflect_monomial (R := ℂ) 1 1
  rw [hX]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, C_neg, pow_one]
  have : (C (starRingEnd ℂ a) * C a : ℂ[X]) = 1 := by rw [← C_mul, hmul, C_1]
  linear_combination this

theorem csr_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    C (starRingEnd ℂ ((s.map fun a => (X - C a : ℂ[X])).prod.coeff 0)) * (s.map fun a => (X - C a : ℂ[X])).prod =
      ((s.map fun a => (X - C a : ℂ[X])).prod.map (starRingEnd ℂ)).reverse := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
    have h1 := csr_linear a (hs a (Multiset.mem_cons_self a s))
    have h2 := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h1, ← h2,
      Polynomial.mul_coeff_zero, map_mul, C_mul]
    ring

theorem csr_global {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  have hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQ : (P.map τ).Monic := hP.1.map τ
  have hroots : (P.map τ) = ((P.map τ).roots.map fun a => (X - C a : ℂ[X])).prod :=
    (IsAlgClosed.splits (P.map τ)).eq_prod_roots_of_monic hQ
  have key := csr_prod (P.map τ).roots (hP.2.2.2 τ)
  rw [← hroots] at key
  apply Polynomial.map_injective τ τ.injective
  have e1 := map_csr_left τ σ (starRingEnd ℂ) hτ P
  have e2 := map_csr_right τ σ (starRingEnd ℂ) hτ P
  rw [e2, ← key, ← e1]
  rfl

theorem csr_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) :
    IsCsr w (atPl w P) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hc : ∀ x, algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) =
      cj w (algebraMap E (w.adicCompletion E) x) := fun x => (GlobalTheory.BCT.LocVal.cj_algebraMap w hs x).symm
  have e1 := map_csr_left (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  have e2 := map_csr_right (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  rw [atPl, ← e1, ← e2, ← csr_global hP]
  rfl

theorem ellLocal : EllLocal := by
  intro E _ _ _ a b p₁ p₂ h₁ h₂ hc w
  have hm₁ : (atPl w p₁).Monic := h₁.1.map _
  have hm₂ : (atPl w p₂).Monic := h₂.1.map _
  refine ⟨hm₁, hm₂, ?_, ?_, ?_, csr_at h₁ w, csr_at h₂ w⟩
  · rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  · rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  · have hs : (p₁ * p₂).Separable := h₁.2.2.1.mul h₂.2.2.1 hc
    have := hs.map (f := algebraMap E (w.adicCompletion E))
    rwa [Polynomial.map_mul] at this

end GlobalTheory.CompanionTheory.EllLoc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentityStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_local_identity : EllLocal := by
  first | exact @GlobalTheory.CompanionTheory.EllLoc.ellLocal | exact GlobalTheory.CompanionTheory.EllLoc.ellLocal | (intros; apply GlobalTheory.CompanionTheory.EllLoc.ellLocal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens} (h : W' ≤ W)
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    Semi.res h (blockUnit i j h') = blockUnit i j (h.trans h') :=
  DVR.res_res' _ _ _

def mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) :
    Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ :=
  Semi.res (inf_le_inf_right _ inf_le_left) u * Semi.res (inf_le_inf_right _ inf_le_right) v

theorem ev_mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C)) :
    CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C) (mulUnit u v : Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ C) (u : Γ(MP ℤ m n, P ⊓ C)) y *
        CxPts.ev (mpStr ℤ m n) σ₀ (Q ⊓ C) (v : Γ(MP ℤ m n, Q ⊓ C)) y := by
  rw [mulUnit, Units.val_mul, CxPts.ev_mul]
  exact congrArg₂ (· * ·) (CxPts.ev_res _ hy _) (CxPts.ev_res _ hy _)

theorem frame_mulUnit {P P' Q Q' C : (MP ℤ m n).Opens} (g : Γ(MP ℤ m n, P ⊓ P')ˣ) (g' : Γ(MP ℤ m n, Q ⊓ Q')ˣ)
    (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (u' : Γ(MP ℤ m n, P' ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) (v' : Γ(MP ℤ m n, Q' ⊓ C)ˣ)
    (a₁ : P ⊓ P' ⊓ C ≤ P' ⊓ C) (a₂ : P ⊓ P' ⊓ C ≤ P ⊓ P') (a₃ : P ⊓ P' ⊓ C ≤ P ⊓ C)
    (b₁ : Q ⊓ Q' ⊓ C ≤ Q' ⊓ C) (b₂ : Q ⊓ Q' ⊓ C ≤ Q ⊓ Q') (b₃ : Q ⊓ Q' ⊓ C ≤ Q ⊓ C)
    (hu : Semi.res a₁ u' = Semi.res a₂ g * Semi.res a₃ u) (hv : Semi.res b₁ v' = Semi.res b₂ g' * Semi.res b₃ v)
    (d₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P' ⊓ Q' ⊓ C) (d₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ (P' ⊓ Q'))
    (d₃ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ C) (f₁ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ P ⊓ P') (f₂ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ Q ⊓ Q') :
    Semi.res d₁ (mulUnit u' v') = Semi.res d₂ (Semi.res f₁ g * Semi.res f₂ g') * Semi.res d₃ (mulUnit u v) := by
  have l₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ P' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_left inf_le_left)
  have l₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ Q ⊓ Q' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_right inf_le_right)
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  exact (congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)

theorem mono_mulUnit {P Q : (MP ℤ m n).Opens} {c c' : ∀ k, Bk n k} (a b : Fin (m + 1) → ℤ)
    (u : Γ(MP ℤ m n, P ⊓ mchart c)ˣ) (u' : Γ(MP ℤ m n, P ⊓ mchart c')ˣ)
    (v : Γ(MP ℤ m n, Q ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, Q ⊓ mchart c')ˣ)
    (a₁ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c) (a₂ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c')
    (b₁ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c) (b₂ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c')
    (ta : ∀ k, P ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (tb : ∀ k, Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hu : Semi.res a₁ u = Semi.res a₂ u' * ∏ k, blockUnit (c k) (c' k) (ta k) ^ a k)
    (hv : Semi.res b₁ v = Semi.res b₂ v' * ∏ k, blockUnit (c k) (c' k) (tb k) ^ b k)
    (d₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c) (d₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c')
    (td : ∀ k, P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) :
    Semi.res d₁ (mulUnit u v) = Semi.res d₂ (mulUnit u' v') * ∏ k, blockUnit (c k) (c' k) (td k) ^ (a k + b k) := by
  have l₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_left
  have l₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_right
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, map_prod, map_zpow, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  refine ((congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)).trans (congrArg (HMul.hMul _) ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [res_blockUnit, res_blockUnit, ← zpow_add]

end GlobalTheory.CompanionTheory.MPDict.TensRep

namespace GlobalTheory.CompanionTheory.MPDict

open TensRep

theorem isHermRep_tens : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M N : HermLB (mpStr ℤ m n)) (A B : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep N B → IsHermRep (M.tens N) (A.tensor B) := by
  rintro m n M N A B ⟨u, hu₁, hu₂, hu₃⟩ ⟨v, hv₁, hv₂, hv₃⟩
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit A.a B.a _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _
  · rintro ⟨i, i'⟩ c y z hz hy
    have hy' := mem_ptsIn_inf.1 hy
    have h₁ := mem_ptsIn_inf.1 hy'.1
    have e₁ := hu₃ i c y z hz (mem_ptsIn_inf.2 ⟨h₁.1, hy'.2⟩)
    have e₂ := hv₃ i' c y z hz (mem_ptsIn_inf.2 ⟨h₁.2, hy'.2⟩)
    have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (ptsIn_mono (mchart_le c k) hy'.2)
    have hp : ∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k) =
        (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ B.a k := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => zpow_add₀ (norm_ne_zero_iff.2 (hz0 k)) _ _
    have hev := ev_mulUnit (u i c) (v i' c) hy
    change A.h z * B.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ N.B.U i' ⊓ mchart c)
        (mulUnit (u i c) (v i' c) : Γ(MP ℤ m n, M.B.U i ⊓ N.B.U i' ⊓ mchart c)ˣ) y‖ *
      Real.exp (((M.φ σ₀).φ i y + (N.φ σ₀).φ i' y) / 2)
    rw [e₁, e₂, hev, hp, norm_mul, add_div, Real.exp_add]
    ring

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicity
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem length_decWord (Γ : Segment k) : (decWord Γ).length = Γ.len := by
  simp [decWord]

theorem decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) :
    (decWord Γ).get a = Γ.first.nu ((Γ.len - 1 - (a : ℕ) : ℕ) : ℂ) := by
  have h : (a : ℕ) < (List.ofFn Γ.term).reverse.length := a.2
  show (List.ofFn Γ.term).reverse[(a : ℕ)] = _
  rw [List.getElem_reverse, List.getElem_ofFn]
  simp [Segment.term]

theorem isCusp_decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) : ((decWord Γ).get a).IsCusp := by
  rw [decWord_get]
  exact Γ.isCusp_first.nu _

theorem sum_decWord (Γ : Segment k) : ∑ a, ((decWord Γ).get a).1 = Γ.deg := by
  have h : ∀ a, ((decWord Γ).get a).1 = Γ.d := fun a => by rw [decWord_get]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]
  rfl

theorem below_of_len_one {s : ℕ} (Γ : Fin s → Segment k) (h : ∀ a, (Γ a).len = 1) (a : Fin s) :
    below Γ a = s - 1 - (a : ℕ) := by
  simp only [below, h, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

theorem jmL_decWord (hJ : LSegJacquet k) (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hΓ : IsLSeg Γ π) : jmL (decWord Γ) π = 1 := by
  have hd : ∑ a, ((decWord Γ).get a).1 = N := (sum_decWord Γ).trans hΓ.deg_eq
  rw [jmL, dite_eq_left hd]
  refine (hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1
    ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩,
      fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩
  · have h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1 := fun _ => rfl
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]
  · refine (decWord_get Γ a).trans ?_
    have e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ) := by
      have := length_decWord Γ
      omega
    rw [below_of_len_one _ (fun _ => rfl), e]

theorem len_eq_one (hJ : LSegJacquet k) {Δ : Segment k} {x : IrrGL (k := k)} (hx : x.IsCusp) (h : IsLSeg Δ x.rep) :
    Δ.len = 1 := by
  have hd : ∑ a, ((decWord Δ).get a).1 = x.1 := (sum_decWord Δ).trans h.deg_eq
  have h1 := jmL_decWord hJ Δ h
  rw [jmL, dite_eq_left hd, jm] at h1
  have hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep) :=
    jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hu := GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _
    (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub
  by_contra hne
  have hl : 2 ≤ (decWord Δ).length := by
    have := Δ.len_pos
    rw [length_decWord]
    omega
  have := hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1
  simp at this

theorem eq_of_isLSeg_single {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) {x : IrrGL (k := k)} (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  have hdeg : ρ.1 = x.1 := by
    have := h.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  obtain rfl : m = n := hdeg
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique h
  exact (IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))

theorem eq_first_of_len_one {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  exact eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)

theorem jmL_cusp_word : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) →
    (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  intro k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW
  refine ⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩
  by_cases hd : ∑ a, (W.get a).1 = N
  · rw [jmL, dite_eq_left hd]
    refine (hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_
    rintro ⟨Γ', ⟨hs, hf⟩, hL⟩
    have hl : ∀ a, (Γ' a).len = 1 := fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)
    have hlen : W.length = Γ.len := by
      simpa only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs
    refine hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)
    have h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ) := by
      have h4 := eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)
      rw [hf, below_of_len_one Γ' hl] at h4
      exact h4
    rw [h3, decWord_get, hlen]
  · rw [jmL, dite_eq_right hd]

end GlobalTheory.CompanionTheory.FineL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_jacquet_word_multiplicity : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FineL.jmL_cusp_word | exact GlobalTheory.CompanionTheory.FineL.jmL_cusp_word | (intros; apply GlobalTheory.CompanionTheory.FineL.jmL_cusp_word <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagCoset

theorem v_eq_of_ne {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0]
  simp

theorem diagT_mem_iwGL {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (τ : Fin n → (w.adicCompletion E)ˣ) (hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ ∈ iwGL n w := by
  have hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1 := by
    intro i
    have : (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹ := by
      simp
    rw [this, map_inv₀, hτ, inv_one]
  have hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1 := by
    intro ρ hρ i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hρ]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩
  · rw [← map_inv]
    exact hle _ hinv
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem fU_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz
  obtain ⟨hUL, hiw, -, hdiag⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hrev := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2

  set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef
  have hvϖ : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [v_eq_of_ne ϖ.ne_zero, hϖ.1]
  have hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  have hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1 := by
    intro i
    have e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      simp [hτdef]
    rw [e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u =
      tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
    rw [tdiag, ← map_mul]
    congr 1
    funext i
    simp [hτdef]

  have hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1 := by
    have h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w := hγ ▸ γ.2
    exact (hdiag u).1 ((hUL _).1 h1)
  have hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]
  have hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1 := by
    intro i
    have e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      intro j
      simp [hτdef]
    rw [e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]
    have h2 := hu1 i
    have hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    calc _ = (cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E)) *
          ((((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ *
            (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hp, one_mul]
  have hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w :=
    (hUL _).2 ((hdiag τ).2 hτ1)
  let κ : UL n w := ⟨_, hκU⟩
  have hκ : κ ∈ iwU n w b := by
    rw [hiw]
    have : b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
      change b⁻¹ * (b * _ * b⁻¹) * b = _
      group
    rw [this]
    exact diagT_mem_iwGL w n τ hτ
  unfold fU
  refine if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩
  change x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)
  rw [hγ, hfac]
  group

end GlobalTheory.CompanionTheory.DiagCoset
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupportStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_orbital_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagCoset.fU_diag | exact GlobalTheory.CompanionTheory.DiagCoset.fU_diag | (intros; apply GlobalTheory.CompanionTheory.DiagCoset.fU_diag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrder
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrder
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CanonOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
def lineSetoid : Setoid (IrrGL (k := k)) where
  r x y := ∃ m : ℤ, y = x.nu m
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := by
        rintro x _ ⟨m, rfl⟩
        exact ⟨-m, by simp⟩
      trans := by
        rintro x _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨m + n, by simp⟩ }

variable (k) in
def Line : Type 1 := Quotient (lineSetoid k)

instance lineLinearOrder : LinearOrder (Line k) := (exists_wellFoundedLT (Line k)).choose

def lineOf (x : IrrGL (k := k)) : Line k := Quotient.mk (lineSetoid k) x

def lineRep (x : IrrGL (k := k)) : IrrGL (k := k) := Quotient.out (s := lineSetoid k) (Quotient.mk (lineSetoid k) x)

theorem exists_height (x : IrrGL (k := k)) : ∃ m : ℤ, x = (lineRep x).nu m := by
  exact @Quotient.mk_out _ (lineSetoid k) x

def height (x : IrrGL (k := k)) : ℤ := (exists_height x).choose

theorem nu_height (x : IrrGL (k := k)) : (lineRep x).nu (height x) = x := by
  exact (exists_height x).choose_spec.symm

theorem lineRep_eq {x y : IrrGL (k := k)} (h : lineOf x = lineOf y) : lineRep x = lineRep y := by
  unfold lineRep
  unfold lineOf at h
  rw [h]

def key (Δ : Segment k) : Line k ×ₗ ℤ ×ₗ ℕ :=
  toLex (lineOf Δ.first, toLex (height Δ.first, Δ.len))

theorem key_injective : Function.Injective (key (k := k)) := by
  intro Δ Δ' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Segment.ext_first ?_ h3
  rw [← nu_height Δ.first, ← nu_height Δ'.first, lineRep_eq h1, h2]

private theorem lineOf_eq_height_eq_add_of_eq_nu {x y : IrrGL (k := k)} (hy : 0 < y.fst) {n : ℤ} (h : x = y.nu n) :
    lineOf x = lineOf y ∧ height x = height y + n := by
  have hl : lineOf x = lineOf y := by
    unfold lineOf
    refine Quotient.sound (s := lineSetoid k) ⟨-n, ?_⟩
    rw [h, IrrGL.nu_nu, Int.cast_neg, add_neg_cancel, IrrGL.nu_zero]
  refine ⟨hl, ?_⟩
  have hR := lineRep_eq hl
  have hRpos : 0 < (lineRep y).fst := by
    have h2 := congrArg Sigma.fst (nu_height y)
    rw [IrrGL.nu_fst] at h2
    rw [h2]
    exact hy
  apply (IrrGL.nu_intCast_inj hRpos).1
  calc (lineRep y).nu (height x) = (lineRep x).nu (height x) := by rw [hR]
    _ = x := nu_height x
    _ = y.nu n := h
    _ = ((lineRep y).nu (height y)).nu n := by rw [nu_height]
    _ = (lineRep y).nu ((height y + n : ℤ) : ℂ) := by rw [IrrGL.nu_nu, Int.cast_add]

theorem key_le {Δ Δ' : Segment k} (h : key Δ ≤ key Δ') :
    (¬ ∃ n : ℕ, 0 < n ∧ Δ.first = Δ'.first.nu (n : ℂ)) ∧ (Δ.first = Δ'.first → Δ.len ≤ Δ'.len) := by
  have hpos : 0 < Δ'.first.fst := Δ'.d_pos
  have hle := h
  simp only [key, Prod.Lex.toLex_le_toLex] at hle
  constructor
  · rintro ⟨n, hn, heq⟩
    have heq' : Δ.first = Δ'.first.nu ((n : ℤ) : ℂ) := by
      rw [Int.cast_natCast]
      exact heq
    obtain ⟨hl, hh⟩ := lineOf_eq_height_eq_add_of_eq_nu hpos heq'
    rcases hle with hlt | ⟨_, hlt | ⟨heq2, _⟩⟩
    · rw [hl] at hlt
      exact lt_irrefl _ hlt
    · omega
    · omega
  · intro hf
    rw [hf] at hle
    rcases hle with hlt | ⟨_, hlt | ⟨_, hlen⟩⟩
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt (lt_irrefl _)
    · exact hlen

theorem exists_isCanon {h : ℕ} (Γ : Fin h → Segment k) : ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  refine ⟨Tuple.sort (key ∘ Γ), ?_⟩
  have hmono : Monotone ((key ∘ Γ) ∘ Tuple.sort (key ∘ Γ)) := Tuple.monotone_sort _
  unfold IsCanon
  refine ⟨fun i j hij => key_le (hmono hij.le), fun i j l hij hjl hil => ?_⟩
  apply key_injective
  apply le_antisymm
  · calc key ((Γ ∘ Tuple.sort (key ∘ Γ)) j) ≤ key ((Γ ∘ Tuple.sort (key ∘ Γ)) l) := hmono hjl.le
      _ = key ((Γ ∘ Tuple.sort (key ∘ Γ)) i) := by rw [hil]
  · exact hmono hij.le

end GlobalTheory.CompanionTheory.CanonOrder

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrderStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_segment_order : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  first | exact @GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | exact GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | (intros; apply GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

private theorem C_mem_ptIdeal_iff_intCast_residueField_eq_zero (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (c : ℤ) :
    (MvPolynomial.C c : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ((c : ℤ) : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, eq_intCast,
    ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField x →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) c,
    MvPolynomial.C_eq_zero]

theorem ptIdeal_isHorizontal_iff (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsHorizontal (ptIdeal x) ↔ CharZero ((MP ℤ m n).residueField x) := by
  constructor
  · intro h
    have h' : (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥ := h
    refine charZero_of_inj_zero fun k hk => ?_
    have hm : ((k : ℤ)) ∈ (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) := by
      rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero]
      exact_mod_cast hk
    rw [h', Ideal.mem_bot] at hm
    exact_mod_cast hm
  · intro h
    show (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero] at hc
    exact Int.cast_eq_zero.mp hc

end GlobalTheory.CompanionTheory.MPDict
end
end
