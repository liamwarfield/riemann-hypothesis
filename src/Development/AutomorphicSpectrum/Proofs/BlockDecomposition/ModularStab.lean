module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScaling
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightInvariantHaarLevi

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerProperty
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

theorem mt_decomp_j0 (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = (d.j0 + d.jX ⬝ b) ⬝ mt W g := by
  have e : mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) =
      mt B (d.nC c) ⬝ (mt B (d.nB b) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a))) := by
    simp only [mt_mul, Matrix.mul_assoc]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.j0 = d.j0 ⬝ mt W g := by
    rw [Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have e₂ : mt B (d.nC c) ⬝ (d.j0 + d.jX ⬝ b) = d.j0 + d.jX ⬝ b := by
    rw [Matrix.mul_add, d.nC_j0, ← Matrix.mul_assoc, d.nC_jX]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc (mt B (d.nB b)), d.nB_j0,
    ← Matrix.mul_assoc, e₂]

theorem mt_decomp_jY (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = (d.jY + d.jX ⬝ c.1) ⬝ adj (a⁻¹).1 := by
  have e : mt B (d.nC c * (d.emb0 g * d.levi a)) = mt B (d.nC c) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a)) := by
    simp only [mt_mul]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := by
    rw [Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  rw [e, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc, d.nC_jY]

theorem coordB_eq_zero (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = 0) : b = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_j0, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : mt W g ⬝ mt W g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc b = b ⬝ mt W g ⬝ mt W g⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem coordC_eq_zero (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = 0) : c = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_jY, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : adj (a⁻¹).1 ⬝ adj a.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  apply Subtype.ext
  calc c.1 = c.1 ⬝ adj (a⁻¹).1 ⬝ adj a.1 := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem pX_levM {q : GlobalTheory.RegSW.stab d} (hq : q ∈ levM d) :
    d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0 ∧ d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0 := by
  obtain ⟨g, a, h⟩ := hq
  rw [h, mt_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding, d.pX_j0]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc (mt B (d.emb0 g)), d.wittDecomp_anisotropicEmbedding_inclY,
      ← Matrix.mul_assoc, d.pX_jY, Matrix.zero_mul]

theorem mem_levM_of_pX {q : GlobalTheory.RegSW.stab d} (h₀ : d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0)
    (hY : d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0) : q ∈ levM d := by
  obtain ⟨n, ⟨c, b, hn⟩, m, ⟨g, a, hm⟩, e⟩ := exists_radN_mul_levM d q
  have hq : (q : GA D B) = d.nC c * d.nB b * (d.emb0 g * d.levi a) := by
    rw [e, Subgroup.coe_mul, hn, hm]
  rw [hq] at h₀ hY
  have hb := coordB_eq_zero d c b g a h₀
  subst hb
  rw [d.nB_zero, mul_one] at hY
  have hc := coordC_eq_zero d c g a hY
  subst hc
  refine (mem_levM d).2 ⟨g, a, hq.trans ?_⟩
  rw [d.nC_zero, d.nB_zero, one_mul, one_mul]

theorem isClosed_levM (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun q : GlobalTheory.RegSW.stab d => mt B (q : GA D B) :=
    (continuous_mt B).comp continuous_subtype_val
  have h₀ : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have hY : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have e : (levM d : Set (GlobalTheory.RegSW.stab d)) = {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} ∩
      {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    Set.ext fun q => ⟨fun h => pX_levM d h, fun h => mem_levM_of_pX d h.1 h.2⟩
  rw [e]
  exact h₀.inter hY

end GlobalTheory.CompanionTheory.QKAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerPropertyStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_stabilizer_property : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_levM | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_levM | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_levM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivial
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem mt_mul_frame {k : ℕ} (x y : GA D B) (J : Mx D B.rank k) :
    mt B (x * y) ⬝ J = mt B x ⬝ (mt B y ⬝ J) := by
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul]

theorem levi_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    {a : GL (Fin t) (AE D)} (e : d.nC c * d.nB b = d.emb0 g * d.levi a) : a = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.jX = mt B (d.emb0 g * d.levi a) ⬝ d.jX := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_jX, d.nC_jX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX] at h
  apply Units.ext
  have h' : d.pX ⬝ d.jX = d.pX ⬝ (d.jX ⬝ a.1) := congrArg (fun M => d.pX ⬝ M) h
  rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h'
  exact h'.symm

theorem unitary_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    (e : d.nC c * d.nB b = d.emb0 g * d.levi 1) : g = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.j0 = mt B (d.emb0 g * d.levi 1) ⬝ d.j0 := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_j0, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, d.nC_j0,
    ← Matrix.mul_assoc, d.nC_jX] at h
  have h' : d.p0 ⬝ (d.j0 + d.jX ⬝ b) = d.p0 ⬝ (d.j0 ⬝ mt W g) := congrArg (fun M => d.p0 ⬝ M) h
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.zero_mul,
    add_zero, Matrix.one_mul] at h'
  apply GlobalTheory.MixModel.mt_injective
  rw [← h', GlobalTheory.MixModel.mt_one]

theorem radN_disj_levM : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  intro D B W t d x hn hm
  obtain ⟨c, b, hx⟩ := (mem_radN d).1 hn
  obtain ⟨g, a, hy⟩ := (mem_levM d).1 hm
  have e : d.nC c * d.nB b = d.emb0 g * d.levi a := hx.symm.trans hy
  have ha := levi_part_eq_one d e
  subst ha
  have hg := unitary_part_eq_one d e
  subst hg
  have h1 : d.emb0 1 * d.levi 1 = 1 := by rw [map_one, map_one, mul_one]
  exact Subtype.ext (hy.trans h1)

end GlobalTheory.CompanionTheory.QKAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivialStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_inf_levi_trivial : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | exact GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | (intros; apply GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsDetUnipotentRadicalEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsDetUnipotentRadicalEqOne
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem absDet_radN (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    ∀ n ∈ radN d, GlobalTheory.RegSW.absDet d n = 1 := by
  intro n hn
  obtain ⟨c, b, hcb⟩ := hn
  have hX : mt B (n : GA D B) ⬝ d.jX = d.jX := by
    rw [hcb, mt_mul, Matrix.mul_assoc, d.nB_jX, d.nC_jX]
  have hon : GlobalTheory.RegSW.onX d n = 1 := by
    apply Units.ext
    rw [GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d n), hX, d.pX_jX, Units.val_one]
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, hon, map_one]

end GlobalTheory.CompanionTheory.QKAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsDetUnipotentRadicalEqOneStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absDet_unipotent_radical_eq_one : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), ∀ n ∈ radN d, GlobalTheory.RegSW.absDet d n = 1 := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.absDet_radN | exact GlobalTheory.CompanionTheory.QKAvg.absDet_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.absDet_radN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizer
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem isClosed_radN : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  intro D B W t d
  have e : (radN d : Set (GlobalTheory.RegSW.stab d)) =
      (Subtype.val : GlobalTheory.RegSW.stab d → GA D B) ⁻¹' (GlobalTheory.MixPer.radX d : Set (GA D B)) := by
    ext q
    constructor
    · rintro ⟨c, b, h⟩
      exact (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, h.trans (d.nC_mul_nB b c)⟩
    · intro h
      obtain ⟨b, c, h⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 h
      exact ⟨c, b, h.trans (d.nC_mul_nB b c).symm⟩
  rw [e]
  exact (GlobalTheory.JacMeas.isClosed_radX d).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.QKAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizerStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_unipotent_radical_stabilizer : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_radN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacter
open MeasureTheory Topology Pointwise
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.QKAvg

theorem mass_const {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Q K : Subgroup G) [LocallyCompactSpace Q]
    (hdec : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (δ : Q →* ℝ≥0) (hδc : Continuous δ)
    (hΔ : ∀ q : Q, Measure.modularCharacterFun q = δ q) (ν : Measure Q) [ν.IsHaarMeasure]
    [SecondCountableTopology Q] {E : Set G} (hEm : MeasurableSet E)
    (hEK : ∀ g, ∀ k ∈ K, g * k ∈ E ↔ g ∈ E) (g : G) :
    ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * g) * (δ q : ℝ≥0∞) ∂ν =
      ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
  obtain ⟨q0, hq0, k, hk, rfl⟩ := hdec g
  obtain ⟨p, hp⟩ : ∃ p : Q, p.1 = q0 := ⟨⟨q0, hq0⟩, rfl⟩
  have hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) :=
    ((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal
  have hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) =
      (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) := by
    intro q
    have hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E := by
      rw [← mul_assoc, Subgroup.coe_mul, hp]
      exact hEK _ k hk
    have h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]
    have h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1 := by
      classical
      by_cases hm : (q * p).1 ∈ E
      · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]
        rfl
      · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]
    rw [h3, h2]
    ring
  have hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞) := by
    rw [hΔ p]
  calc ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) ∂ν
      = ∫⁻ q : Q, (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) ∂ν := by
        congr 1
        funext q
        exact hpt q
    _ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν :=
        lintegral_const_mul _ (hF.comp (measurable_mul_const p))
    _ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) *
          ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) :=
        congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)
    _ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
        rw [hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one,
          one_mul]

theorem lintegral_mul_right_of_modular_law : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g
  haveI := hκ
  haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  haveI := hν
  obtain ⟨c, hc0, hctop, hdecomp⟩ :=
    GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ
  obtain ⟨S, hSc, hS1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := S * (K : Set G) with hE
  have hEc : IsCompact E := hSc.mul hK
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E := by
    intro h k hk
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h * k := hab
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      show a * (b * k⁻¹) = h
      rw [← mul_assoc, hab', mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h := hab
      refine ⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩
      show a * (b * k) = h * k
      rw [← mul_assoc, hab']
  set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef
  have hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M :=
    fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t
  have hT : IsCompact (((↑) : Q → G) ⁻¹' E) := hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc
  have hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν := by
    rw [hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ E
    · simp [Set.indicator_apply, hq]
    · simp [Set.indicator_apply, hq]
  have hMtop : M ≠ ⊤ := by
    rw [hMeq]
    exact (setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne
  have hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0 := by
    intro q hq
    have h1 := map_mul_eq_one δ (mul_inv_cancel q)
    rw [ENNReal.coe_eq_zero] at hq
    rw [hq, zero_mul] at h1
    exact zero_ne_one h1
  have hM0 : M ≠ 0 := by
    rw [hMeq]
    intro h0
    rw [lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False :=
      h0.mono fun q hq => hδ0 q hq
    rw [ae_iff] at h1
    have hTz : ν (((↑) : Q → G) ⁻¹' E) = 0 := by simpa using h1
    have hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS1
    have hpos := Measure.measure_pos_of_mem_nhds ν hV
    have hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E := fun q hq =>
      ⟨q.1, hq, 1, K.one_mem, mul_one _⟩
    have := measure_mono (μ := ν) hsub
    rw [hTz] at this
    exact (lt_irrefl 0 (hpos.trans_le this))
  have hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b := by
    intro a b
    have h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) =
        E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b := by
      intro q
      rw [hsq q b, mul_assoc]
    have hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) :=
      ((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul
        hδc.measurable.coe_nnreal_ennreal
    rw [lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]
  have hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ) := by
    have hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g) :=
      (measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k) (↑k * g)
  have hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ) := by
    have hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h :=
      ((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k * g⁻¹) ↑k
  have hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ =
      ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]
    simp only [mul_inv_cancel_right]
  rw [hA, hB] at hI
  exact (ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)

end GlobalTheory.CompanionTheory.QKAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacterStatement
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_iwasawa_modular_character : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | exact GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | (intros; apply GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterFunEqOfMapLeftMul
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_eq_of_map_left_mul :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (ρ : Measure Q) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [ρ.IsMulRightInvariant] (δ : Q →* ℝ≥0), (∀ q : Q, ρ.map (fun x => q * x) = (δ q)⁻¹ • ρ) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ ρ _ _ _ δ h q
  have : ρ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hδ : (δ q⁻¹)⁻¹ = δ q := by
    rw [inv_eq_iff_eq_inv]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  have hcomp : (fun x : Q => x * q) ∘ Inv.inv = Inv.inv ∘ (fun y : Q => q⁻¹ * y) := by
    funext y
    simp [mul_inv_rev]
  have hmap : Measure.map (fun x : Q => x * q) ρ.inv = δ q • ρ.inv := by
    rw [Measure.inv_def, Measure.map_map (measurable_mul_const q) measurable_inv, hcomp,
      ← Measure.map_map measurable_inv (measurable_const_mul q⁻¹), h q⁻¹, Measure.map_smul, hδ]
    exact measurable_inv.aemeasurable
  rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ.inv q]
  simp only [hmap, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.ModChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplement
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.TopGroup

theorem homeomorph_prod_of_closed_complements :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
      [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q),
      IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) →
      (∀ x, x ∈ N → x ∈ M → x = 1) →
      ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  intro Q _ _ _ _ _ _ N M hN hM hprod hint
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  haveI : SigmaCompactSpace (N × M) := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI act : MulAction (N × M) Q :=
    { smul := fun p q => (p.1 : Q) * q * (p.2 : Q)⁻¹
      one_smul := fun q => by
        change ((1 : N) : Q) * q * ((1 : M) : Q)⁻¹ = q
        simp
      mul_smul := fun p r q => by
        change ((p.1 * r.1 : N) : Q) * q * ((p.2 * r.2 : M) : Q)⁻¹ =
          (p.1 : Q) * ((r.1 : Q) * q * (r.2 : Q)⁻¹) * (p.2 : Q)⁻¹
        simp [mul_assoc] }
  have hsmul : ∀ (p : N × M) (q : Q), p • q = (p.1 : Q) * q * (p.2 : Q)⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (N × M) Q := ⟨by
    have : (fun x : (N × M) × Q => x.1 • x.2) =
        fun x : (N × M) × Q => ((x.1.1 : Q)) * x.2 * ((x.1.2 : Q))⁻¹ := rfl
    rw [this]
    fun_prop⟩
  haveI : MulAction.IsPretransitive (N × M) Q := ⟨fun x y => by
    obtain ⟨n₁, hn₁, m₁, hm₁, rfl⟩ := hprod x
    obtain ⟨n₂, hn₂, m₂, hm₂, rfl⟩ := hprod y
    refine ⟨(⟨n₂ * n₁⁻¹, N.mul_mem hn₂ (N.inv_mem hn₁)⟩,
      ⟨m₂⁻¹ * m₁, M.mul_mem (M.inv_mem hm₂) hm₁⟩), ?_⟩
    rw [hsmul]
    simp [mul_assoc]⟩
  have hopen₀ : IsOpenMap (fun g : N × M => g • (1 : Q)) := isOpenMap_smul_of_sigmaCompact (1 : Q)
  let e : (N × M) ≃ₜ (N × M) := (Homeomorph.refl N).prodCongr (Homeomorph.inv M)
  let f : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have hf : f = (fun g : N × M => g • (1 : Q)) ∘ e := by
    funext p
    change (p.1 : Q) * (p.2 : Q) = ((e p).1 : Q) * 1 * (((e p).2 : M) : Q)⁻¹
    simp [e]
  have hopen : IsOpenMap f := by
    rw [hf]
    exact hopen₀.comp e.isOpenMap
  have hcont : Continuous f := by fun_prop
  have hinj : Function.Injective f := by
    rintro ⟨⟨n₁, hn₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨n₂, hn₂⟩, ⟨m₂, hm₂⟩⟩ h
    have h' : n₁ * m₁ = n₂ * m₂ := h
    have h1 : n₂⁻¹ * n₁ = m₂ * m₁⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h']
    have h2 : n₂⁻¹ * n₁ = 1 :=
      hint _ (N.mul_mem (N.inv_mem hn₂) hn₁) (h1 ▸ M.mul_mem hm₂ (M.inv_mem hm₁))
    have h3 : n₁ = n₂ := by
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have h4 : m₁ = m₂ := by
      subst h3
      exact mul_left_cancel h'
    subst h3
    subst h4
    rfl
  have hsurj : Function.Surjective f := fun q => by
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod q
    exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    fun _ => rfl⟩

end GlobalTheory.CompanionTheory.TopGroup
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplementStatement
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q), IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | exact GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | (intros; apply GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormula
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_semidirect :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ N M _ _ _ hN hM hgen hdisj νN νM hNH hNR hMH hMR δ hδN hδM q
  haveI := hNH
  haveI := hNR
  haveI := hMH
  haveI := hMR
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set Q))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set Q))
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement Q N M hN hM hgen hdisj
  let Ψ : (M × N) ≃ₜ Q := (Homeomorph.prodComm M N).trans Φ
  have hΨ : ∀ p : M × N, Ψ p = (p.2 : Q) * (p.1 : Q) := fun p => hΦ (p.2, p.1)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  set ρ : Measure Q := (νM.prod νN).map Ψ with hρ
  have hconj : ∀ (m : Q) (n : N), ((MulAut.conjNormal m n : N) : Q) = m * n * m⁻¹ :=
    fun m n => MulAut.conjNormal_apply m n
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) K = (νM.prod νN) (Ψ ⁻¹' K) from
      Ψ.toMeasurableEquiv.map_apply K]
    have : IsCompact (Ψ ⁻¹' K) := by
      have := hK.image Ψ.symm.continuous
      rwa [Ψ.symm.image_eq_preimage_symm, Ψ.symm_symm] at this
    exact this.measure_lt_top
  haveI : ρ.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) U = (νM.prod νN) (Ψ ⁻¹' U) from
      Ψ.toMeasurableEquiv.map_apply U]
    exact (hU.preimage Ψ.continuous).measure_ne_zero _ (hne.preimage Ψ.surjective)
  haveI : ρ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective g
    have hmul : Measurable (fun y : Q => y * Ψ (m₀, n₀)) := measurable_mul_const _
    have hc : Continuous (fun p : M × N => (MulAut.conjNormal (p.1 : Q) n₀ : N)) := by
      have h : Continuous (fun p : M × N => (p.1 : Q) * n₀ * (p.1 : Q)⁻¹) := by fun_prop
      exact Topology.IsInducing.subtypeVal.continuous_iff.2
        (h.congr fun p => (hconj _ _).symm)
    let T : M × N → M × N := fun p => (p.1 * m₀, p.2 * MulAut.conjNormal (p.1 : Q) n₀)
    have hT : MeasurePreserving T (νM.prod νN) (νM.prod νN) := by
      refine MeasurePreserving.skew_product (f := fun m : M => m * m₀)
        (g := fun (m : M) (n : N) => n * MulAut.conjNormal (m : Q) n₀)
        (measurePreserving_mul_right νM m₀) ?_ (Filter.Eventually.of_forall fun m => ?_)
      · exact (continuous_snd.mul hc).measurable
      · exact (measurePreserving_mul_right νN _).map_eq
    have hcomp : (fun y : Q => y * Ψ (m₀, n₀)) ∘ Ψ = Ψ ∘ T := by
      funext ⟨m, n⟩
      simp only [Function.comp, T, hΨ, Subgroup.coe_mul, hconj]
      group
    rw [hρ, Measure.map_map hmul hΨm, hcomp, ← Measure.map_map hΨm hT.measurable, hT.map_eq]
  refine GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_eq_of_map_left_mul Q ρ δ ?_ q
  intro q₀
  obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective q₀
  have hmul : Measurable (fun y : Q => Ψ (m₀, n₀) * y) := measurable_const_mul _
  have hcm : Continuous (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := by
    have h : Continuous (fun n : N => (m₀ : Q) * n * (m₀ : Q)⁻¹) := by fun_prop
    exact Topology.IsInducing.subtypeVal.continuous_iff.2
      (h.congr fun p => (hconj _ _).symm)
  let f₁ : M → M := fun m => m₀ * m
  let f₂ : N → N := fun n => n₀ * MulAut.conjNormal (m₀ : Q) n
  have hf₁ : Measurable f₁ := measurable_const_mul _
  have hf₂ : Measurable f₂ := (continuous_const.mul hcm).measurable
  have hcomp : (fun y : Q => Ψ (m₀, n₀) * y) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext ⟨m, n⟩
    simp only [Function.comp, Prod.map, f₁, f₂, hΨ, Subgroup.coe_mul, hconj]
    group
  have hνM : νM.map f₁ = νM := (measurePreserving_mul_left νM m₀).map_eq
  have hνN : νN.map f₂ = (δ m₀)⁻¹ • νN := by
    have : f₂ = (fun n : N => n₀ * n) ∘ (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hcm.measurable, hδM _ m₀.2,
      Measure.map_smul (c := (δ m₀)⁻¹) (f := fun x : N => n₀ * x)
        (measurable_const_mul _).aemeasurable,
      (measurePreserving_mul_left νN n₀).map_eq]
  have hδ : δ (Ψ (m₀, n₀)) = δ m₀ := by
    rw [hΨ]
    simp [map_mul, hδN _ n₀.2]
  rw [hρ, Measure.map_map hmul hΨm, hcomp,
    ← Measure.map_map hΨm (hf₁.prodMap hf₂), ← Measure.map_prod_map νM νN hf₁ hf₂, hνM, hνN,
    Measure.prod_smul_right,
    Measure.map_smul (c := (δ m₀)⁻¹) (f := Ψ) hΨm.aemeasurable, hδ]

end GlobalTheory.CompanionTheory.ModChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormulaStatement
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_semidirect_product_formula : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  first | exact @GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | exact GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | (intros; apply GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect <;> assumption)
end
end

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem modular_stab (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (GlobalTheory.RegSW.stab d)]
    (q : GlobalTheory.RegSW.stab d) :
    Measure.modularCharacterFun q = GlobalTheory.RegSW.absDet d q ^ (W.rank + t) := by
  haveI : LocallyCompactSpace (radN d) := (GlobalTheory.T.isClosed_unipotent_radical_stabilizer D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (levM d) := (GlobalTheory.T.unipotent_radical_stabilizer_property D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.RegSW.stab d) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨νN, h1, h2, h3⟩ := GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling D B W t d
  obtain ⟨νM, h4, h5⟩ := GlobalTheory.T.exists_right_invariant_haar_levi D B W t d
  exact GlobalTheory.T.haar_measure_semidirect_product_formula (GlobalTheory.RegSW.stab d) (radN d) (levM d) (GlobalTheory.T.isClosed_unipotent_radical_stabilizer D B W t d) (GlobalTheory.T.unipotent_radical_stabilizer_property D B W t d)
    (exists_radN_mul_levM d) (GlobalTheory.T.unipotent_radical_inf_levi_trivial D B W t d)
    νN νM h1 h2 h4 h5 ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (fun n hn => by simp [GlobalTheory.T.absDet_unipotent_radical_eq_one D B W t d n hn]) (fun m hm => by simpa using h3 m hm) q

theorem qk : PositivityTheory.Rg.Rsw.L.QK := by
  intro D t B W d l hl νK hνK s hs hlaw g
  obtain ⟨hIw, hK⟩ := GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d hl
  haveI : LocallyCompactSpace (GlobalTheory.RegSW.stab d) :=
    (GlobalTheory.RegSW.isClosed_stab d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GA D B) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D B μ inferInstance
  refine GlobalTheory.T.haar_measure_iwasawa_modular_character (GA D B) μ (GlobalTheory.RegSW.stab d) l.K (GlobalTheory.RegSW.isClosed_stab d) hK
    (fun g => ?_) ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (show Continuous fun q => GlobalTheory.RegSW.absDet d q ^ (W.rank + t) from (GlobalTheory.RegSW.continuous_absDet d).pow _)
    (fun q => ?_) νK hνK s hs (fun q h => ?_) g
  · obtain ⟨q, k, hk, e⟩ := hIw g
    exact ⟨q, q.2, k, hk, e⟩
  · simpa using modular_stab D B W t d q
  · simpa using hlaw q h

end GlobalTheory.CompanionTheory.QKAvg
