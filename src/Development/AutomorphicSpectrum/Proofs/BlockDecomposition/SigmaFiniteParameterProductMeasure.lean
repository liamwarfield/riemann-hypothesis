module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

def c1 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a W.rank :=
  U.submatrix id fun j => finCongr hn (Fin.castAdd t j)

def c2 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a t :=
  U.submatrix id fun j => finCongr hn (Fin.natAdd W.rank j)

def ww (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) : Mx D W.rank W.rank :=
  mm (mt W h⁻¹) (rat x₀)

def ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) : Mx D V.rank a × Mx D V.rank b :=
  (mm (mt V g) z.1, mm (mt V g) z.2)

abbrev Par (D : D7) (n t : ℕ) (W : HSp D) : Type := GA D W × Mx D t n × Mx D W.rank t

def zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (p : Par D n t W) :
    Mx D B.rank W.rank × Mx D B.rank t :=
  (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1),
    mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1))

def Q0 {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) : Measure (Par D n t W) :=
  I.m.prod (I.μ₁.prod μ)

def rho {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (Q0 I μ).map (zp d hn x₀)

def nuT {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (I.νK.prod (Q0 I μ)).map fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem top_mx (a b : ℕ) : IsTopologicalAddGroup (Mx D a b) ∧ LocallyCompactSpace (Mx D a b) ∧ SecondCountableTopology (Mx D a b) ∧
    T2Space (Mx D a b) ∧ BorelSpace (Mx D a b) := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  exact ⟨i1, i2, i3, i4, ⟨rfl⟩⟩

theorem continuous_first_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c1 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_second_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c2 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Continuous (ww W x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  exact ((continuous_mt W).comp continuous_inv).matrix_mul continuous_const

theorem continuous_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous (zp d hn x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) B.rank W.rank).1
  have hT2 := (top_mx (D := D) B.rank t).1
  have h1 : Continuous fun p : Par D n t W => mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1) :=
    (continuous_const.matrix_mul ((continuous_first_column_block hn).comp (continuous_fst.comp continuous_snd))).add
      (continuous_const.matrix_mul ((continuous_ww x₀).comp continuous_fst))
  exact h1.prodMk ((h1.matrix_mul (continuous_snd.comp continuous_snd)).add
    (continuous_const.matrix_mul ((continuous_second_column_block hn).comp (continuous_fst.comp continuous_snd))))

theorem continuous_ac (V : HSp D) {a b : ℕ} :
    Continuous fun u : GA D V × (Mx D V.rank a × Mx D V.rank b) => ac V u.1 u.2 := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).prodMk
    (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_snd.comp continuous_snd))

theorem top_pair (a b c : ℕ) : BorelSpace (Mx D a b × Mx D a c) ∧ SecondCountableTopology (Mx D a b × Mx D a c) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) a b
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) a c
  exact ⟨inferInstance, inferInstance⟩

theorem top_par (n t : ℕ) (W : HSp D) : BorelSpace (Par D n t W) ∧ SecondCountableTopology (Par D n t W) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) t n
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, -, g4, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance⟩

theorem measurable_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable (zp d hn x₀) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  exact (continuous_zp d hn x₀).measurable

theorem sigmaFinite_parameter_product_measure {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) :
    SigmaFinite (Q0 I μ) := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  unfold Q0
  infer_instance

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

def XU (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) (U : Mx D t n) :
    Mx D B.rank n :=
  mm d.jX U + mm d.j0 (jn hn (ww W x₀ h) 0)

theorem measurable_pi {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  have hc : Continuous fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) :=
    (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  exact hc.measurable

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

def Dom : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b c : ℕ) (ι : Fin c → Fin b), Function.Injective ι →
  ∀ Φ ∈ schwartzA θ a b, ∃ M ∈ schwartzA θ a c, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
    ∀ x : Mx D a b, ‖Φ x‖ ≤ (M (x.submatrix id ι)).re

def OrbFin : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (m : Measure (GA D W)), m.IsHaarMeasure →
  ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ N ∈ schwartzA θ W.rank W.rank,
    ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂m < ⊤

def ZpEq : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (b₀ : HermE D W.rank),
  b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ p : Par D n t W,
    ip B (zp d hn x₀ p).1 (zp d hn x₀ p).1 = rat b₀.1 ∧ yv B b₀ (zp d hn x₀ p) = p.2.2 ∧ qv B b₀ (zp d hn x₀ p) = 0

def AcEq : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) (g : GA D V) (z : Mx D V.rank r × Mx D V.rank t),
  ip V (ac V g z).1 (ac V g z).1 = ip V z.1 z.1 ∧ yv V b₀ (ac V g z) = yv V b₀ z ∧ qv V b₀ (ac V g z) = qv V b₀ z

def JnPi : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) x₀ (g : GA D B) (p : Par D n t W),
  jn hn (ac B g (zp d hn x₀ p)).1 (ac B g (zp d hn x₀ p)).2 =
    mm (mt B g) (mm (XU d hn x₀ p.1 p.2.1) (bl hn 1 p.2.2 0 1))

def JnBl : Prop := ∀ (D : D7) (n t a : ℕ) (r : ℕ) (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t),
  mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v)

def Ext0 : Prop := ∀ (D : D7) (n t : ℕ) (W : HSp D) (hn : W.rank + t = n) x₀ (h : GA D W),
  mm (mt W h⁻¹) (rat (ext0 hn x₀)) = jn hn (ww W x₀ h) 0

def Shift : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (Φ : Mx D B.rank n → ℂ) (y : Mx D W.rank t) (a : Mx D W.rank n),
    ikp I (fun X => Φ (mm X (bl hn 1 y 0 1))) a = ikp I Φ (mm a (bl hn 1 y 0 1))

def IkLint : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (I : IkD d n) θ, IsInfFam θ →
  ∀ M ∈ schwartzA θ B.rank n, (∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) → ∀ a : Mx D W.rank n,
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 a))‖ₑ ∂I.νK ∂I.μ₁ = ‖ikp I M a‖ₑ

def Fub4 : Prop := ∀ (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e],
  (∀ f : α × β × γ × δ → ℂ, Integrable f (a.prod (b.prod (c.prod e))) →
    ∫ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫ y, ∫ h, ∫ u, ∫ k, f (k, h, u, y) ∂a ∂c ∂b ∂e) ∧
  (∀ f : α × β × γ × δ → ℝ≥0∞, Measurable f →
    ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, f (k, h, u, y) ∂a ∂c ∂b ∂e)

def Law : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (q : GlobalTheory.RegSW.stab d),
    (rho hn I μ x₀).map (ac B (q : GA D B)) = ((GlobalTheory.RegSW.absDet d q)⁻¹ ^ (W.rank + t) : ℝ≥0) • rho hn I μ x₀

def core {D : D7} {n t : ℕ} {B W : HSp D} {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (Φ : Mx D B.rank n → ℂ) (η : Mx D W.rank t → ℂ) (p : I.l.K × Par D n t W) : ℂ :=
  Φ (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1))) * conj (η p.2.2.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitaryWitt

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem conj_mem_UJ_one_iff (σ : L →+* L) {J : Matrix (Fin n) (Fin n) L} (b g : GL (Fin n) L)
    (hb : cT σ b.val * b.val = J) : b * g * b⁻¹ ∈ UJ σ 1 ↔ g ∈ UJ σ J := by
  have hbi : b.val * (b⁻¹ : GL (Fin n) L).val = 1 := by rw [← Units.val_mul]; simp
  have hib : (b⁻¹ : GL (Fin n) L).val * b.val = 1 := by rw [← Units.val_mul]; simp
  change cT σ (b * g * b⁻¹).val * 1 * (b * g * b⁻¹).val = 1 ↔ cT σ g.val * J * g.val = J
  simp only [Units.val_mul, Matrix.mul_one]
  have hc : cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val = 1 := by
    rw [← cT_mul, hbi, cT_one]
  have key : cT σ (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) * (b.val * g.val * (b⁻¹ : GL (Fin n) L).val)
      = cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val := by
    rw [← hb]
    simp only [cT_mul, Matrix.mul_assoc]
  rw [key]
  constructor
  · intro h
    have h2 : cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val
        = cT σ b.val * 1 * b.val := by rw [h]
    have hc' : cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val = 1 := by
      rw [← cT_mul, hib, cT_one]
    calc cT σ g.val * J * g.val
        = (cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val) * (cT σ g.val * J * g.val) * ((b⁻¹ : GL (Fin n) L).val * b.val) := by
          rw [hc', hib, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.mul_one, hb]
  · intro h
    rw [h, ← hb]
    calc cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ b.val * b.val) * (b⁻¹ : GL (Fin n) L).val
        = (cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val) * (b.val * (b⁻¹ : GL (Fin n) L).val) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hbi, Matrix.one_mul]

theorem diagT_mem_UJ_antiJ_iff (σ : L →+* L) (u : Fin n → Lˣ) :
    GlobalTheory.SmGL.diagT L (Fin n) u ∈ UJ σ (antiJ L n) ↔ ∀ i, σ (u i) * u (Fin.rev i) = 1 := by
  have hent : ∀ i j, (cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val) i j
      = σ (u i) * antiJ L n i j * u j := by
    intro i j
    have hd : cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val = Matrix.diagonal fun i => σ (u i) := by
      rw [GlobalTheory.SmGL.val_diagT]
      ext a c
      by_cases h : a = c
      · subst h; simp [cT]
      · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rw [hd, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrev : ∀ i : Fin n, antiJ L n i (Fin.rev i) = 1 := by
    intro i
    have : i.val + (Fin.rev i).val + 1 = n := by
      rw [Fin.val_rev]; omega
    exact if_pos this
  change cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val = antiJ L n ↔ _
  constructor
  · intro h i
    have := congrFun (congrFun h i) (Fin.rev i)
    rw [hent, hrev, mul_one] at this
    exact this
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = Fin.rev i := by
        apply Fin.ext; rw [Fin.val_rev]; omega
      subst hj
      rw [hrev, mul_one, h i]
    · have : antiJ L n i j = 0 := by simp [antiJ, hij]
      rw [this]; simp

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem UL_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) : UL n w = UJ (cj w) 1 := if_neg hw

theorem mem_iwU_iff (n : ℕ) (w : Pl E) (b : GLw n w) (γ : UL n w) :
    γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w := by
  rw [iwU, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have e' : b * x * b⁻¹ = γ.1 := e
    rw [← e']
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    change b * (b⁻¹ * γ.1 * b) * b⁻¹ = γ.1
    group

theorem isClosed_UJ_one {w : Pl E} (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Set (GLw n w)) := by
  have hv : Continuous fun g : GLw n w => (g.val : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GLw n w => cT (cj w) g.val * 1 * g.val := by
    refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
    exact (hv.matrix_map hc).matrix_transpose
  exact isClosed_eq hm continuous_const

theorem isCompact_iwU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hc : Continuous (cj w)) :
    IsCompact (iwU n w b : Set (UL n w)) := by
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [UL_eq_of_not_split hw]; exact isClosed_UJ_one n hc
  have hK : IsCompact ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n)).image (by fun_prop)
  have hP := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have e : (iwU n w b : Set (UL n w)) = Subtype.val ⁻¹'
      ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) := by
    ext γ
    simp only [SetLike.mem_coe, mem_iwU_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨_, h, by group⟩
    · rintro ⟨x, hx, e⟩
      rw [← e]
      simpa [mul_assoc] using hx
  rw [e]
  exact hP

theorem unitary_hyperbolic_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  intro E _ _ _ hU w hw n b hb
  refine ⟨fun g => ?_, mem_iwU_iff n w b, isCompact_iwU hw n b (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1,
    diagT_mem_UJ_antiJ_iff (cj w)⟩
  rw [UL_eq_of_not_split hw]
  exact conj_mem_UJ_one_iff (cj w) b g hb.2

end GlobalTheory.CompanionTheory.UnitaryWitt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactsStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis | exact GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis | (intros; apply GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem hypOne_mul_hypOne_of_mul_eq_one {K : Type} [Field K] {M : ℕ} {A B : Matrix (Fin M) (Fin M) K}
    (h : A * B = 1) : hypOne A * hypOne B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, Matrix.one_apply,
      ← Matrix.mul_apply, h, Fin.ext_iff]

theorem isHermND_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    all_goals first
      | exact hJ.1 i j
      | simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
          hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one]
  · have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
    have h1 : hypOne J * hypOne J⁻¹ = 1 :=
      hypOne_mul_hypOne_of_mul_eq_one (Matrix.mul_nonsing_inv J hu)
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2

theorem e0_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨linearIndependent_unique_iff.2 ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · ext a b
    simp [gramE, hE, hform, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem hypOne_isHermND_and_e0_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (_hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) :=
  ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_sum_nondegenerate_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : Fin (M + 2) → K :=
  Fin.cons a (Fin.cons s Y)

def tailH {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : Fin M → K := fun i => x i.succ.succ

section Chart

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR : R ⊗[F] E := inclR R (algebraMap F E (1 / 2))

def tHalf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E) : R ⊗[F] E :=
  halfR (F := F) (E := E) R * hR R σ (hypOne J) x x

def cvec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x v : Fin (M + 2) → R ⊗[F] E) :
    Fin (M + 2) → R ⊗[F] E :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (sigR R σ (x 0)) *
      (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
    (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E :=
  Fin.cons (x 0) fun j => cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))


variable {R} in
def yPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin n → Fin M → K :=
  fun j i => X j.succ i.succ.succ - X j.succ 0 * Ring.inverse (X 0 0) * X 0 i.succ.succ

def freeCell (K : Type) [CommRing K] (M n : ℕ) : Set (Fin (n + 1) → Fin (M + 2) → K) :=
  {X | IsUnit (X 0 0) ∧ LinearIndependent K (yPart X)}

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

def qH (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (t : HermR R σ 1) (s a : Fin 1 → Fin n → R ⊗[F] E) :
    HermR R σ n :=
  ⟨Matrix.of fun i j => sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
      (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j), by
    intro i j
    have ht : sigR R σ ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      t.2 0 0
    simp only [Matrix.of_apply, map_add (f := _), map_sub, map_mul, sigR_sigR R σ hσ, ht]
    ring⟩

end Chart

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def scalT {K : Type} [Mul K] {n M : ℕ} (c : K) (y : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun p i => c * y p i

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

def qv (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)


variable (E) in
def zetaV (v : HeightOneSpectrum (𝓞 F)) (s : ℕ) : ℝ :=
  open Classical in
  if IsField (Fv F v ⊗[F] E) then (1 - ((qv v : ℝ) ^ (2 * s))⁻¹)⁻¹ else ((1 - ((qv v : ℝ) ^ s)⁻¹)⁻¹) ^ 2

def IsContent (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type}
    (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ) : Prop :=
  (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧
  (∀ i (lam : Measure (Fv F v)), IsStdV v lam →
    (coordK (Fv F v) b lam).map (fun x => c i * x) = (qv v ^ w i) • coordK (Fv F v) b lam) ∧
  (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧
    ‖t‖ = ((qv v : ℝ) ^ w i)⁻¹) ∧
  (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧
  (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j)

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.Wexp

theorem cone_strictAnti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) : StrictAnti l := by
  have key : ∀ (d : ℕ) (i j : Fin m), (j : ℕ) = i + d + 1 → l j < l i := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have := hl.1 i j (by omega)
      omega
    | succ d ih =>
      intro i j hij
      have hk : (i : ℕ) + d + 1 < m := by have := j.isLt; omega
      have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
      have h2 := hl.1 ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
      omega
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  exact key ((j : ℕ) - i - 1) i j (by omega)

theorem wexp_of_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    wexp n l i = l ⟨i, h⟩ := by
  simp only [wexp, dif_pos h]

theorem wexp_of_rev_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h' : n - 1 - (i : ℕ) < n / 2) :
    wexp n l i = -l ⟨n - 1 - i, h'⟩ := by
  have h : ¬ (i : ℕ) < n / 2 := by have := i.isLt; omega
  simp only [wexp, dif_neg h, dif_pos h']

theorem wexp_of_middle {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : ¬ (i : ℕ) < n / 2)
    (h' : ¬ n - 1 - (i : ℕ) < n / 2) : wexp n l i = 0 := by
  simp only [wexp, dif_neg h, dif_neg h']

theorem wexp_strictAnti_rev : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l →
    StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  intro n l hl
  have hs := cone_strictAnti hl
  have hp := hl.2
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.isLt
    by_cases h1 : (i : ℕ) < n / 2
    · rw [wexp_of_lt l i h1]
      have a := hp ⟨i, h1⟩
      by_cases h2 : (j : ℕ) < n / 2
      · rw [wexp_of_lt l j h2]
        exact hs (Fin.mk_lt_mk.mpr hij')
      · by_cases h3 : n - 1 - (j : ℕ) < n / 2
        · rw [wexp_of_rev_lt l j h3]
          have b := hp ⟨_, h3⟩
          omega
        · rw [wexp_of_middle l j h2 h3]
          omega
    · have h3 : n - 1 - (j : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l j h3]
      have b := hp ⟨_, h3⟩
      by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · rw [wexp_of_rev_lt l i h2]
        have : l ⟨n - 1 - i, h2⟩ < l ⟨n - 1 - j, h3⟩ := hs (Fin.mk_lt_mk.mpr (by omega))
        omega
      · rw [wexp_of_middle l i h1 h2]
        omega
  · intro i
    have hi := i.isLt
    have hr : ((Fin.rev i : Fin n) : ℕ) = n - 1 - i := by
      rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < n / 2
    · have h' : n - 1 - ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l _ h', wexp_of_lt l i h1]
      congr 2
      apply Fin.ext
      simp only
      omega
    · by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · have h' : ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
        rw [wexp_of_lt l _ h', wexp_of_rev_lt l i h2, neg_neg]
        congr 1
        exact Fin.ext hr
      · rw [wexp_of_middle l i h1 h2, wexp_of_middle l _ (by omega) (by omega), neg_zero]

end GlobalTheory.CompanionTheory.Wexp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitoneStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_exponent_strictly_antitone : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l → StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  first | exact @GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | exact GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | (intros; apply GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AdeleComp

open TensorProduct

theorem coord_zero {F A B E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (ℬ : Module.Basis ι F E) (f : A →ₗ[F] B) (c : ι →₀ A)
    (h : LinearMap.rTensor E f (c.sum fun i m => m ⊗ₜ[F] ℬ i) = 0) (i : ι) : f (c i) = 0 := by
  have h1 : (c.mapRange f (map_zero f)).sum (fun i m => m ⊗ₜ[F] ℬ i) = 0 := by
    rw [Finsupp.sum_mapRange_index (by intro i; simp)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h, Finsupp.sum, Finsupp.sum, map_sum]
    simp
  have h2 := TensorProduct.sum_tmul_basis_right_eq_zero ℬ _ h1
  simpa using DFunLike.congr_fun h2 i

theorem adele_eq_zero {F : Type} [Field F] [NumberField F] (x : AF F)
    (hi : ∀ w, evInf F w x = 0) (hf : ∀ v, evFin F v x = 0) : x = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact RestrictedProduct.ext _ _ fun v => hf v

theorem tensor_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (a : AF F ⊗[F] E) (hi : ∀ w, compInf F E w a = 0) (hf : ∀ v, compFin F E v a = 0) : a = 0 := by
  let ℬ := Module.Basis.ofVectorSpace F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ a
  have hc : c = 0 := by
    ext i
    refine adele_eq_zero _ (fun w => ?_) (fun v => ?_)
    · refine coord_zero ℬ (evInf F w).toLinearMap c ?_ i
      rw [← hi w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [compInf, Finsupp.sum, map_sum]
      rfl
    · refine coord_zero ℬ (evFin F v).toLinearMap c ?_ i
      rw [← hf v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [compFin, Finsupp.sum, map_sum]
      rfl
  simp [hc]

theorem eq_zero_of_comps (D : D7) (a : AE D) (hi : ∀ w, compInf D.host.F D.host.E w a = 0)
    (hf : ∀ v, cv D v a = 0) : a = 0 :=
  tensor_eq_zero a hi hf

end GlobalTheory.CompanionTheory.AdeleComp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Stab

variable (R : Type) [CommRing R] [Algebra F R]

theorem actW_mul_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J (g * h) X = actW R σ J g (actW R σ J h X) := by
  funext a
  change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ X a =
    (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a)
  rw [Matrix.mulVec_mulVec]

theorem actW_one_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J 1 X = X := by
  funext a
  change (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a = X a
  exact Matrix.one_mulVec _

def stabilizer₂ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ (hypOne J)) where
  carrier := {h | actW R σ (hypOne J) h (e0 _ M) = e0 _ M}
  one_mem' := actW_one_apply R σ (hypOne J) _
  mul_mem' := by
    intro g h hg hh
    change actW R σ (hypOne J) (g * h) (e0 _ M) = e0 _ M
    rw [actW_mul_apply, show actW R σ (hypOne J) h (e0 _ M) = e0 _ M from hh]
    exact hg
  inv_mem' := by
    intro g hg
    change actW R σ (hypOne J) g⁻¹ (e0 _ M) = e0 _ M
    have hg' : actW R σ (hypOne J) g (e0 _ M) = e0 _ M := hg
    conv_lhs => rw [← hg']
    rw [← actW_mul_apply, inv_mul_cancel, actW_one_apply]

def ratP (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (stabilizer₂ R σ J) :=
  Subgroup.comap (stabilizer₂ R σ J).subtype
    (show Subgroup (HA R σ (hypOne J)) from HFinIn R σ (hypOne J))

end Stab

def framesOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    Set (Fin (n + 1) → Fin (M + 2) → E) :=
  {X | X ∈ framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) ∧ X 0 = e0 E M 0}

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_comp_bounded_fibres_le : ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.GAUnimod

theorem isMulRightInvariant_haar_GA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N _ _ μ _ => GlobalTheory.CompanionTheory.PairDom.isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.GAUnimod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplexStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_right_invariant_totally_complex : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | exact GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | (intros; apply GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA <;> assumption)
end
end
