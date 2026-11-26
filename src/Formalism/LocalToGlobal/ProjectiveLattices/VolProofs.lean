module

public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7}

def VolPairEx (V : HSp D) : Prop := ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2

theorem volPair_eq_choose (V : HSp D) (h : VolPairEx V) : volPair V = h.choose := by
  unfold volPair
  exact dif_pos h

theorem volPair_isVolPair (V : HSp D) (h : VolPairEx V) : IsVolPair D V (volPair V).1 (volPair V).2 := by
  rw [volPair_eq_choose V h]
  exact h.choose_spec

theorem autMk_measurable (V : HSp D) : Measurable (autMk V) := by
  first
  | exact measurable_quotient_mk'
  | exact fun _ hs => hs

theorem muQ_univ (V : HSp D) : muQ V Set.univ = (volPair V).1 (volPair V).2 := by
  unfold muQ
  rw [Measure.map_apply (autMk_measurable V) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

instance instCMHost (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

def InR (D : D7) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

structure Par (D : D7) : Type 1 where
  H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E
  l : Level H
  c : Coeff l
  Dw : ℕ → Datum H
  Xo : ∀ j, Moduli (Dw j) l
  eO : 𝓞 c.F ≃+* D.what₂.O

variable {D : D7}

def IsDatW (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (j : ℕ) (Dw : Datum H) : Prop :=
  letI := D.host.cmStar
  Dw.p = (D.R.sigW j).1 ∧ Dw.q = (D.R.sigW j).2 ∧
  ∃ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ ∧
    LinearMap.range φ = Submodule.span (𝓞 D.host.E)
      {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ (D.sp.W j).L0, v = a • x} ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))

namespace Par

variable (Q : Par D)

def PinHost : Prop :=
  Q.H.d = D.host.d ∧ (Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ Q.H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0

def PinLevel : Prop := Q.l.M = D.host.g 0 * D.host.g 1 ∧ Q.l.A = 1

def PinField : Prop := ∀ x : 𝓞 Q.c.F, D.what₂.embLL (D.what₂.OtoLL (Q.eO x)) = ((x : Q.c.F) : ℂ)

def PinDat : Prop := ∀ j, InR D j → IsDatW D j (Q.Dw j)

def Pins : Prop := Q.PinHost ∧ Q.PinLevel ∧ Q.PinField ∧ Q.PinDat

end Par

def ext0 {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : ℕ := if h : i < p then f ⟨i, h⟩ else 0

theorem matrixExtendByZero_add {p : ℕ} (f g : Fin p → ℕ) (i : ℕ) : ext0 (fun k => f k + g k) i = ext0 f i + ext0 g i := by
  unfold ext0; split_ifs <;> rfl

theorem partitionExtendByZero_antitone {p : ℕ} {f : Fin p → ℕ} (hf : Antitone f) : Antitone (ext0 f) := by
  intro i k hik
  unfold ext0
  by_cases hk : k < p
  · rw [dite_eq_left hk, dite_eq_left (lt_of_le_of_lt hik hk)]; exact hf hik
  · rw [dite_eq_right hk]; exact Nat.zero_le _


open Classical in
def wtA {j : ℕ} (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t then ext0 (w.aP t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) then ext0 (w.aM t) x.2 else 0)

theorem wtA_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
  funext x
  simp only [wtA, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wadd w w').aP t) x.2 = ext0 (w.aP t) x.2 + ext0 (w'.aP t) x.2 := matrixExtendByZero_add _ _ _
  have h2 : ext0 ((WeightAlgebra.wadd w w').aM t) x.2 = ext0 (w.aM t) x.2 + ext0 (w'.aM t) x.2 := matrixExtendByZero_add _ _ _
  rw [h1, h2]
  split_ifs <;> omega

theorem n_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl

theorem dom_wtA {j : ℕ} (w : WeightFamilies.Wt D j) : Dom (wtA w) w.n := by
  refine ⟨fun τ i k hik => ?_, w.n_even⟩
  simp only [wtA]
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hik
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hik
    · exact le_rfl

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

structure Unf (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) : Type 1 where

  Comp : Type
  [fin : Fintype Comp]

  X : Comp → Data E r

  un : ∀ k, (X k).dom → FrPt Xo c (CAt σ)

attribute [instance] Unf.fin

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def gxFst {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Xo.univ.t.G.left :=
  (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left

def gxSnd {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Gx x ⟶ Sp S :=
  (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left

def toC {K : Type} [Field K] {σ : K →+* ℂ} (z : CAt σ) : ℂ := z


open Classical in
def rdU (U : Unf Xo c σ r) : Rul Xo c →ₛₗ[σ] FDSec U.X where
  toFun f := fun k x => if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0
  map_add' f g := by
    funext k x
    simp only [Pi.add_apply]
    split_ifs with h
    · have e := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
      exact e
    · simp
  map_smul' a f := by
    funext k x
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (U.un k ⟨x, h⟩)
      exact e
    · simp

def relab (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) : E →+* ℂ := σ.comp (embF c τ)

def GoodEmb (c : Coeff l) (σ : c.F →+* ℂ) : Prop :=
  (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0


open Classical in
def laU (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
    else -(a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ)


open Classical in
def perFr (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) : ℂ :=
  if h : τ ∈ X.Ψ then
    (if hi : X.p0 + i < r then ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ v)) ⟨X.p0 + i, hi⟩ else 0)
  else if h' : conjEmb τ ∈ X.Ψ then
    (if hj : X.p0 - 1 - i < r then
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, hj⟩) (Data.emb (conjEmb τ) v) else 0)
  else 0

def IsUnf (U : Unf Xo c σ r) : Prop :=
  r = Dw.p + Dw.q ∧ (∀ k, (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) ∧
    (∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y) ∧
    (∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom), (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) (U.un k' x')) ↔
      ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (U.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩) ∧
    (∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, (U.X k).IsSec (laU U a n k) (rdU U f k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ),
      (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
      ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          ((U.un k x).u τ i)) ∧
        ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HostSize
noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.I2

variable {D : D7}

theorem hostSize_finrank (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  first
  | ring
  | rfl
  | omega
  | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)

theorem hostSize_f (D : D7) : PT.f D.host.E = D.R.f := by
  simp only [ReciprocityTheory.ChartRestriction.G.I2.PT.f, hostSize_finrank D]
  omega

theorem hostSize_rd (D : D7) : PT.rd D.host.E = D.host.rdE := rfl

theorem hostSize_n_sqrt_le (D : D7) :
    Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem hostSize_sqrt_gt {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) :
    ((D.R.f : ℝ) + 6) ^ 2 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hfk := D.R.f_le_k
  have hm := D.R.two_le_m
  have hmf := D.R.m_le_f
  have ht := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 : D.R.f + 6 ≤ D.R.t := by omega
  have h2 : D.R.f + 6 ≤ 4 * D.R.r := by omega
  have key : (D.R.f + 6) ^ 2 < 4 * D.R.t * D.R.r + 1 := by
    have := Nat.mul_le_mul h1 h2
    nlinarith
  have keyR : ((D.R.f : ℝ) + 6) ^ 2 < ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := by exact_mod_cast key
  have hA : (0 : ℝ) ≤ ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.q : ℝ) := by exact_mod_cast hq
  have hdR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.d : ℝ) := by exact_mod_cast hd
  have hsq : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.lt_sqrt hA]
    nlinarith
  linarith

theorem host_f_sq_le_rd {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : (PT.f D.host.E : ℝ) ^ 2 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_f D, hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_rd_ge_sixteen {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : 16 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_m_pow_four_le_f {large₂ : SizeData₂ D} (hS : SizesAt large₂) : D.R.m ^ 4 ≤ PT.f D.host.E := by
  have hx : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hx0 : 0 < large₂.sc.x := by linarith
  have he : 0 < large₂.sc.eps := large₂.sc.eps_pos
  obtain ⟨⟨hN1, -⟩, ⟨-, hM2⟩, -⟩ := hS
  simp only [Formalism.MainNotions.szTh, Formalism.BasicNotions.Scale.delta1] at hN1 hM2
  have hA : Real.sqrt (large₂.sc.x * large₂.sc.x ^ (-(large₂.sc.eps / 8))) =
      large₂.sc.x ^ ((1 + -(large₂.sc.eps / 8)) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
  rw [hA, ← Real.rpow_add hx0] at hM2
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have h4 : (D.R.m : ℝ) ^ 4 ≤ (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 :=
    pow_le_pow_left₀ hm0 hM2 4
  have h5 : (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 =
      large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h6 : large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) ≤
      large₂.sc.x ^ (2 + 8 * large₂.sc.eps - large₂.sc.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have key : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ (D.R.n : ℝ) := by
    push_cast
    linarith
  have hmn : D.R.m ^ 4 ≤ D.R.n := by exact_mod_cast key
  have hn : D.R.n = D.R.ord := rfl
  rw [hostSize_f D, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  omega

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PtExt (X : PJ D B P j) where
  Pt' : HeightOneSpectrum (𝓞 B.KO) → Type
  extendedPointBaseChange : ∀ la, Pt' la → (P.loc X.dat (resCh la)).Pt (P.loc X.dat (resCh la)).YY
  vAt' : ∀ la, Pt' la → X.Forms → EReal
  vAt'_zero : ∀ la y, vAt' la y 0 = ⊤
  vAt'_ne_bot : ∀ la y F, vAt' la y F ≠ ⊥
  vAt'_add : ∀ la y F G, min (vAt' la y F) (vAt' la y G) ≤ vAt' la y (F + G)
  vAt'_smul : ∀ la y (a : B.KO) F, a ≠ 0 →
    vAt' la y (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAt' la y F
  vAt'_mul : ∀ la y w w' (F : B.Cusp j w) (G : B.Cusp j w'),
    vAt' la y (X.inc w F * X.inc w' G) = vAt' la y (X.inc w F) + vAt' la y (X.inc w' G)

def IntAtExt (X : PJ D B P j) (E : PtExt X) : Prop :=
  ∀ w (F : B.Cusp j w), F ∈ B.Mlat j w → ∀ la (y : E.Pt' la), 0 ≤ E.vAt' la y (X.inc w F)

def xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D B P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt la := X.Pt la ⊕ E.Pt' la
  pt66 la := Sum.elim (X.pt66 la) (E.extendedPointBaseChange la)
  vAt la := Sum.elim (X.vAt la) (E.vAt' la)
  vAt_zero la
    | .inl y => X.vAt_zero la y
    | .inr y => E.vAt'_zero la y
  vAt_ne_bot la
    | .inl y => X.vAt_ne_bot la y
    | .inr y => E.vAt'_ne_bot la y
  vAt_add la
    | .inl y => X.vAt_add la y
    | .inr y => E.vAt'_add la y
  vAt_smul la
    | .inl y => X.vAt_smul la y
    | .inr y => E.vAt'_smul la y
  vAt_mul la
    | .inl y => X.vAt_mul la y
    | .inr y => E.vAt'_mul la y
  Mlat_eq w F :=
    ⟨fun h la y => match y with
      | .inl y => (X.Mlat_eq w F).1 h la y
      | .inr y => hM w F h la y,
     fun h => (X.Mlat_eq w F).2 fun la y => h la (.inl y)⟩
  thAll := X.thAll
  shortTh := X.shortTh

section xplus

variable (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)

end xplus

abbrev withNorm (B : WeightFamilies.Prov D) (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F) : WeightFamilies.Prov D :=
  { B with l2NormAlt := N, l2Norm_nonneg_bis := h0, l2Norm_eq_zero_iff := h1, l2Norm_smul_alt := h2, l2Norm_add_le' := h3, l2Norm_le_supNorm_alt := h4 }

section tol2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def PJ.tol2NormAlt (X : PJ D B P j) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt := X.Pt
  pt66 := X.pt66
  vAt := X.vAt
  vAt_zero := X.vAt_zero
  vAt_ne_bot := X.vAt_ne_bot
  vAt_add := X.vAt_add
  vAt_smul := X.vAt_smul
  vAt_mul := X.vAt_mul
  Mlat_eq := X.Mlat_eq
  thAll := X.thAll
  shortTh := X.shortTh

def scalarsWithNorm (S : Scal B) : Scal (withNorm B N h0 h1 h2 h3 h4) := ⟨S.sW, S.sF, S.s0, S.sK⟩

def xplusN (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j :=
  PJ.tol2NormAlt N h0 h1 h2 h3 h4 (xplus X E hM)

end tol2NormAlt

section Transfer

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)


theorem concl_xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) :
    Concl (xplus X E hM) S ka wL wF T nus β ↔ Concl X S ka wL wF T nus β := Iff.rfl

end Transfer

section On

variable (cov : ∀ j, WeightFamilies.Wt D j → Prop) (Nn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)


open Classical in
def l2nOn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ :=
  fun j ka σ F => if cov j ka then Nn j ka σ F else B.supN j ka σ F

variable {cov Nn}
variable (h0 : ∀ j ka, cov j ka → ∀ σ F, 0 ≤ Nn j ka σ F)
    (h1 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka, cov j ka → ∀ σ (a : B.KO) F, Nn j ka σ (a • F) = ‖σ a‖ * Nn j ka σ F)
    (h3 : ∀ j ka, cov j ka → ∀ σ F G, Nn j ka σ (F + G) ≤ Nn j ka σ F + Nn j ka σ G)
    (h4 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F ≤ B.supN j ka σ F)

include h0 in
theorem l2nOn_nonneg : ∀ j ka σ F, 0 ≤ l2nOn cov Nn j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h0 j ka h σ F
  · exact B.supN_nonneg j ka σ F

include h1 in
theorem l2nOn_eq_zero : ∀ j ka σ F, l2nOn cov Nn j ka σ F = 0 ↔ F = 0 := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h1 j ka h σ F
  · exact B.supN_eq_zero j ka σ F

include h2 in
theorem l2nOn_smul : ∀ j ka σ (a : B.KO) F, l2nOn cov Nn j ka σ (a • F) = ‖σ a‖ * l2nOn cov Nn j ka σ F :=
  fun j ka σ a F => by
  unfold l2nOn; split_ifs with h
  · exact h2 j ka h σ a F
  · exact B.supN_smul j ka σ a F

include h3 in
theorem l2nOn_add : ∀ j ka σ F G, l2nOn cov Nn j ka σ (F + G) ≤ l2nOn cov Nn j ka σ F + l2nOn cov Nn j ka σ G :=
  fun j ka σ F G => by
  unfold l2nOn; split_ifs with h
  · exact h3 j ka h σ F G
  · exact B.supN_add j ka σ F G

include h4 in
theorem l2nOn_le : ∀ j ka σ F, l2nOn cov Nn j ka σ F ≤ B.supN j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h4 j ka h σ F
  · exact le_rfl

abbrev withNormOnWeights : WeightFamilies.Prov D :=
  withNorm B (l2nOn cov Nn) (l2nOn_nonneg h0) (l2nOn_eq_zero h1) (l2nOn_smul h2) (l2nOn_add h3) (l2nOn_le h4)

end On

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def N3AtPoints (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C), Nonempty (DatAt Y P)

def BetaAdd (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (a a' b : A.Ylat),
    A.beta (a + a') b = A.beta a b + A.beta a' b

def BetaBal (Y : Model Xo c β) (p : ℕ) (cj : E → E) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (x x' : 𝓞 E), (x' : E) = cj (x : E) →
    ∀ a b : A.Ylat, A.beta (x • a) b = A.beta a (x' • b)

def BetaPosDef (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P),
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem beta_add_right (hA : BetaAdd Y p) (A : DatAt Y P) (a b b' : A.Ylat) :
    A.beta a (b + b') = A.beta a b + A.beta a b' := by
  rw [A.beta_symm, hA C P A, A.beta_symm b, A.beta_symm b']

def beLin (hA : BetaAdd Y p) (A : DatAt Y P) : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => A.beta a b)
      (fun b b' => A.beta_add_right hA a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [hA C P A a a' b])).toIntLinearMap

theorem beLin_apply (hA : BetaAdd Y p) (A : DatAt Y P) (a b : A.Ylat) : A.beLin hA a b = A.beta a b := rfl

end DatAt

end Formalism.L2.Pj
end
end
