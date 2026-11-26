module

public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

def SiteAdm (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) (Lv : Levels Fl) (Ch : Chain Lv) : Prop :=
  ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : ℕ → ℕ)
    (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) Fl Lv Ch std vp unif eO eO_spec dG dG_spec om)),
    FormalGroupSystem.admitted D _ Y5 ∧ dG 0 = 0 ∧ ∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam

def phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    sub2 p be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩))

def IsPlaceCofactorValuationLowerBound {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) (g : ℝ) : Prop :=
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p), IntS p (inParam p U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), ∃ a : WW p,
      AddMonoidAlgebra.coeff (applyD (X.PIv j I v) (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U))) n =
        (p : K0 p) ^ ⌈g⌉ * algebraMap (WW p) (K0 p) a

def inE {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕ Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) →
      X.EA j ⊕ X.EA j :=
  Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j))

def thOne {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (K0 p))
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)) : MvPowerSeries (Zidx n' r0 r1) (K0 p) :=
  ThZ B (K0 p) 1 (expS p (-(∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)))) * U)

def toFin {n : ℕ} [NeZero n] (s : ZMod n) : Fin n := ⟨s.val, ZMod.val_lt s⟩

def inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries (ZMod n × Fin r0 × Fin r1) R :=
  resV (fun x => (toFin x.1, x.2)) f

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS phFF NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog at1 lgF)

namespace GlobalTheory.KerStd

def CurveData (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

def HostLog (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Formalism.DworkPowerSeriesWeights.Integral
    (Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l]) *
      (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l]))

abbrev HypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n] (f f' : E → n → K) : Prop :=
  Formalism.L2.Th1.Top.IsHypPair σ f f'

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

def HostAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    ‖c‖ = 1 ∧ CurveData p g2 g3 s2 ε σ F ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b ∧ TaylorLogMetric.Orthonormal D b ∧
        ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HostLog p g2 g3 s2 ε (thOrth D lam c b G)

theorem HostLog.iff_phSum (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) :
    HostLog l g2 g3 s2 ε Θ ↔ Formalism.DworkPowerSeriesWeights.Integral
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
        (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l])) :=
  Iff.rfl

theorem HostLog.constantCoeff_subst {K σ τ : Type} [Field K] [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f : MvPowerSeries τ K) = MvPowerSeries.constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have e : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) + MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by ring
  conv_lhs => rw [e]
  rw [MvPowerSeries.subst_add hs, map_add (f := _), MvPowerSeries.constantCoeff_subst_eq_zero hs ha (by simp), zero_add,
    MvPowerSeries.subst_C]
  simp

end GlobalTheory.KerStd
end
end
