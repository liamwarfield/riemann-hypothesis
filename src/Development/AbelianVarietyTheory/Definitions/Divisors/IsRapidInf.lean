module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import GroundTheory.AutomorphicForms.FourierWhittaker
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
noncomputable section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def whit (F : GA E a → ℂ) (g : GA E a) : ℂ := GroundTheory.Automorphic.FourierWhittaker.whittaker F g


variable (E a) in
def NA : Set (GA E a) :=
  {u | (∀ i j : Fin a, j < i → (u : Matrix (Fin a) (Fin a) (Ad E)) i j = 0) ∧ ∀ i, (u : Matrix (Fin a) (Fin a) (Ad E)) i i = 1}

def psiN (u : GA E a) : ℂ := (GroundTheory.Global.adelicChar E (GlobalTheory.Whittaker.superDiag u) : ℂ)


variable (E a) in
def supS (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E a) :=
  {g | ∀ w ∉ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1}


variable (E) in
def mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : Set (GA E (m + 1)) :=
  supS E (m + 1) S ∩ {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = if j = Fin.last m then 1 else 0}

def diagPow {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) : GL (Fin n) K :=
  Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)

def tl (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) : GA E a :=
  (l.support.toList.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod

def IsRapidInf {X : Type} [MeasurableSpace X] (ν : MeasureTheory.Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : Prop :=
  Measurable k ∧ Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
    ∀ N : ℕ, MeasureTheory.Integrable (fun x => ‖k x‖ * height (γ x) ^ N) ν

def mspanR [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    ∀ F ∈ S, ∀ (X : Type) (_ : MeasurableSpace X) (ν : MeasureTheory.Measure X) (_ : MeasureTheory.SFinite ν) (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ S}

def psiLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E (sLoc E w x)) : ℂ)

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
noncomputable section

open Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM.SplitModel

variable {K : Type} [Field K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable [Invertible (2 : K)]





variable [Fintype K]

variable [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K]





end GlobalTheory.WeilM.SplitModel

namespace GlobalTheory.WeilM.SplitModel

end GlobalTheory.WeilM.SplitModel

end

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : R)]


omit [DecidableEq α] in
theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

end Alg

section Forms

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




end Forms

section RankZero

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]


variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology R E] {C : TestClass R}



end RankZero


end GlobalTheory.WeilM.SiegelModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
noncomputable section

namespace GlobalTheory.ColRows

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

structure KerTies (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) : Prop where
  host : HostTie (ofRecord D L Del h0) t.seam t.Pr
  wts : ∃ pl : RPl D.R ≃ t.X.Tau, ∀ u, WeightTie (ofRecord D L Del h0) W pl (t.word u) (letterOf D L Del h0 u)
  chr : CharTie (ofRecord D L Del h0) t.seam W t.Ch t.glob t.sel
  an : AnalyticTie D t.δ t.χ t.cD
  mu0 : t.tup D.what₂.mu0 = 1
  sharp : (t.cst D.what₂.mu0).sharp = true
  m2 : t.m2 = D.R.m - 2
  fld : ∀ u, FieldOfDefinition W t.sel (t.tup D.what₂.mu0) (t.cst D.what₂.mu0) (t.word u) t.amb

structure KerSizes (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (CY CT : ℝ) : Prop where
  sizes : Sizes t.Pr W L.sc.a
  what₂ : ∀ u, GlobalTheory.Core.Ht2.SizeRowsS CY (ofRecord D L Del h0) (letterOf D L Del h0 u)
  logT : ∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * L.sc.L

end GlobalTheory.ColRows

end
end
