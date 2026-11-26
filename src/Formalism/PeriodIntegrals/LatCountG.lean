module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.ScMuExists

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.LatCountG
noncomputable section

namespace PI.LatCountG

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

section Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

def coordV (x : I.GA) (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ :=
  (Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (u i))

def gramV (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) : Matrix (Fin j) (Fin j) ℂ :=
  fun a c => ∑ i, star (coordV I x v (b a) i) * coordV I x v (b c) i

structure Sub (x : I.GA) where
  j : ℕ
  j_pos : 1 ≤ j
  b : Fin j → Fin I.n → I.E
  b_ind : LinearIndependent I.E b
  B : Submodule (𝓞 I.E) (Fin I.n → I.E)
  B_lat : (B : Set (Fin I.n → I.E)) ⊆ latSet I x
  b_mem : ∀ a, b a ∈ B
  B_span : (B : Set (Fin I.n → I.E)) ⊆ Submodule.span I.E (Set.range b)

def ht {x : I.GA} (s : Sub I x) : ℝ :=
  (∏ v, (gramV I x v s.b).det.re) /
    (Nat.card (s.B ⧸ (Submodule.span (𝓞 I.E) (Set.range s.b)).comap s.B.subtype) : ℝ)

def size {x : I.GA} (s : Sub I x) : ℝ := ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))

def tau1 (x : I.GA) : ℝ := min (1 / 2) (⨅ s : Sub I x, size I s)

end Size

section Lat

variable (I : Formalism.MainNotions.S.AutInst)

def LatCount : Prop :=
  ∀ x y : I.GA, 0 < tau1 I x → 0 < tau1 I y →
    ∀ r : InfinitePlace I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset I.GFset,
      (∀ γ ∈ S, (x⁻¹ * (γ : I.GA) * y).2 ∈ I.Kset ∧ ∀ v, PI.symD (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v) ≤ r v) →
      (S.card : ℝ) ≤ (3 * Real.sqrt (I.n : ℝ) / (tau1 I x * tau1 I y)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end Lat

def LatCountAll : Prop := ∀ I : Formalism.MainNotions.S.AutInst, LatCount I

end PI.LatCountG

end
end

section -- merged from Formalism.PeriodIntegrals.AdBridgeSteps
noncomputable section

namespace PI.AdBridgeSteps

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def IsFormula (I : AutInst) (f : HAd I → I.GA) : Prop :=
  ∀ h, (∀ v, uMat ((f h).1 v) = ofHAInf I h v) ∧ I.fmat (f h).2 = ofHAFin I h

def RealK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε k →
    (kᴴ * k = 1 ↔ ∀ a b, ε a ≠ ε b → k a b = 0)

def FinK : Prop :=
  ∀ (I : AutInst) (h : HAd I),
    (∀ x, x ∈ I.Lf ↔ ofHAFin I h *ᵥ x ∈ I.Lf) ↔
      ∀ v : HeightOneSpectrum (𝓞 I.F),
        Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) ∈
          Formalism.L2.SG.Sub.Kloc v (I.L : Set (Fin I.n → I.E))

end PI.AdBridgeSteps
end
end

section -- merged from Formalism.PeriodIntegrals.EtaHostFacts
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PI.EtaHostFacts

def Unram : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1


end PI.EtaHostFacts
end
end

section -- merged from Formalism.PeriodIntegrals.ScXuExists
noncomputable section

open NumberField Formalism.MainNotions.S PI.ScRefExists
open scoped TensorProduct
open Matrix

namespace PI.ScXuExists

def OneOff (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf) : Prop :=
  ∀ m : ℕ, Nat.Coprime m g → ∀ y ∈ I.Lf, InAt I m m ((I.fmat x - 1) *ᵥ y)

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    InAt I g 1 (incl I z) →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ incl I (e a) = incl I (e a) ∧ I.fmat x *ᵥ incl I (f a) = incl I (f a)) ∧
      InAt I g g (I.fmat x⁻¹ *ᵥ incl I z - Rf.z0) ∧ OneOff I g x ∧ x ∈ I.Kset

end PI.ScXuExists
end
end

section -- merged from Formalism.PeriodIntegrals.InHHClassFin
noncomputable section

open NumberField Matrix Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.InHHClassFin

section Defs

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def HinfS (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}
  one_mem' := by
    intro v x _
    simp [uMat]
  mul_mem' := by
    intro s t hs ht v x hx
    have e1 : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
    rw [e1, ← Matrix.mulVec_mulVec, ht v x hx, hs v x hx]
  inv_mem' := by
    intro s hs v x hx
    have e1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by simp [uMat]
    calc uMat (s⁻¹ v) *ᵥ rv I v x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ rv I v x) := by rw [hs v x hx]
      _ = rv I v x := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def HfinS (S : Set (Fin I.n → I.E)) : Subgroup I.Gf where
  carrier := {x | ∀ y ∈ S, I.fmat x *ᵥ incl I y = incl I y}
  one_mem' := by
    intro y _
    simp [AutInst.fmat]
  mul_mem' := by
    intro a b ha hb y hy
    have e1 : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]
    rw [e1, ← Matrix.mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := by
    intro a ha y hy
    have e1 : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]
    calc I.fmat a⁻¹ *ᵥ incl I y = I.fmat a⁻¹ *ᵥ (I.fmat a *ᵥ incl I y) := by rw [ha y hy]
      _ = incl I y := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def GamS (S : Set (Fin I.n → I.E)) : Subgroup I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF I ⊓ (HinfS I S).prod (HfinS I S)

def iotaFS (S : Set (Fin I.n → I.E)) : GamS I S →* HfinS I S :=
  MonoidHom.codRestrict ((MonoidHom.snd _ _).comp (GamS I S).subtype) (HfinS I S)
    (fun γ => (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2)

end Defs

def DefiniteCompl (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) : Prop :=
  ∀ ι : I.F →+* ℝ,
    (∀ x : Fin I.n → I.E, x ≠ 0 → (∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s x = 0) →
      ∃ a : I.F, algebraMap I.F I.E a = Formalism.UG.hform (starRingEnd I.E) I.J x x ∧ 0 < ι a) ∨
    (∀ x : Fin I.n → I.E, x ≠ 0 → (∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s x = 0) →
      ∃ a : I.F, algebraMap I.F I.E a = Formalism.UG.hform (starRingEnd I.E) I.J x x ∧ ι a < 0)

def StabClassFinite : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S →
    ∀ (K : Subgroup (HfinS I S)) (g : ℕ) (x : I.Gf), 1 ≤ g →
      (∀ h : HfinS I S, x⁻¹ * (h : I.Gf) * x ∈ I.Kg g → h ∈ K) →
      Finite (Formalism.UG.ClassSet (iotaFS I S).range K)

end PI.InHHClassFin
end
end
