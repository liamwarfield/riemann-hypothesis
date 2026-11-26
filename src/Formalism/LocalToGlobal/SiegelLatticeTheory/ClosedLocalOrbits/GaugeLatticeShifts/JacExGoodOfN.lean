module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def coordSc (r : ℕ) (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : Fin (r + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (fun a : Fin r => (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2 * q.1 a) q.2

def psiP {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (u : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => (P⁻¹ * uMat u * P) i j

def PFrame : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' →
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r ∧ IsUnit P.det ∧
      (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) ∧
      ∃ zH zH' : Fin (2 * r + k + 1) → ℂ, Formalism.QuantumDeterminants.inWb k r zH ∧ Formalism.QuantumDeterminants.inWb k r zH' ∧
        P *ᵥ zH = z ∧ P *ᵥ zH' = z' ∧ Formalism.QuantumDeterminants.Tz k r zH = T ∧ Formalism.QuantumDeterminants.Tz k r zH' = T'

def SetCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH →
    ∀ u : Formalism.REAL.UJ ε, u ∈ SLoc ε e z ↔ P⁻¹ * uMat u * P ∈ Formalism.QuantumDeterminants.Sset k r zH

def HaarCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH → 1 ≤ k →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (psiP P)) ∧
    ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r zH) μW →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
      ∀ μS : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS →
        ∃ c : ℝ, 0 < c ∧ μS.map (psiP P) = ENNReal.ofReal c • Formalism.MainNotions.S.muS μW μN

def ZBig : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ)
    (z z' zH zH' : Fin (2 * r + k + 1) → ℂ) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (sc : ℝ),
    Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r → IsUnit P.det → (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) →
    Formalism.QuantumDeterminants.inWb k r zH → Formalism.QuantumDeterminants.inWb k r zH' → P *ᵥ zH = z → P *ᵥ zH' = z' → 0 < sc →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r zH zH' μsec →
    ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq q.2 →
      Formalism.REAL.inUJ ε (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) ∧
      Zhat ε (famSc sc e z) (famSc sc e z') (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) =
        Matrix.diagonal (coordSc r sc q)

def BigMem : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

def CoordW : Prop :=
  ∀ (r k : ℕ) (T T' sc : ℝ), 1 ≤ k → 0 < T → 0 < T' → 0 < sc →
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : (Fin (r + 1) → ℂ) → ℝ≥0∞,
      ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
        ENNReal.ofReal κ * ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))

def SecWb : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' → ∃ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec

def JacExGoodN : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' sc : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

theorem jacExGood_of_N (H : JacExGoodN) : JacExGood := by
  intro n r k ε e z z' T T' sc hF hG hsc
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  exact H r k ε e z z' T T' sc hF hG hsc

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormSqLine
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} (ε : Fin n → Bool)

structure Frm (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0
  pp : ∀ a b, hJ ε (p a) (p b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  pz : ∀ a, hJ ε (p a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ew : ∀ a j, hJ ε (e a) (w j) = 0
  pw : ∀ a j, hJ ε (p a) (w j) = 0
  zw : ∀ j, hJ ε z (w j) = 0
  ww : ∀ i j, hJ ε (w i) (w j) = if i = j then 1 else 0
  T_ne : T ≠ 0

variable {ε}

theorem hJ_swap0 {x y : Fin n → ℂ} (h : hJ ε x y = 0) : hJ ε y x = 0 := by
  rw [UnitaryIsometries.hJ_conj, h, map_zero]

theorem hJ_swapδ {ι : Type*} [DecidableEq ι] {x y : ι → Fin n → ℂ} (h : ∀ a b, hJ ε (x a) (y b) = if a = b then 1 else 0)
    (a b : ι) : hJ ε (y b) (x a) = if a = b then 1 else 0 := by
  rw [UnitaryIsometries.hJ_conj, h]
  split_ifs <;> simp

def syn (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ)
    (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) : Fin n → ℂ :=
  ∑ a, α a • e a + ∑ a, β a • p a + (-γ / (T : ℂ)) • z + ∑ j, δ j • w j

section Coord

variable {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ} {T : ℝ}

theorem hJ_syn (x : Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε x (syn e p z w T α β γ δ) = ∑ a, α a * hJ ε x (e a) + ∑ a, β a * hJ ε x (p a) +
      (-γ / (T : ℂ)) * hJ ε x z + ∑ j, δ j * hJ ε x (w j) := by
  simp only [syn, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_sum_right]

theorem syn_p (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (p c) (syn e p z w T α β γ δ) = α c := by
  rw [hJ_syn]
  simp [hJ_swapδ F.ep, F.pp, F.pz, F.pw]

theorem syn_e (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (e c) (syn e p z w T α β γ δ) = β c := by
  rw [hJ_syn]
  simp [F.ee, F.ep, F.ez, F.ew]

theorem synthesized_vector_z_pairing (F : Frm ε e p z w T) α β γ δ : hJ ε z (syn e p z w T α β γ δ) = γ := by
  rw [hJ_syn]
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F.T_ne
  simp only [fun a => hJ_swap0 (F.ez a), fun a => hJ_swap0 (F.pz a), F.zz, F.zw, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  field_simp

theorem syn_w (F : Frm ε e p z w T) (c : Fin k) α β γ δ : hJ ε (w c) (syn e p z w T α β γ δ) = δ c := by
  rw [hJ_syn]
  simp [fun a => hJ_swap0 (F.ew a c), fun a => hJ_swap0 (F.pw a c), hJ_swap0 (F.zw c), F.ww]

def crd (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ) :=
  (LinearMap.pi fun a => hJL ε (p a)).prod ((LinearMap.pi fun a => hJL ε (e a)).prod
    ((hJL ε z).prod (LinearMap.pi fun j => hJL ε (w j))))

theorem crd_syn (F : Frm ε e p z w T) α β γ δ :
    crd (ε := ε) e p z w (syn e p z w T α β γ δ) = (α, β, γ, δ) := by
  ext c
  · exact syn_p F c α β γ δ
  · exact syn_e F c α β γ δ
  · exact synthesized_vector_z_pairing F α β γ δ
  · exact syn_w F c α β γ δ

theorem recon (F : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) (v : Fin n → ℂ) :
    v = syn e p z w T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  have hsurj : Function.Surjective (crd (ε := ε) e p z w) := fun c =>
    ⟨syn e p z w T c.1 c.2.1 c.2.2.1 c.2.2.2, crd_syn F _ _ _ _⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  apply hinj
  rw [crd_syn F]
  rfl

end Coord

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem uMat_inv_mul (g : UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  show (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

theorem uMat_mul_inv (g : UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  show _ * (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_mul (g h : UJ ε) : Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem inv_fix {g : UJ ε} {v : Fin n → ℂ} (h : Formalism.MainNotions.S.uMat g *ᵥ v = v) : Formalism.MainNotions.S.uMat g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [mulVec_mulVec, uMat_inv_mul, one_mulVec]

theorem fix_span {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ a, g *ᵥ e a = e a) (a : ℕ) :
    ∀ x ∈ spanLt e a, g *ᵥ x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact hg b
  | zero => exact mulVec_zero _
  | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
  | smul c x _ hx => rw [mulVec_smul, hx]

theorem InN_one : InN ε e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨UnitaryIsometries.RI.inS_one e z, fun y _ => by rw [sub_self, zero_mulVec]; exact Submodule.zero_mem _⟩

theorem InN_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) (hh : InN ε e z h) : InN ε e z (g * h) := by
  refine ⟨UnitaryIsometries.RI.inS_mul e z hg.1 hh.1, fun y hy => ?_⟩
  have key : (g * h - 1) *ᵥ y = g *ᵥ ((h - 1) *ᵥ y) + (g - 1) *ᵥ y := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [key]
  exact Submodule.add_mem _ (UnitaryIsometries.RI.inS_pres e z hg.1 r _ (hh.2 y hy)) (hg.2 y hy)

def NG : Subgroup (UJ ε) where
  carrier := NLoc ε e z
  one_mem' := InN_one ε e z
  mul_mem' {g h} hg hh := InN_mul ε e z hg hh
  inv_mem' {g} hg := by
    have hS : g⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
    refine ⟨hS, fun y hy => ?_⟩
    have key : (Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ y = -(Formalism.MainNotions.S.uMat g⁻¹ *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ y)) := by
      rw [mulVec_mulVec, Matrix.mul_sub, uMat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec]
      abel
    rw [key]
    exact Submodule.neg_mem _ (UnitaryIsometries.RI.inS_pres e z hS r _ (hg.2 y hy))

def HG : Subgroup (UJ ε) where
  carrier := HLoc ε e p z
  one_mem' := ⟨fun a => one_mulVec _, fun a => one_mulVec _, one_mulVec _⟩
  mul_mem' {g h} hg hh := ⟨fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.1 a, hg.1 a],
    fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.2.1 a, hg.2.1 a],
    by rw [uMat_mul, ← mulVec_mulVec, hh.2.2, hg.2.2]⟩
  inv_mem' {g} hg := ⟨fun a => inv_fix ε (hg.1 a), fun a => inv_fix ε (hg.2.1 a), inv_fix ε hg.2.2⟩

theorem coe_NG : (NG ε e z : Set (UJ ε)) = NLoc ε e z := rfl

theorem coe_HG : (HG ε e p z : Set (UJ ε)) = HLoc ε e p z := rfl

theorem NG_closed : IsClosed (NG ε e z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((UnitaryIsometries.RI.continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (NG ε e z : Set (UJ ε)) = (UnitaryIsometries.RI.SG ε e z : Set (UJ ε)) ∩
      ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0},
        (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ y) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_NG, NLoc, InN, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
    rfl
  rw [e1]
  exact (UnitaryIsometries.RI.SG_closed ε e z).inter (isClosed_biInter fun y _ =>
    (Submodule.closed_of_finiteDimensional _).preimage (hc y))

theorem HG_closed : IsClosed (HG ε e p z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => Formalism.MainNotions.S.uMat g *ᵥ v) := fun v =>
    (UnitaryIsometries.RI.continuous_uMat ε).matrix_mulVec continuous_const
  have e1 : (HG ε e p z : Set (UJ ε)) = (⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ e a = e a}) ∩
      ((⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ p a = p a}) ∩ {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ z = z}) := by
    ext g
    simp only [coe_HG, HLoc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e1]
  exact (isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const))

theorem NG_le_SG : NG ε e z ≤ UnitaryIsometries.RI.SG ε e z := fun _ hg => hg.1

theorem HG_le_SG : HG ε e p z ≤ UnitaryIsometries.RI.SG ε e z := by
  intro g hg
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, one_mulVec, hg.1 a, sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, one_mulVec, hg.2.2, sub_self]
    exact Submodule.zero_mem _

theorem conj_mem {h g : UJ ε} (hh : h ∈ HG ε e p z) (hg : g ∈ NG ε e z) : h * g * h⁻¹ ∈ NG ε e z := by
  have hfix : ∀ a, Formalism.MainNotions.S.uMat h *ᵥ e a = e a := hh.1
  have hfix' : ∀ a, Formalism.MainNotions.S.uMat h⁻¹ *ᵥ e a = e a := fun a => inv_fix ε (hh.1 a)
  have key : ∀ v, (Formalism.MainNotions.S.uMat (h * g * h⁻¹) - 1) *ᵥ v =
      Formalism.MainNotions.S.uMat h *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ v)) := by
    intro v
    rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      uMat_mul_inv, Matrix.sub_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, hfix', fix_span e hfix a.1 _ (hg.1.1 a)]
    exact hg.1.1 a
  · rw [key, inv_fix ε hh.2.2, fix_span e hfix r _ hg.1.2]
    exact hg.1.2
  · have hy' : ∀ a, hJ ε (e a) (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ y) = 0 := by
      intro a
      rw [← hfix' a, UnitaryIsometries.isIsom_uMat ε h⁻¹, hy a]
    rw [key, fix_span e hfix r _ (hg.2 _ hy')]
    exact hg.2 _ hy'

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem lieE_G : Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL := by
  have h : Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = ((uH k r : Submodule ℝ (Mat k r)) : Set (Mat k r)) := BH.lieG k r
  unfold Formalism.MainNotions.S.lieE
  rw [h]
  change Submodule.span ℝ (⇑(RL (k := k) (r := r)) '' ↑(uH k r)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem lieG' : LieG := fun k r => lieE_G

theorem mulVec_bvec (X : Mat k r) (j i : Fin (2 * r + k + 1)) : (X *ᵥ bvec j) i = X i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]

theorem mid_or (j : Fin (2 * r + k + 1)) (h : ¬ Mid k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) := by
  simp only [Mid, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨2 * r + k - j, by omega⟩, Fin.ext ?_⟩
    have hj := j.isLt
    show (j : ℕ) = 2 * r + k - (2 * r + k - j)
    omega

private theorem mul_hpk_apply_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  rw [Matrix.mul_apply]
  simp_rw [Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row]
  rw [Finset.sum_eq_single (tau k r j)]
  · rw [tau_tau, if_pos rfl, sgn_tau]
  · intro m _ hm
    rw [if_neg (fun h => hm (by rw [h, tau_tau])), mul_zero]
  · simp

private theorem adjH_apply_lemma_2 (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Xᴴ * Hpk k r) i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  rw [mul_hpk_apply_lemma, Formalism.QuantumDeterminants.WeylGroupFacts.hpk_mul_apply, Matrix.conjTranspose_apply]

theorem lieWb_set : Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r : Set (Mat k r)) := by
  rw [BH.lieWb k r]
  ext X
  change _ ↔ (adjH X + X = 0 ∧ ∀ i j, ¬(Mid k r i ∧ Mid k r j) → X i j = 0)
  rw [adjH_def]
  constructor
  · rintro ⟨hX, hc⟩
    have hcol : ∀ i j, ¬ Mid k r j → X i j = 0 := by
      intro i j hj
      rcases mid_or j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [← mulVec_bvec X (eI k r a) i, (hc a).1]; rfl
      · rw [← mulVec_bvec X (esI k r a) i, (hc a).2]; rfl
    refine ⟨hX, fun i j hij => ?_⟩
    rcases not_and_or.1 hij with hi | hj
    · have h := congrFun (congrFun hX i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      rw [adjH_apply_lemma_2] at h
      have htau : ¬ Mid k r (tau k r i) := by
        have := tau_out i (by simp only [Mid, not_and_or, not_le] at hi; exact hi)
        simp only [Mid, not_and_or, not_le]; exact this
      rw [hcol _ _ htau, star_zero, mul_zero, zero_mul, zero_add] at h
      exact h
    · exact hcol i j hj
  · rintro ⟨hX, hz⟩
    refine ⟨hX, fun a => ⟨?_, ?_⟩⟩
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h1 : r ≤ (a : ℕ) := h.2.1
      have := a.isLt
      omega
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h2 : 2 * r + k - (a : ℕ) ≤ r + k := h.2.2
      have := a.isLt
      omega

theorem lieWb' : LieWb := by
  intro k r
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have h : Z ∈ Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) := by rw [lieWb_set]; exact hZ
    simpa using h 1
  · unfold Formalism.MainNotions.S.lieE
    rw [lieWb_set]
    have : (fun X => (WithLp.equiv 2 _).symm (Formalism.MainNotions.S.realifyFun X)) '' (uWb k r : Set (Mat k r)) =
        (RL : Mat k r → _) '' (uWb k r : Set (Mat k r)) := rfl
    rw [this, Submodule.span_image, Submodule.span_eq]

def prodEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_prodS {R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) [FiniteDimensional R p] [FiniteDimensional R q] :
    Module.finrank R ↥(p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

private theorem eq_zero_of_RL_lemma_3 (M : Mat k r) (h : ‖RL (k := k) (r := r) M‖ ^ 2 = 0) : M = 0 := by
  rw [RL_sq] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖M i j‖))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖M i j‖)).1 h1 j (Finset.mem_univ _)
  simpa using h2

theorem lm_inj {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (h : Lm k r v = 0) : v = 0 := by
  have hn := lm_norm hv
  rw [h, map_zero, norm_zero] at hn
  have h1 := sq_nonneg ‖RL (k := k) (r := r) v.1‖
  have h2 : 0 ≤ ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have h3 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.1‖
  have h4 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.2‖
  have e1 : ‖RL (k := k) (r := r) v.1‖ ^ 2 = 0 := by nlinarith
  have e2 : ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
  have e3 : ‖RL (k := k) (r := r) v.2.2.1‖ ^ 2 = 0 := by nlinarith
  have e4 : ‖RL (k := k) (r := r) v.2.2.2‖ ^ 2 = 0 := by nlinarith
  have hx : v.2.1 = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v.2.1 a‖)).1 e2 a (Finset.mem_univ _)
    simpa using this
  exact Prod.ext (eq_zero_of_RL_lemma_3 _ e1)
    (Prod.ext hx (Prod.ext (eq_zero_of_RL_lemma_3 _ e3) (eq_zero_of_RL_lemma_3 _ e4)))

def lmEquiv (k r : ℕ) : ↥(Vs k r) ≃ₗ[ℝ] ↥(uH k r) :=
  LinearEquiv.ofBijective ((Lm k r).toLinearMap.restrict fun v hv => lm_mem hv)
    ⟨fun a b hab => by
      have h : Lm k r (a.1 - b.1) = 0 := by
        have := congrArg Subtype.val hab
        simp only [LinearMap.restrict_apply] at this
        rw [map_sub]; exact sub_eq_zero.2 this
      exact Subtype.ext (sub_eq_zero.1 (lm_inj ((Vs k r).sub_mem a.2 b.2) h)),
     fun y => by
      obtain ⟨v, hv, hvy⟩ := lm_surj y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

theorem dimG : Formalism.L2.SG.Pf.BH.DimG := by
  intro k r
  have eG : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (UH (Hpk k r))) = Module.finrank ℝ ↥(uH k r) := by
    rw [lieE_G]; exact ((Submodule.equivMapOfInjective _ RL_injective (uH k r)).finrank_eq).symm
  have eN : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Nset k r)) = Module.finrank ℝ ↥(lieNS k r) := by
    rw [lieE_N]; exact ((Submodule.equivMapOfInjective _ RL_injective (lieNS k r)).finrank_eq).symm
  have eW : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) = Module.finrank ℝ ↥(uWb k r) := by
    rw [(lieWb' k r).2]; exact ((Submodule.equivMapOfInjective _ RL_injective (uWb k r)).finrank_eq).symm
  rw [eG, eN, eW, ← (lmEquiv k r).finrank_eq]
  unfold Vs
  rw [finrank_prodS, finrank_prodS, finrank_prodS, finrank_top, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Formalism.L2.SG.Pf.BH.Sw
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.GramEqOfHyp
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SurjOfIndep
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} (ε : Fin n → Bool)

abbrev dl (i : Fin n) : Fin n → ℂ := Pi.single i 1

theorem hJ_dl (i j : Fin n) : hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := by
  unfold hJ
  simp only [dl, Formalism.REAL.Jm, mulVec_diagonal, dotProduct, Pi.star_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [h]
    · simp [hl]

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool)

def frm3 (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin r ⊕ (Fin r ⊕ Unit) → Fin n → ℂ :=
  Sum.elim e (Sum.elim f (fun _ => z))

structure Hyp (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z = -T

theorem Hyp.fe {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a b : Fin r) :
    hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  rw [hJ_conj, h.ef]; by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

theorem Hyp.ze {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (e a) = 0 := by rw [hJ_conj, h.ez, map_zero]

theorem Hyp.zf {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (f a) = 0 := by rw [hJ_conj, h.fz, map_zero]

theorem gram_eq_of_hyp {e f e' f' : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T : ℂ}
    (h : Hyp ε e f z T) (h' : Hyp ε e' f' z' T) (i j : Fin r ⊕ (Fin r ⊕ Unit)) :
    hJ ε (frm3 e f z i) (frm3 e f z j) = hJ ε (frm3 e' f' z' i) (frm3 e' f' z' j) := by
  rcases i with a | a | _ <;> rcases j with b | b | _ <;>
    simp only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz,
      h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]

theorem gram_nd_of_hyp {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (hT : T ≠ 0) (h : Hyp ε e f z T) :
    (Matrix.of fun i j => hJ ε (frm3 e f z i) (frm3 e f z j)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0 := fun i => by
    have := congrFun hw i
    simpa [mulVec, dotProduct] using this
  funext i
  rcases i with a | a | u
  · have := row (Sum.inr (Sum.inl a))
    simpa [Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz] using this
  · have := row (Sum.inl a)
    simpa [Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez] using this
  · have := row (Sum.inr (Sum.inr u))
    simp [Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this
    rcases this with h1 | h1
    · exact absurd h1 hT
    · simpa using h1

theorem coord_inj {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ (N : Fin (r + 1) → Fin n) (P : Fin (r + k) → Fin n), Function.Injective N ∧ Function.Injective P ∧
      (∀ y, ε (N y) = false) ∧ (∀ x, ε (P x) = true) := by
  set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN
  set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP
  have hcard : sP.card + sN.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => ε i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hP : sP.card = r + k := by omega
  let eN := sN.equivFinOfCardEq hsig
  let eP := sP.equivFinOfCardEq hP
  refine ⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp eN.symm.injective
  · exact Subtype.val_injective.comp eP.symm.injective
  · exact (Finset.mem_filter.1 (eN.symm y).2).2
  · exact (Finset.mem_filter.1 (eP.symm x).2).2

theorem complement {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1)
    {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T) (h : Hyp ε e f z (T : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      (∀ c a, hJ ε (e c) (w a) = 0) ∧ (∀ c a, hJ ε (f c) (w a) = 0) ∧ (∀ a, hJ ε z (w a) = 0) := by
  obtain ⟨N, P, hN, hP, hNs, hPs⟩ := coord_inj ε hdim hsig
  have hNP : ∀ y x, N y ≠ P x := fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this
  set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq
  have hsqc : conj sq = sq := Complex.conj_ofReal _
  have hsq2 : sq * sq = 1 / 2 := by
    rw [hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let p : Fin r → Fin n := fun c => P (Fin.castAdd k c)
  let q : Fin r → Fin n := fun c => N (Fin.castSucc c)
  let qz : Fin n := N (Fin.last r)
  let wi : Fin k → Fin n := fun j => P (Fin.natAdd r j)
  let e0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) + dl (q c))
  let f0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) - dl (q c))
  let z0 : Fin n → ℂ := ((Real.sqrt T : ℝ) : ℂ) • dl qz
  let w0 : Fin k → Fin n → ℂ := fun j => dl (wi j)
  have hp : Function.Injective p := hP.comp (Fin.castAdd_injective r k)
  have hq : Function.Injective q := hN.comp (Fin.castSucc_injective r)
  have hqz : ∀ c, q c ≠ qz := fun c h => Fin.castSucc_ne_last c (hN h)
  have hwi : Function.Injective wi := hP.comp (Fin.natAdd_injective k r)
  have hpw : ∀ c j, p c ≠ wi j := fun c j h => by
    have h1 := congrArg Fin.val (hP h)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  have hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := hJ_dl ε
  have pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [p, hPs]
    · rw [if_neg (hp.ne hab), if_neg hab]
  have qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [q, hNs]
    · rw [if_neg (hq.ne hab), if_neg hab]
  have pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _).symm]
  have qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _)]
  have h0 : Hyp ε e0 f0 z0 (T : ℂ) := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
    · simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · simp only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs
      · linear_combination 2 * hsq2
      · ring
    · simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
      have hq0 : ε qz = false := hNs _
      simp only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true,
        if_false]
      linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h)
    (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)
  have hiso := isIsom_uMat ε g
  have he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c := fun c => hg (Sum.inl c)
  have hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c := fun c => hg (Sum.inr (Sum.inl c))
  have hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z := hg (Sum.inr (Sum.inr ()))
  have ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0 := fun a b => by
    simp only [w0]; rw [hd]; by_cases hab : a = b
    · subst hab; simp [wi, hPs]
    · rw [if_neg (hwi.ne hab), if_neg hab]
  have pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]
  have qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  have zw : ∀ j, hJ ε (dl qz) (w0 j) = 0 := fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  refine ⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩
  · rw [← he, hiso]; simp only [e0, hJ_smul_left, hJ_add_left, pw, qw]; ring
  · rw [← hf, hiso]; simp only [f0, hJ_smul_left, hJ_sub_left, pw, qw]; ring
  · rw [← hz, hiso]; simp only [z0, hJ_smul_left, zw]; ring

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end
