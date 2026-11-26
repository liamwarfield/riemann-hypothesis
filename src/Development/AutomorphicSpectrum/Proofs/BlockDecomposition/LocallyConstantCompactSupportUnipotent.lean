module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Fib

section Abstract

variable {G D W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_translate (H : Subgroup G) (σ : Representation ℂ H W)
    (f : smoothPart (ind H σ)) (e : D → G) (he : Continuous e) (h0 : e 0 = 1)
    (hadd : ∀ a b, e (a + b) = e a * e b) (y : G) :
    IsLocallyConstant (fun d => f.1.1 (e d * y)) := by
  have hK : IsOpen {g : G | ind H σ g f.1 = f.1} := f.2
  let c : D → G := fun a => y⁻¹ * e a * y
  have hc : Continuous c := by fun_prop
  have hU : IsOpen (c ⁻¹' {g : G | ind H σ g f.1 = f.1}) := hK.preimage hc
  rw [IsLocallyConstant.iff_exists_open]
  intro d
  refine ⟨(fun x => -d + x) ⁻¹' (c ⁻¹' {g : G | ind H σ g f.1 = f.1}), hU.preimage (by fun_prop), ?_, ?_⟩
  · show ind H σ (c (-d + d)) f.1 = f.1
    simp [c, h0]
  · intro x hx
    have hx' : ind H σ (c (-d + x)) f.1 = f.1 := hx
    have h1 : e x = e d * e (-d + x) := by rw [← hadd, add_neg_cancel_left]
    have h2 := congrArg (fun v : indSpace H σ => v.1 (e d * y)) hx'
    have h3 : (ind H σ (c (-d + x)) f.1).1 (e d * y) = f.1.1 (e d * y * c (-d + x)) := rfl
    simp only [h3] at h2
    have h4 : e d * y * c (-d + x) = e x * y := by
      simp only [c, h1]; group
    simpa [h4] using h2

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp [dEmb, this]

theorem dEmb_add (i t : ℕ) (a b : Fin (t + 1) → k) : dEmb k i t (a + b) = dEmb k i t a * dEmb k i t b := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (a + b) = Fin.append (0 : Fin (i + 1) → k) a + Fin.append (0 : Fin (i + 1) → k) b := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [dEmb, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  have hcol : Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
    refine continuous_matrix fun r c => ?_
    by_cases hc : c = Fin.last _
    · subst hc
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · simpa [colMat] using continuous_const
      · simp only [colMat, if_true, Fin.lastCases_castSucc]
        refine Fin.addCases (fun a => ?_) (fun a => ?_) r'
        · simpa using continuous_const
        · simpa using continuous_apply a
    · simpa [colMat, hc] using continuous_const
  constructor
  · exact continuous_const.add hcol
  · exact continuous_const.sub hcol

theorem dEmb_mul_entry (i t : ℕ) (d : Fin (t + 1) → k) (g : Mir k ((i + 1) + t + 1)) (b : Fin (t + 1)) :
    (((dEmb k i t d * g : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) =
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) + d b := by
  have hg : ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 g.2) (Fin.last _)
    simpa [eLast] using this
  have hv : ((dEmb k i t d : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl
  have hc : colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = d b := by
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right]
  rw [Subgroup.coe_mul, Units.val_mul, hv, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last _)]
  · rw [hc]
    exact congrArg (_ + ·) ((congrArg (d b * ·) hg).trans (mul_one _))
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem hpg_entry_eq_zero (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (b : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = 0 := by
  have h1 := mem_parab_iff.1 (show ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k)) ∈ parab k (ePG (i + 1) (t + 1)) from hh)
    true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_false_last] at h1
  have h2 : ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
    apply Fin.ext
    rw [ePG_true_val]
    simp
  rw [h2] at h1
  exact h1

theorem fibre_isLocallyConstant_hasCompactSupport (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
      HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  refine ⟨isLocallyConstant_translate (HPG k (i + 1) (t + 1)) (sigX τ σ) f.1 (dEmb k i t) (continuous_dEmb i t)
    (dEmb_zero i t) (dEmb_add i t) y, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.2
  let φ : Mir k ((i + 1) + t + 1) → Fin (t + 1) → k := fun c b =>
    -(((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _)
  have hφ : Continuous φ := by
    refine continuous_pi fun b => Continuous.neg ?_
    have h1 : Continuous fun c : Mir k ((i + 1) + t + 1) =>
        (((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
          Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_inv))
    exact (continuous_apply_apply _ _).comp h1
  refine HasCompactSupport.intro (hC.image hφ) fun x hx => ?_
  by_contra hne
  obtain ⟨h, hh, c, hc, e⟩ := hf (dEmb k i t x * y) hne
  refine hx ⟨c, hc, ?_⟩
  have e1 : h = dEmb k i t x * (y * c⁻¹) := by
    rw [← mul_assoc]
    exact eq_mul_inv_of_mul_eq e.symm
  funext b
  have h0 := hpg_entry_eq_zero i t h hh b
  rw [e1, dEmb_mul_entry] at h0
  exact neg_eq_of_add_eq_zero_right h0

end GlobalTheory.CompanionTheory.BZPhiPG.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)),
  IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
    HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport | exact GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PairMult

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then 0 else (n + 1) * (n + 1)) + CompanionTheory.D.LK.key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun j => keyL j < keyL l).card

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftq (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def Ts (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then E1 p q + E2 p q else E1 p q - E2 p q

def Tl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V := Ts E1 E2 l.1 l.2.1.1 l.2.1.2

def bdq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l) +
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) * annq (t, j) * annq (s, i) else 0

def SuppQ (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegQ (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def adLq (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n, CompanionTheory.RgExh.U.adC p q i k • (creq ((s == t), k) * annq (t, i))

def lFq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  liftq n (Ts E1 E2 s p q) + adLq s p q

def c1 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q + lFq E1 E2 false p q)

def c2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q - lFq E1 E2 false p q)

end Chains

abbrev inUL (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inKU (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def omQ (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def topq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (v : V) : Cq n V := Pi.single (omQ lev) v

def IsSubL (lev : Fin n → ℕ) (S : Lt n → Prop) : Prop :=
  (∀ l, S l → inUL lev l) ∧ ∀ (s t : Bool) (i j k : Pos n), i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 →
    S (s, i) → S (t, j) → S ((s == t), k)

section Algebra

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def PairRel (E1 E2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, Commute (E1 a b) (E2 c d)

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ W) : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

def evB (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if lev x.2.1 = lev x.2.2 then (if x.1 then X1 x.2.1 x.2.2 else X2 x.2.1 x.2.2) else 0

def LRel (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X1 p q * X1 r v - X1 r v * X1 p q = (if q = r then X1 p v else 0) - (if v = p then X1 r q else 0)) ∧
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X2 p q * X2 r v - X2 r v * X2 p q = (if q = r then X2 p v else 0) - (if v = p then X2 r q else 0)) ∧
  ∀ p q r v, lev p = lev q → lev r = lev v → Commute (X1 p q) (X2 r v)

end Algebra

def Inv2 (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def InvLev (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ p q, lev p = lev q → Commute (X1 p q + X2 p q) (evB lev X1 X2 b)

def LiftInv : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ v w : V, v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a, Inv2 a ∧ ev2 E1 E2 a v = w

def HCDec2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → Inv2 a →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ∀ x : V, ∃ w : Lt n → V,
        ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

def GenCOU2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (S : Lt n → Prop) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → IsSubL lev S →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (j : ℕ) (x : Cq n V), SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
        ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
          liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def TopCyc : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    PairRel E1 E2 → ∀ v : V, (∀ l, inKU lev l → Tl E1 E2 l v = 0) → bdq E1 E2 (topq lev v) = 0

def LeviRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → PairRel E1 E2 → ∀ x : Cq n V, SuppQ (inUL lev) x →
      (∀ s p q, lev p = lev q → SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ (∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x)) ∧
        lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        (c1 E1 E2 p q (c1 E1 E2 r v x) - c1 E1 E2 r v (c1 E1 E2 p q x) =
          (if q = r then c1 E1 E2 p v x else 0) - (if v = p then c1 E1 E2 r q x else 0)) ∧
        (c2 E1 E2 p q (c2 E1 E2 r v x) - c2 E1 E2 r v (c2 E1 E2 p q x) =
          (if q = r then c2 E1 E2 p v x else 0) - (if v = p then c2 E1 E2 r q x else 0)) ∧
        c1 E1 E2 p q (c2 E1 E2 r v x) = c2 E1 E2 r v (c1 E1 E2 p q x)

def InvL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W)
    (L : Submodule ℂ W) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), LRel lev X1 X2 →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) s ∈ L) →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) (evB lev X1 X2 b s) = evB lev X1 X2 b ((X1 p q + X2 p q) s)) →
    ∃ b', InvLev lev b' ∧ ∀ s ∈ L, evB lev X1 X2 b' s = evB lev X1 X2 b s

def CapOne : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA E m x = GlobalTheory.Dec.gelfVal χ m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def DualCap : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA (barF E) m x = GlobalTheory.Dec.gelfVal (fun a => -χ a) m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

end GlobalTheory.CompanionTheory.PairMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCountG

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + (((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ))

theorem wtR_muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : wtR (muZ lam lev) = muQ lam lev := by
  funext a
  simp only [wtR, muZ, muQ, rhoU]
  push_cast
  ring

theorem wtR_injective : Function.Injective (wtR : (Fin n → ℤ) → Fin n → ℝ) := fun x y h => by
  funext a
  have := congrFun h a
  simpa [wtR] using this


open Classical in
def harmZ (lam : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  ((univ : Finset (Fin n → Fin n)).filter fun lev => IsLev lam fun a => (lev a : ℕ)).image
    fun lev => muZ lam fun a => (lev a : ℕ)

open Classical in
theorem harmSet_eq (lam : Fin n → ℤ) : harmSet lam = (harmZ lam).image wtR := by
  unfold harmSet harmZ
  rw [Finset.image_image]
  refine Finset.image_congr fun lev _ => ?_
  exact (wtR_muZ lam _).symm

def hwOf {M : Type*} [AddCommGroup M] [Module ℂ M] (G : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) :
    Submodule ℂ M where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) G μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add (f := _), hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add (f := _), hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm],
    fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def IsDualFam (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) : Prop :=
  Formalism.REAL.GlRel G ∧ ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
    (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ ξ : E.V →L[ℂ] ℂ,
      HasDerivAt (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) (∑ a, ∑ b, X a b • G a b ξ) 0

end GlobalTheory.CompanionTheory.RealCountG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.CTFin.CapFactor

theorem two_sum (n : Fin 2 → ℕ) : ∑ i, n i = n 0 + n 1 := Fin.sum_univ_two n

theorem std_zero (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 0)) :
    stdBlocks n h ⟨0, i⟩ = Fin.castAdd (n 1) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 0 i).trans ?_
  simp

theorem std_one (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 1)) :
    stdBlocks n h ⟨1, i⟩ = Fin.natAdd (n 0) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 1 i).trans ?_
  simp

theorem modExp_zero (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 0 = n 1 := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
  simp [modExp, h1]

theorem modExp_one (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 1 = -(n 0 : ℤ) := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅ := by decide
  simp [modExp, h1, Finset.sum_filter]

theorem exists_unip_of_mem {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    {v : GL (Fin (n 0 + n 1)) R} (hv : v ∈ unipRad R (stdBlocks n h)) :
    ∃ x : BlockIx (n 0 + n 1) (n 0) → R, v = unip x := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hv
  have hp' := mem_parab_iff.1 hp
  have A : ∀ i j : Fin (n 0), (v : Matrix _ _ R) (Fin.castAdd (n 1) i) (Fin.castAdd (n 1) j) =
      (1 : Matrix (Fin (n 0)) (Fin (n 0)) R) i j := by
    intro i j
    have := hd 0 i j
    rwa [std_zero, std_zero] at this
  have B : ∀ i j : Fin (n 1), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.natAdd (n 0) j) =
      (1 : Matrix (Fin (n 1)) (Fin (n 1)) R) i j := by
    intro i j
    have := hd 1 i j
    rwa [std_one, std_one] at this
  have C : ∀ (i : Fin (n 1)) (j : Fin (n 0)), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.castAdd (n 1) j) = 0 := by
    intro i j
    have := hp' 1 0 i j (by decide)
    rwa [std_one, std_zero] at this
  refine ⟨fun p => (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) p.1.1 p.1.2, Units.ext ?_⟩
  change (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) = 1 + nilM _
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have : ¬ (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, A, Matrix.one_apply, Fin.castAdd_inj]
  · have : (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.castAdd (n 1) i : Fin (n 0 + n 1)) ≠ Fin.natAdd (n 0) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_pos this, Matrix.one_apply, if_neg hne, zero_add]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.natAdd (n 0) i : Fin (n 0 + n 1)) ≠ Fin.castAdd (n 1) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, Matrix.one_apply, if_neg hne, add_zero, C]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_natAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, B, Matrix.one_apply, Fin.natAdd_inj]

def levPair {R : Type} [CommRing R] {n : Fin 2 → ℕ} (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    ∀ i : Fin 2, GL (Fin (n i)) R
  | ⟨0, _⟩ => g.1
  | ⟨1, _⟩ => g.2

theorem lev_eq_leviEmb {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    lev R (n 0) (n 1) g = leviEmb R (stdBlocks n h) (levPair g) := by
  have p0 : ∀ i : Fin (n 0), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨false, i⟩ = stdBlocks n h ⟨0, i⟩ := fun i => by
    rw [std_zero, two_false]; exact Fin.ext (by simp)
  have p1 : ∀ i : Fin (n 1), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨true, i⟩ = stdBlocks n h ⟨1, i⟩ := fun i => by
    rw [std_one, two_true]; exact Fin.ext (by simp)
  have key : ∀ (a b : Fin 2) (i : Fin (n a)) (j : Fin (n b)),
      (lev R (n 0) (n 1) g : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) =
      (leviEmb R (stdBlocks n h) (levPair g) : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩,
      Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · rw [leviEmb_apply_same, ← p0, ← p0]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) false i j
    · rw [leviEmb_apply_ne R _ _ (a := 0) (b := 1) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := false) (b := true) (by simp) i j
    · rw [leviEmb_apply_ne R _ _ (a := 1) (b := 0) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := true) (b := false) (by simp) i j
    · rw [leviEmb_apply_same, ← p1, ← p1]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) true i j
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective j
  exact key a b i j

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  have := map_qdet S.val (fun i j => (⟨X i j, hX i j⟩ : S)) u
  simp only [Subalgebra.coe_val] at this
  rw [← this]
  exact (Formalism.REAL.qdet _ _ : S).2

theorem Eop_commute_blocks (r s : ℕ) (τ : E →+* ℂ) (i j : Fin r) (k l : Fin s) :
    Commute (Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
      (Eop (a := r + s) τ (Fin.natAdd r k) (Fin.natAdd r l)) := by
  have h := glRel_Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j) (Fin.natAdd r k) (Fin.natAdd r l)
  have h1 : (Fin.castAdd s j : Fin (r + s)) ≠ Fin.natAdd r k := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  have h2 : (Fin.natAdd r l : Fin (r + s)) ≠ Fin.castAdd s i := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  rw [if_neg h1, if_neg h2, sub_zero] at h
  exact sub_eq_zero.1 h

theorem capR_commute_capS (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ) : Commute (capR r s τ u) (capS r s τ v) := by
  let T : Set (Module.End ℂ (Sm E (r + s))) :=
    Set.range fun kl : Fin s × Fin s => Eop (a := r + s) τ (Fin.natAdd r kl.1) (Fin.natAdd r kl.2)
  have h1 : capR r s τ u ∈ Subalgebra.centralizer ℂ T := by
    refine qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (Eop_commute_blocks r s τ i j kl.1 kl.2).symm.eq
  have h2 : capS r s τ v ∈ Subalgebra.centralizer ℂ {capR r s τ u} := by
    refine qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl)

theorem capelli_levi_factorization (n : Fin 2 → ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) (g : GA E (n 0 + n 1)), F.1 (unip x * g) = F.1 g)
    (m : GA E (n 0) × GA E (n 1)) :
    (cap (a := n 0 + n 1) τ u F).1 (lev (Ad E) (n 0) (n 1) m) =
      (capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) F)).1
        (lev (Ad E) (n 0) (n 1) m) := by
  have h : ∑ i, n i = n 0 + n 1 := two_sum n
  let S : Subalgebra ℂ (Module.End ℂ (Sm E (n 0 + n 1))) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin (n 0 + n 1) × Fin (n 0 + n 1) => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ GlobalTheory.SpehInfChar.leftInvAlg (unipRad (Ad E) (stdBlocks n h)) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin (n 0 + n 1) → Fin (n 0 + n 1) → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := n 0 + n 1) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := GlobalTheory.SpehInfChar.qdet_sub_blocks_mem S n h X hX u
  have hB0 : Formalism.REAL.qdet (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩))
      (u + ((n 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 0 : ℂ) / 2) = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
      funext p q
      rw [std_zero, std_zero]
    rw [e1, modExp_zero, capR]
    congr 1
    push_cast
    ring
  have hB1 : Formalism.REAL.qdet (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩))
      (u + ((n 1 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 1 : ℂ) / 2) = capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
      funext p q
      rw [std_one, std_one]
    rw [e1, modExp_one, capS]
    congr 1
    push_cast
    ring
  have hval : S.val (List.ofFn fun i : Fin 2 => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod =
      capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) * capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    rw [map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [Function.comp_apply, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    rw [← hB0, ← hB1, map_qdet, map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + (((n 0 + n 1 : ℕ) : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl
  have hψ : ∀ v ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (v * g) = F.1 g := fun v hv g => by
    obtain ⟨x, rfl⟩ := exists_unip_of_mem n h hv
    exact hF x g
  rw [lev_eq_leviEmb n h m]
  set ℓ := leviEmb (Ad E) (stdBlocks n h) (levPair m) with hℓ
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun w => ((w : Module.End ℂ (Sm E (n 0 + n 1))) F).1 ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin (n 0 + n 1)) (w : S), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} ≤
      LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change (Eop τ p q ((w : Module.End ℂ (Sm E (n 0 + n 1))) F)).1 ℓ = 0
    exact GlobalTheory.SpehInfChar.Eop_leviEmb_eq_zero E n h _ (hSL w.2 F hψ) τ p q hpq _
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hL : ∀ w : S, L w = ((S.val w) F).1 ℓ := fun _ => rfl
  rw [hL, hL, hcap, hval] at h1
  rw [h1, (capR_commute_capS (n 0) (n 1) τ _ _).eq]
  rfl

theorem cap_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
    ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) =
      (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  intro E _ _ _ r s τ u F hF m
  exact capelli_levi_factorization ![r, s] τ u F hF m

end GlobalTheory.CompanionTheory.CTFin.CapFactor

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSumStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_levi_factorization_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) = (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | exact GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def IsBump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (c : G) (v : W) (B : cIndSpace H ρ) : Prop :=
  (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a v) ∧
    ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0

end Abs

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 100000 in
def sO (i t : ℕ) : Mir k (i + (t + 1)) →* Mir k ((i + 1) + t + 1) :=
  (sEmb k ((i + 1) + t)).comp (castM k (by omega : i + (t + 1) = (i + 1) + t)).toMonoidHom

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Fin n × Fin n

abbrev Ix (n : ℕ) : Type := Bool × Pos n

abbrev Cr (n : ℕ) (V : Type) : Type := Finset (Ix n) → V

def keyR (i : Ix n) : ℕ := (if i.1 then n * n else 0) + CompanionTheory.D.LK.key i.2

def sgR (i : Ix n) (A : Finset (Ix n)) : ℂ := (-1) ^ (A.filter fun j => keyR j < keyR i).card

def cp (p q r : Pos n) : ℂ :=
  (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then 1 else 0) - (if q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2) then 1 else 0)

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then 0 else sgR i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def creR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then sgR i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def liftR (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cr n V →ₗ[ℂ] Cr n V' :=
  T.compLeft (Finset (Ix n))

def rl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Ix n) : Module.End ℂ V :=
  if i.1 then E1 i.2.1.1 i.2.1.2 + E2 i.2.1.1 i.2.1.2 else E2 i.2.1.1 i.2.1.2

def torV (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2 p.2 else E2 p.2 p.2

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Lt n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2.1 p.2.2 else E2 p.2.1 p.2.2

structure Pair2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

end Chains

def Inv2 (a : FreeAlgebra ℂ (Lt n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def LiftInv : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Pair2 E1 E2 → (∀ a b (x y : V), inner ℂ (kF E1 E2 a b x) y = inner ℂ x (kF E1 E2 b a y)) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ (μ : Fin n → ℝ) (v w : V), v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a : FreeAlgebra ℂ (Lt n), Inv2 a ∧ ev2 E1 E2 a v = w

end GlobalTheory.CompanionTheory.RealMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CFin

abbrev Idx (r m : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin r

def frm {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : Matrix (Fin n) (Idx r m) A :=
  Matrix.fromCols X (Matrix.fromCols Z Y)

def cnt {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : ℤ := ((S.filter (· < i)).card : ℤ)

def lev {r : ℕ} (m : ℕ) (S : Finset (Fin r)) : Idx r m → ℤ
  | .inl i => cnt S i - S.card
  | .inr (.inl _) => 0
  | .inr (.inr i) => S.card - cnt S i

def wt {r : ℕ} (m : ℕ) (t : Fin r → ℝ) : Idx r m → ℝ
  | .inl i => t i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (t i)⁻¹

def bd {ι A : Type} [Zero A] (b : ι → ℤ) (M : Matrix ι ι A) : Matrix ι ι A :=
  Matrix.of fun u v => if b u = b v then M u v else 0


open Classical in
def deep {r : ℕ} (t₁ : ℝ) (t : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter fun j => t₁ < t j ∧ ∀ j' : Fin r, j'.val = j.val + 1 → t₁ * t j' < t j

def StabUpTo {L : Type} [CommRing L] {n r : ℕ} (X : Matrix (Fin n) (Fin r) L) (g : Matrix (Fin n) (Fin n) L)
    (j : Fin r) : Prop :=
  ∀ l : Fin r, l ≤ j → ∃ b : Fin r → L, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0

theorem bd_map {ι A B : Type} [Zero A] [Zero B] (b : ι → ℤ) (φ : A → B) (h0 : φ 0 = 0) (M : Matrix ι ι A) :
    (bd b M).map φ = bd b (M.map φ) := by
  ext u v
  by_cases h : b u = b v <;> simp [bd, h, h0]

theorem bd_mul {ι A : Type} [Fintype ι] [CommRing A] {b : ι → ℤ} {M N : Matrix ι ι A}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) : bd b (M * N) = bd b M * bd b N := by
  ext u v
  simp only [bd, Matrix.of_apply, Matrix.mul_apply]
  by_cases h : b u = b v
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : b u = b w
    · rw [if_pos h1, if_pos (h1.symm.trans h)]
    · rw [if_neg h1]
      rcases lt_or_gt_of_ne h1 with h2 | h2
      · rw [show N w v = 0 from hN (by omega), mul_zero, zero_mul]
      · rw [show M u w = 0 from hM h2, zero_mul, zero_mul]
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun w _ => ?_).symm
    by_cases h1 : b u = b w
    · rw [if_neg (fun e => h (h1.trans e)), mul_zero]
    · rw [if_neg h1, zero_mul]

end GlobalTheory.CompanionTheory.CFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMir

theorem iterPhi_twJacquet_equiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)) :
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  induction j with
  | zero =>
    exact ⟨Submodule.quotEquivOfEq _ _ (GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ)⟩
  | succ j ih =>
    obtain ⟨e₁⟩ := ih (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n + j) n (Nat.le_add_right n j) τ.V τ.ρ
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.CompanionTheory.BZMir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_iterated_phi_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)), Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ] TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
open Ad3 (Pl Qv pOf)
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

end GlobalTheory.CompanionTheory.HalfIntegral
end
end
