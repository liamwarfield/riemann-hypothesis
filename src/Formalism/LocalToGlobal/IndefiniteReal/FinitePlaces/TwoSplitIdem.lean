module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

def TwoSplits (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (2 : 𝓞 D.host.E) ∈ P.asIdeal → ¬ Lev.IsConjPl (D := D) P P

def TwoSplitIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal →
    ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def LatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
          AddSubgroup (WO S T)) : Set (WO S T)) ∧
      IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
          (fun _ => True), (w - u).map (finPart D) = 0} ∧
      (∀ a : AE D, finPart D a ∈ intAE D →
        ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ x : WO S T, x.map (infPart D) = 0 →
        (x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
          ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
            ψ (symplO S T x u) = 1)


def HeisStable (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ),
    IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w₀ f)

def DRhoStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)

def PtStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ)
      (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev latAll (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T ΛS ΛT fun _ => True

def PlaceLatDual (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ e' : AE D, IsSplitIdem D e' → ∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e' * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT) ∧
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT)) ∧
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT)) ∧
      (∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceModelAt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
      (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm ∧
          (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm' →
            ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → Tm' Φ = Tm Φ) ∧
          (∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
          ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) →
            heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ

def SplitLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
    ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm →
    ∀ e₁ : AE D, IsSplitIdem D e₁ → e₁ * e = e₁ →
    ∀ (g : GA D S) (h : GA D T), SuppAt e₁ S g → SuppAt e₁ T h →
    ∀ x y : (AE D)ˣ, IsDetAt e₁ S g x → IsDetAt e₁ T h y →
      ∃ r : ℝ, 0 < r ∧
        (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
          om (g, h) (Tm Φ) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • Tm (fun t => Φ (actO S T g⁻¹ h⁻¹ t))) ∧
        ((∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) →
          (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) → r = 1)

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)
    | fun_prop

theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_const v))

theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  obtain ⟨hq2, ⟨U2, hU2, hl2⟩, hc2, hs2⟩ := hg
  refine ⟨fun γ w => ?_, ⟨U1 ⊓ U2, ?_, fun u hu h0 => ?_⟩, hc1.add hc2,
    fun k L hL h0 w => (hs1 k L hL h0 w).add (hs2 k L hL h0 w)⟩
  · simp only [Pi.add_apply, hq1 γ w, hq2 γ w, mul_add]
  · rw [AddSubgroup.coe_inf]
    exact hU1.inter hU2
  · have e1 := hl1 u hu.1 h0
    have e2 := hl2 u hu.2 h0
    funext z
    have z1 := congrFun e1 z
    have z2 := congrFun e2 z
    simp only [heisO, Pi.add_apply, Pi.zero_apply] at z1 z2 ⊢
    rw [mul_add, z1, z2]

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  refine ⟨fun γ w => ?_, ⟨U1, hU1, fun u hu h0 => ?_⟩, hc1.const_smul c,
    fun k L hL h0 w => (hs1 k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hq1 γ w]
    ring
  · have e1 := hl1 u hu h0
    funext z
    have z1 := congrFun e1 z
    simp only [heisO, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at z1 ⊢
    rw [mul_left_comm, z1]

end Theta

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

end Svn

end Formalism.IndefR.Fin

end
end
