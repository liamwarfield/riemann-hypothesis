module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.TopEig
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace PositivityTheory.Rg.HF.GL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := by
  intro L hL W _ _ _ ρ hρ J hJ
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  haveI : FiniteDimensional ℂ (GA E 0 → ℂ) := inferInstance
  infer_instance

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  rw [CuspidalL2GL.splitCentre_comm]
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) 0 s := by
    intro s
    have := GlobalTheory.T.split_centre_derivative_lie_action E a ψ g s
    rwa [h] at this
  have := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [CuspidalL2GL.splitCentre_zero] using this

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := _root_.CuspFormAutomorphicBounds.cuspFin_pos (a := a) ha

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact cuspFin_zero
  · exact cuspFin_pos ha

theorem genFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a :=
  GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters cuspFin GlobalTheory.CompanionTheory.CTFin.ctFin

theorem automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  PositivityTheory.Affgl.TopEig.top genFin

end PositivityTheory.Rg.HF.GL
