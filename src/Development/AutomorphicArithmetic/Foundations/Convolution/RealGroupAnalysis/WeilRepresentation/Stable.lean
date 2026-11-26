module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FinLift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.finLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), FinLift W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ k
  obtain ⟨κ, -, hκ⟩ := finTr F E D
  refine ⟨TR.finRep F 2 (κ k) f, π.stable (.fin (κ k)) f hf, W.L (finGL E 2 k) φ,
    (fockSt F E D W).fin k φ hφ, fun h => ?_⟩
  have e : (fun x => f.1 (x * dM (nu F (finGL E 2 k)))) = (TR.finRep F 2 (κ k) f).1 := by
    funext x
    rw [hκ k]
    rfl
  rw [transl F E D W M f.1 φ h (finGL E 2 k), e]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.stable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Stable W M π := by
  intro F E _ _ _ _ _ _ _ D W M π o Φ hΦ
  refine (Submodule.span_le.2 ?_ : span W M π ≤ (span W M π).comap (act o)) hΦ
  rintro Ψ ⟨f, hf, φ, hφ, e⟩
  cases o with
  | fin k =>
    obtain ⟨f', hf', φ', hφ', h⟩ := finLift F E D W M π f hf φ hφ k
    exact Submodule.subset_span ⟨f', hf', φ', hφ', funext fun g => (congrFun e _).trans (h g)⟩
  | cpt k => exact (kFin F E D W M π f hf φ hφ Ψ e).1 k
  | lie X =>
    obtain ⟨O⟩ := UpperTheory.ConvolutionTheory.R2.Fo.opsEx F
    obtain ⟨Y, s, hY, rfl, -⟩ := lieSplit X
    change lie E 2 (Y + zE s) Ψ ∈ span W M π
    rw [map_add (f := _), LinearMap.add_apply]
    exact add_mem (Submodule.subset_span ⟨f, hf, _, dLFock F E D O Y φ hφ, lieL F E D O W M π f hf φ hφ Y hY Ψ e⟩)
      (Submodule.subset_span ⟨_, π.stable (.lie _) f hf, φ, hφ, lieZ F E D W M π f hf φ hφ s Ψ e⟩)
