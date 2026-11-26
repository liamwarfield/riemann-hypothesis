module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieL O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y hY Φ hΦ
  funext g
  have hE := (exPar E Y)
  have h0 : ex Y 0 = 1 := by
    refine Units.ext ?_
    show NormedSpace.exp ((0 : ℝ) • Matrix.of Y) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ g (ex Y) Y h0 hE.2.2.1
  have h2 := derL F E D O W M π f hf φ hφ Y hY g
  rw [hΦ] at h1
  rw [GlobalTheory.CuspRep.lie_apply, hΦ]
  exact h1.unique h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieZ
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieZ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieZ W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ s Φ hΦ
  funext h
  obtain ⟨hadd, -, hder, -, -⟩ := UpperTheory.ConvolutionTheory.R2.Ff.exPar E (zE s)
  have h0 : ex (zE s) 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.mp h00
  obtain ⟨z, c, hc, hz⟩ := UpperTheory.ConvolutionTheory.R2.Ff.cenExp F E D s
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hE := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf)
  have hlin := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ h (ex (zE s)) (zE s) h0 hder
  have h2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ c _ hc h
  have key : ∀ t, lift W M (fun x => f.1 (x * TR.infGL F 2 (c t))) φ h =
      Φ.1 (h * infGL E 2 (ex (zE s) t)) := by
    intro t
    obtain ⟨e1, e2⟩ := hz t
    have e3 : (fun x => f.1 (x * TR.infGL F 2 (c t))) = ((ω (ideleNorm F E (z t)) : ℂˣ) : ℂ) • f.1 := by
      funext x
      rw [← e2, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, hω f hf]
      rfl
    rw [hΦ, e1, e3, hlin, ← UpperTheory.ConvolutionTheory.R2.scalar_comm (z t) h, hE]
    rfl
  have h3 : HasDerivAt (fun t => Φ.1 (h * infGL E 2 (ex (zE s) t)))
      (lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0 := by
    simpa only [key] using h2
  exact h1.unique h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormDetKinf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem norm_det_kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : Kinf E 2)
    (w : InfinitePlace E) : ‖(Unitary.toUnits k).val.det w‖ = 1 := by
  have h : star k.1 * k.1 = 1 := by simp
  have hd : star (k.1.det) * k.1.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at this
  have hw : star (k.1.det w) * k.1.det w = 1 := congrFun hd w
  have hn : ‖k.1.det w‖ * ‖k.1.det w‖ = 1 := by
    have := congrArg norm hw
    rwa [norm_mul, norm_star, norm_one] at this
  have h0 : 0 ≤ ‖k.1.det w‖ := norm_nonneg _
  change ‖k.1.det w‖ = 1
  nlinarith

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

theorem UpperTheory.ConvolutionTheory.R2.Ff.kFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), KFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  have hl := lin F E D W M π
  obtain ⟨U, hUF, hfd, hU⟩ := (fockSt F E D W).cpt φ hφ
  have key : ∀ k : Kinf E 2, (cptRep E 2 k Φ).1 = lift W M f.1 (W.L (infGL E 2 (Unitary.toUnits k)) φ) := by
    intro k
    funext h
    have h1 : nu F (infGL E 2 (Unitary.toUnits k)) = 1 :=
      oneOf F E D (Unitary.toUnits k) (norm_det_kinf k)
    have h2 := transl F E D W M f.1 φ h (infGL E 2 (Unitary.toUnits k))
    rw [h1, dM_one'] at h2
    simp only [mul_one] at h2
    change Φ.1 (h * infGL E 2 (Unitary.toUnits k)) = _
    rw [hΦ]
    exact h2
  refine ⟨fun k => Submodule.subset_span ⟨f, hf, _, hUF (hU k), key k⟩, ?_⟩
  haveI := hfd
  let T : U →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun u => lift W M f.1 u.1
      map_add' := fun u u' => hl.1 f hf u.1 (hUF u.2) u'.1 (hUF u'.2)
      map_smul' := fun c u => hl.2.1 f.1 c u.1 }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype ≤ LinearMap.range T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨_, hU k⟩, (key k).symm⟩
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact (Submodule.equivMapOfInjective (Sm E 2).subtype (Submodule.injective_subtype _) _).symm.finiteDimensional
end
