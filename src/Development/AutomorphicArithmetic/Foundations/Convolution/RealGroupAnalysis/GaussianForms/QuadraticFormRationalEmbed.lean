module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormRationalEmbed
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_rt {F : Type} [Field F] [NumberField F] (c : F) : ψ (UpperTheory.ConvolutionTheory.R2.rt c) = 1 := by
  unfold ψ UpperTheory.ConvolutionTheory.R2.rt
  rw [adelicChar_algebraMap]
  simp

private lemma quadraticForm_rational_embed {F : Type} [Field F] [NumberField F] (δ : F) (ξ : Fin 4 → F) :
    q4 δ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = UpperTheory.ConvolutionTheory.R2.rt (ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0) := by
  simp [q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]

theorem UpperTheory.ConvolutionTheory.R2.C.thOm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), δ ≠ 0 → IsOm δ η Om → ∀ γ φ, Th (Om (ratS F γ) φ).1 = Th φ.1 := by
  intro F _ _ δ η Om hδ hO γ
  have hγ : ratS F γ ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}) := by
    rw [(UpperTheory.ConvolutionTheory.R2.gen F).2]
    exact ⟨γ, rfl⟩
  have key : ∀ g ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}),
      ∀ φ : S4 F, Th (Om g φ).1 = Th φ.1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro φ
      rcases hg with ⟨b, rfl⟩ | hg
      · unfold Th
        refine tsum_congr fun ξ => ?_
        rw [hO.n, quadraticForm_rational_embed, ← map_mul, psi_rt, one_mul]
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        have h : (Om (wW F) φ).1 = ft4 δ φ.1 := funext (hO.w φ)
        rw [h]
        exact (UpperTheory.ConvolutionTheory.R2.C.ftBasic F δ hδ φ.1 φ.2).2.2
    | one => intro φ; simp
    | mul x y _ _ hx hy =>
      intro φ
      rw [map_mul, Module.End.mul_apply, hx, hy]
    | inv x _ hx =>
      intro φ
      have h := hx (Om x⁻¹ φ)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
      exact h.symm
  exact key _ hγ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsGauss
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussOp
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem quadraticForm_neg (δ : F) (y : V4 F) : q4 δ (-y) = q4 δ y := by
  simp only [q4, Pi.neg_apply]
  ring

private theorem quaternaryForm_neg_right (δ : F) (y v : V4 F) : B4 δ (-y) (-v) = B4 δ y v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.gaussOp :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    Pc δ (b : A F) φ.1 v = c * ft4 δ (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) v := by
  intro F _ _ δ hδ b c hc φ v
  have hmem := (pcMem F δ).2 hδ b φ.1 φ.2
  have h2 := (ftBasic F δ hδ _ hmem).2.1 (-v)
  rw [neg_neg] at h2
  rw [← h2]
  have e1 : ∀ y, ft4 δ (Pc δ (b : A F) φ.1) y * ψ (B4 δ y (-v)) =
      c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 (-y) * ψ (B4 δ y (-v)) := fun y => by
    rw [idxFt F δ b c hc φ y]
  conv_lhs => rw [ft4]
  simp only [e1]
  rw [← integral_neg_eq_self _ (adeleMeasurePi F)]
  simp only [neg_neg, quadraticForm_neg, quaternaryForm_neg_right]
  rw [ft4, ← integral_const_mul]
  congr 1
  funext y
  ring
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.opsGauss :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) →
    (∀ b : (A F)ˣ, IsIdx δ (b : A F) (((η b : ℂˣ) : ℂ) * (((ab b)⁻¹ ^ 2 : ℝ) : ℂ))) → Gauss O.N O.M O.W := by
  intro F _ _ δ η O hδ hη hidx t
  obtain ⟨b, hb⟩ : ∃ b : (A F)ˣ, b = -t⁻¹ := ⟨_, rfl⟩
  have hbc : -((t⁻¹ : (A F)ˣ) : A F) = (b : A F) := by simp [hb]
  have htb : -(((b⁻¹ : (A F)ˣ) : A F)) = (t : A F) := by simp [hb]
  rw [hbc, ← hb]
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  simp only [Module.End.mul_apply]
  have hL : (O.W (O.N (t : A F) (O.W φ))).1 v =
      ft4 δ (fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y) v := by
    rw [O.W_apply]
    congr 1
    funext y
    rw [O.N_apply, O.W_apply]
  have hR : (O.N (b : A F) (O.M b (O.W (O.N (b : A F) φ)))).1 v =
      ((η b : ℂˣ) : ℂ) * ((ab b ^ 2 : ℝ) : ℂ) * Pc δ (b : A F) φ.1 v := by
    rw [O.N_apply, O.M_apply, O.W_apply, (pcMem F δ).1]
    have : (fun y => (O.N (b : A F) φ).1 y) = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x :=
      funext fun y => O.N_apply _ _ _
    have h2 : (O.N (b : A F) φ).1 = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x := this
    rw [h2]
    ring
  have hG := gaussOp F δ hδ b _ (hidx b) φ v
  have hη2 : ((η b : ℂˣ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hη b)
    simpa using this
  have hab : ab b ≠ 0 := by
    have : 0 < ab b := (IdeleGroup.ideleModule F b).2
    exact this.ne'
  have habc : ((ab b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  have hfn : (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) =
      fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y := by
    funext y
    rw [← htb, neg_mul]
  rw [hfn] at hG
  rw [hL, hR, hG]
  push_cast
  field_simp
  rw [hη2]
  ring
end
