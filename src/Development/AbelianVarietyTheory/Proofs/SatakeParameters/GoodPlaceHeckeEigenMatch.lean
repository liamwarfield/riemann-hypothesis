module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitFrameReps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pre_mul_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    Formalism.IndefR.principalLevelFrame.pre Ψ (Ψ.ψ x) = x :=
  Ψ.inj (Formalism.IndefR.principalLevelFrame.pre_spec Ψ (Ψ.into x))

theorem frame_reps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  intro D V n hF Ψ hΨ Pp hS d hd
  obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D Pp (GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS)
  have hv : Formalism.L2.NG.OverPl Pp s.v := by rw [← hs]; exact s.w_under
  have hrep : GlobalTheory.Hk3.rep V Pp d = hd.choose := by unfold GlobalTheory.Hk3.rep; rw [dite_eq_left hd]
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hRs, hR⟩ := hd.choose_spec
  rw [hrep]
  have hK : ∀ k, k ∈ GlobalTheory.HeckeScalarSph.locK n s.v ↔
      Ψ.ψ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} :=
    fun k => and_congr (hΨ.2 k) (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv k).symm
  have h1 : (1 : Formalism.L2.Theta.GA D V) ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
    have := (hK 1).1 (one_mem _)
    rwa [map_one] at this
  have hαG : α ∈ Formalism.L2.Theta.GfC V := by
    obtain ⟨γ, ⟨hγ, hx⟩, -⟩ := hR.2 α ⟨1, h1, 1, h1, by rw [one_mul, mul_one]⟩
    have := mul_mem (hR.1 γ hγ).1 hx.1.1
    rwa [mul_inv_cancel_left] at this
  obtain ⟨a, rfl⟩ := Ψ.onto α hαG
  have hpull : ∀ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k},
      ∃ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Ψ.ψ κ = k := by
    intro k hk
    obtain ⟨κ, rfl⟩ := Ψ.onto k hk.1.1
    exact ⟨κ, (hK κ).2 hk, rfl⟩
  refine ⟨s, a, hv, (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨-, k₁, hk₁, k₂, hk₂, eγ⟩ := hR.1 γ hγ
    obtain ⟨κ₁, hκ₁, rfl⟩ := hpull k₁ hk₁
    obtain ⟨κ₂, hκ₂, rfl⟩ := hpull k₂ hk₂
    refine ⟨κ₁, hκ₁, κ₂, hκ₂, ?_⟩
    rw [eγ, ← map_mul, ← map_mul, pre_mul_eq]
  · rintro x ⟨κ₁, hκ₁, κ₂, hκ₂, rfl⟩
    obtain ⟨γ, ⟨hγ, hγx⟩, hu⟩ := hR.2 (Ψ.ψ (κ₁ * a * κ₂)) ⟨Ψ.ψ κ₁, (hK _).1 hκ₁, Ψ.ψ κ₂, (hK _).1 hκ₂, by rw [map_mul, map_mul]⟩
    have hγG : γ ∈ Formalism.L2.Theta.GfC V := (hR.1 γ hγ).1
    have eγ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ γ) = γ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hγG
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · have : Ψ.ψ ((Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * (κ₁ * a * κ₂)) ∈
          {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
        rw [map_mul, map_inv, eγ]; exact hγx
      exact ((hK _).2 this).1
    · rintro δ ⟨hδ, hδx⟩
      refine hu δ ⟨hδ, ?_⟩
      have hδG : δ ∈ Formalism.L2.Theta.GfC V := (hR.1 δ hδ).1
      have eδ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ δ) = δ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hδG
      have hδT : TrivOutside {s.v} (Formalism.IndefR.principalLevelFrame.pre Ψ δ) := by
        refine (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv _).1 ?_
        rw [eδ]; exact hRs δ hδ
      have hT : TrivOutside {s.v} ((Formalism.IndefR.principalLevelFrame.pre Ψ δ)⁻¹ * (κ₁ * a * κ₂)) :=
        GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hδT)
          (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul hκ₁.2
            ((GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα)) hκ₂.2)
      have := (hK _).1 ⟨hδx, hT⟩
      rwa [map_mul, map_inv, eδ] at this

end GlobalTheory.SplitFrameReps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  first | exact @GlobalTheory.SplitFrameReps.frame_reps | exact GlobalTheory.SplitFrameReps.frame_reps | (intros; apply GlobalTheory.SplitFrameReps.frame_reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HeckeScalarDC

open GlobalTheory.HeckeScalarSph

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem dc_scalar_fin (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (s : SplitPlace L) (α : GAf L n) (hα : TrivOutside {s.v} α) (Rα : Finset (GAf L n))
    (hRα0 : (∀ γ ∈ Rα, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ Rα ∧ γ⁻¹ * x ∈ Umax L n) :
    ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      ∑ γ ∈ Rα, NG.rt L n γ f = c • f := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα hRα0
  have hRtriv : ∀ γ ∈ Rα, TrivOutside {s.v} γ := by
    intro γ hγ
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hRα0.1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ Rα, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ Rα, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b Rα (R b) hα hb (fun y hy => hRα0.2 y (conv.1 hy))
        (fun γ hγ => conv.2 (hRα0.1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [← e]
  rfl

theorem dc_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS s α hα ι R r h1 h2
  classical
  have hinj : Set.InjOn r R := by
    intro γ hγ δ hδ e
    have hx := h1 γ hγ
    have hU : (r γ)⁻¹ * r γ ∈ Umax L n := by rw [inv_mul_cancel]; exact one_mem _
    exact (h2 (r γ) hx).unique ⟨hγ, hU⟩ ⟨hδ, by rw [← e]; exact hU⟩
  have hA : ∀ γ ∈ R.image r, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    exact h1 δ hδ
  have hB : ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) →
      ∃! γ, γ ∈ R.image r ∧ γ⁻¹ * x ∈ Umax L n := by
    intro x hx
    obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h2 x hx
    refine ⟨r γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hy
    rw [hu δ ⟨hδ, ey⟩]
  obtain ⟨c, hc⟩ := dc_scalar_fin a S hS s α hα (R.image r) ⟨hA, hB⟩
  refine ⟨c, fun f hf hfix => ?_⟩
  rw [← hc f hf hfix, Finset.sum_image (fun γ hγ δ hδ e => hinj hγ hδ e)]

end GlobalTheory.HeckeScalarDC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixedStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.HeckeScalarDC.dc_scalar | exact GlobalTheory.HeckeScalarDC.dc_scalar | (intros; apply GlobalTheory.HeckeScalarDC.dc_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypic
open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.SumTransIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem sumRt_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsSubrep ρ S) (hiso : Formalism.L2.NG.IsoRep S S')
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (f' : Formalism.AUTREP.GAf L n → W) (hf' : f' ∈ S')
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f' = f') :
    ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' = c • f' := by
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : Formalism.AUTREP.GAf L n,
      ((T ⟨Formalism.L2.NG.rt L n h f, hS.stable h _ f.2⟩ : S') : Formalism.AUTREP.GAf L n → W) = Formalism.L2.NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ (f : Formalism.AUTREP.GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨Formalism.L2.NG.rt L n (r γ) f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f := by
    simp only [σ, Submodule.coe_sum]
  have hTσ : ((T σ : S') : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [σ, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt _
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : Formalism.AUTREP.GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem iSup_finset_stable (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, Formalism.L2.NG.rt L n h f ∈ i) (h : Formalism.AUTREP.GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (Formalism.L2.NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

theorem sumRt_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsIrrRep ρ S)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) :
    ((↑t : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : Formalism.L2.NG.IsIrrRep ρ a ∧ Formalism.L2.NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : Formalism.L2.NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : Formalism.L2.NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : Formalism.L2.NG.rt L n κ y - y = z - Formalism.L2.NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := sumRt_iso hS.1 haF.2 v R r c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

theorem sumRt_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n)
    (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S →
    ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ),
    (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) →
    ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS v ι R r c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact sumRt_finset_sum hS v R r c hc t ht f hft hfix

end GlobalTheory.SumTransIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypicStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.SumTransIso.sumRt_isoTyp | exact GlobalTheory.SumTransIso.sumRt_isoTyp | (intros; apply GlobalTheory.SumTransIso.sumRt_isoTyp <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SummandEig

theorem irrScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed

theorem isoScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.rightTranslationSum_scalar_isotypic

theorem frameReps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem cast_sum {D : D7} (M : MtFam D) (μ : D.what₂.Tup) {j k : ℕ} (e : j = k) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m)
    (h1' : 1 ≤ j) (h2' : j ≤ D.R.m) (f' : D.what₂.Mt μ j) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf D.host.E D.R.nV)
    (c : ℂ) (h : ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ k h1 h2).real (e ▸ f')) = c • (M μ k h1 h2).real (e ▸ f')) :
    ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ j h1' h2').real f') = c • (M μ j h1' h2').real f' := by
  subst e
  exact h

theorem extV_inf {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (y : (X.R.HV j t).H) {a b : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)}
    (ha : a ∈ Formalism.L2.Theta.GinfC (Formalism.IndefR.Links.Vc D j)) (hb : b ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j)) :
    X.R.extV j t y (a * b) = (X.R.cV j).ρ a⁻¹ (X.R.extV j t y b) := by
  have hcv := (X.given.core.models.cV j).1
  have e0 : ∀ g, X.R.extV j t y g = (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) := fun g => rfl
  have e1 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict a = 1 := by
    apply Subtype.ext
    exact (MonoidHom.mem_ker (f := Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j))).1 ha
  refine (e0 (a * b)).trans (Eq.trans ?_ (congrArg ((X.R.cV j).ρ a⁻¹) (e0 b)).symm)
  have e2 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict (a * b) = (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict b := by
    rw [map_mul, e1, one_mul]
  have e3 : (X.R.cV j).ρ (a * b)⁻¹ = (X.R.cV j).ρ a⁻¹ := by
    rw [mul_inv_rev, map_mul, hcv _ (inv_mem hb), one_mul]
  have e4 : (X.R.cV j).ρ b⁻¹ = 1 := hcv _ (inv_mem hb)
  have e5 : ∀ x, (X.R.cV j).ρ b⁻¹ x = x := fun x => by rw [e4]; rfl
  have e6 := congr (congrArg DFunLike.coe e3) (congrArg ((X.R.HV j t).e y) e2)
  exact e6.trans (congrArg ((X.R.cV j).ρ a⁻¹) (e5 _)).symm

end GlobalTheory.SummandEig
