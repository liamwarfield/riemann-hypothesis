module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isParamVec_of_injective_equivariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : GlobalTheory.LFun.IsParamVec σ J L h ρ' (f x) B) : GlobalTheory.LFun.IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, GlobalTheory.LFun.IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, GlobalTheory.LFun.IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem thetaKO_om_apply {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g a : GA D S)
    (x a' : GA D T) (u : WO S T → ℂ) : thetaKO om g x (om (a, a') u) = thetaKO om (g * a) (x * a') u := by
  simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem thetaKO_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {u : WO S T → ℂ}
    (hu : IsThetaFunO ψ S T u) (γ : GA D S) (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) :
    thetaKO om (γ * g) x u = thetaKO om g x u := by
  have e : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  simp only [thetaKO, e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hu)

theorem thetaIntegral_param : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  intro hP D hT ψ θ S T χS χT om hθ hW t ht ν 𝓕 hν h𝓕 v hunr w h f hf y B hy hc hB hne
  let U : Submodule ℂ (WO S T → ℂ) := by
    exact {
    carrier := {f | IsThetaFunO ψ S T f}
    add_mem' {f g} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) := by
      have h : IsThetaFunO ψ S T (f + g) := {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          obtain ⟨V, hV, hfix'⟩ := hg.level
          refine ⟨U ⊓ V, hU.inter hV, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu.1 hfin) w
          have eg := congrFun (hfix' u hu.2 hfin) w
          unfold heisO at ef eg ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, ef, eg]
        cont := hf.cont.add hg.cont
        smooth k L hL hreal w := (hf.smooth k L hL hreal w).add (hg.smooth k L hL hreal w) }
      exact h
    zero_mem' := by
      have h : IsThetaFunO ψ S T 0 := {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const }
      exact h
    smul_mem' c f (hf : IsThetaFunO ψ S T f) := by
      have h : IsThetaFunO ψ S T (c • f) := {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          refine ⟨U, hU, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu hfin) w
          unfold heisO at ef ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ef]
        cont := hf.cont.const_smul c
        smooth k L hL hreal w := contDiff_const.mul (hf.smooth k L hL hreal w) }
      exact h
    }
  have hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  let ρ0 : Representation ℂ (Gv S v) (GA D S → ℂ) := (rightReg ℂ (GA D S) ℂ).comp (embV S v)
  have hρ0 : ∀ a (z : GA D S → ℂ) g, ρ0 a z g = z (g * embV S v a) := fun _ _ _ => rfl
  let cy : GA D S → ℂ := fun g => conj (y g)
  let X : Submodule ℂ (GA D S → ℂ) := Submodule.span ℂ (Set.range fun a : Gv S v => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (Gv S v) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u, IsThetaFunO ψ S T u → ∀ x, IntegrableOn (fun g => thetaKO om g x u * z g) 𝓕 ν) ∧
      (∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u hu x => GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn hP D ψ S T χS χT om hW θ hθ ν 𝓕 hν h𝓕 u y hu hy hc (embV S v a) x,
        fun γ hγ g => ?_⟩
      show conj (y (γ * g * embV S v a)) = conj (y (g * embV S v a))
      rw [mul_assoc, hy.left γ hγ]
    | zero => exact ⟨fun u _ x => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (z + z') g) = fun g => thetaKO om g x u * z g + thetaKO om g x u * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u hu x).add (h2.1 u hu x)
    | smul c z _ h1 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (c • z) g) = fun g => c * (thetaKO om g x u * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u hu x).const_mul c
  let bf : U → X → GA D T → ℂ := fun u z x => ∫ g in 𝓕, thetaKO om g x (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D T → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z z.2).1 u' u'.2 x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z' z'.2).1 u u.2 x)]
      congr 1; funext g
      simp [mul_add])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ a a' (u : U) (z : X), b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a z) =
      (rightReg ℂ (GA D T) ℂ).comp (embV T v) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in 𝓕, thetaKO om g x (om (embV S v a, embV T v a') u) * (z : GA D S → ℂ) (g * embV S v a) ∂ν =
      ∫ g in 𝓕, thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D S ν 𝓕 hν h𝓕 (fun g => thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hW u.2 γ hγ, (hXp z z.2).2 γ hγ]) (embV S v a)
  have hx : GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ ⟨cy, hcy⟩ B :=
    isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective hB
  exact hT ψ S T χS χT om hW t ht v trivial hunr w h U hU ⟨f, hf.1⟩ hf X ρ ⟨cy, hcy⟩ B hx (GA D T → ℂ)
    ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) b hb hne

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransferStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  first | exact @GlobalTheory.ChainOnto.thetaIntegral_param | exact GlobalTheory.ChainOnto.thetaIntegral_param | (intros; apply GlobalTheory.ChainOnto.thetaIntegral_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSumProof

variable {D : D7}

theorem om_zero_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ hf)

theorem liftSum : ∀ D : D7, LiftSum D := by
  intro D ψ θ hθ S T x y hx hy k hk P
  obtain ⟨χS, χT, hω⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hk.vac.1
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hcomb : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 k.vac hvac (WO S T) k.c.support id k.c (fun u hu => hk.fin u hu)
  have hpt : IsThetaFunO ψ S T (k.pt ψ θ x y P) :=
    GlobalTheory.FockTheta.ptStable D ψ θ hψ hθ S T x.s y.s x.B y.B _ P hcomb

  have key : ∀ φ : GA D S → ℂ, IsContAut S φ →
      (∀ h, IntegrableOn (fun g => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) x.vol.𝓕 x.vol.μ) ∧
      Continuous fun h => ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ := by
    intro φ hφ
    have hc : Continuous (Function.uncurry fun (g : GA D S) (h : GA D T) => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) :=
      (hω.om_cont _ hpt 0).mul (hφ.2.comp continuous_fst)
    have hinv : ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T),
        k.om (γ * g, h) (k.pt ψ θ x y P) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y P) 0 * φ g := by
      intro γ hγ g h
      have e := om_zero_rat hω hpt hγ (one_mem (GQ T)) g h
      rw [one_mul] at e
      rw [e, hφ.1 γ hγ g]
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hx.cpt x.vol (GA D T) _ hc hinv
    exact ⟨h1, h2⟩
  refine ⟨hpt, fun φ hφ => ⟨fun γ' hγ' h => ?_, ?_⟩, fun I s a φ hφ => ?_⟩
  · show ∫ g in x.vol.𝓕, k.om (g, γ' * h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ =
      ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ
    congr 1
    funext g
    have e := om_zero_rat hω hpt (one_mem (GQ S)) hγ' g h
    rw [one_mul] at e
    rw [e]
  · exact (key φ hφ).2
  · funext h
    show ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * (∑ i ∈ s, a i • φ i) g ∂x.vol.μ =
      (∑ i ∈ s, a i • fun h' => ∫ g in x.vol.𝓕, k.om (g, h') (k.pt ψ θ x y P) 0 * φ i g ∂x.vol.μ) h
    rw [Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : (fun g => ∑ i ∈ s, k.om (g, h) (k.pt ψ θ x y P) 0 * (a i * φ i g)) =
        fun g => ∑ i ∈ s, a i * (k.om (g, h) (k.pt ψ θ x y P) 0 * φ i g) := by
      funext g
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum s (fun i hi => ((key (φ i) (hφ i hi)).1 h).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul (a i) _

end GlobalTheory.SeeSaw.LiftSumProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.PlaceProjAt

theorem algebraMap_mem_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (PP : Formalism.L2.DIV.Pl D.host.E) (h : IsProjAt φ PP) (a : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ PP.asIdeal ↔ a ∈ v.asIdeal := by
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  refine (h _).trans ?_
  rw [h1, GlobalTheory.PlaceRed.rdQ_alg, ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem under_resCard : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal := by
  intro D v φ PP h
  have hmem := algebraMap_mem_iff φ PP h
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← hmem]
    rfl
  refine ⟨hv, ?_⟩
  refine (GlobalTheory.LFun.SatBoundGL.resCard_completion v).trans ?_
  let f : 𝓞 D.host.F →+* 𝓞 D.host.E ⧸ PP.asIdeal :=
    (Ideal.Quotient.mk PP.asIdeal).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hker : RingHom.ker f = v.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hmem]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) (GlobalTheory.PlaceRed.rdQ_int φ x)
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk PP.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = Ideal.Quotient.mk PP.asIdeal x
    rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    refine (h _).2 ?_
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        (x : D.host.E) - ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) from
        map_sub (algebraMap (𝓞 D.host.E) D.host.E) _ _, ← GlobalTheory.PlaceRed.rdQh_apply, map_sub, GlobalTheory.PlaceRed.rdQh_apply, GlobalTheory.PlaceRed.rdQh_apply, h1,
      GlobalTheory.PlaceRed.rdQ_alg]
    exact ha
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv

end GlobalTheory.PlaceProjAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_projection_under_eq_residue_card_eq_absNorm : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal := by
  first | exact @GlobalTheory.PlaceProjAt.under_resCard | exact GlobalTheory.PlaceProjAt.under_resCard | (intros; apply GlobalTheory.PlaceProjAt.under_resCard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TameLiftChar

open ValuativeRel

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem val_le_iff (x y : Fv D.host.F v) :
    valuation (Fv D.host.F v) x ≤ valuation (Fv D.host.F v) y ↔ Valued.v x ≤ Valued.v y := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]

theorem val_lt_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h := val_le_iff (D := D) (v := v) 1 x
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

theorem val_eq_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x = 1 ↔ Valued.v x = 1 := by
  have h1 := val_le_iff (D := D) (v := v) 1 x
  have h2 := val_le_iff (D := D) (v := v) x 1
  rw [map_one, map_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem rdQ_one (φ : SplitProj D v) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (1 : D.host.E) = 1 := by
  show φ (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def, map_one]

def rdQHom (φ : SplitProj D v) : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _).toRingHom

theorem rdQHom_apply (φ : SplitProj D v) (x : D.host.E) : rdQHom φ x = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x := rfl

theorem val_rdQ_le_one (φ : SplitProj D v) (x : 𝓞 D.host.E) : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) ≤ 1 := by
  let w : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)) := Valued.v
  have hx : IsIntegral ℤ (x : D.host.E) := x.2
  obtain ⟨p, hm, hp⟩ := hx
  have hO : IsIntegral w.integer (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) := by
    refine ⟨p.map (Int.castRingHom w.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← rdQHom_apply]
    have : (algebraMap w.integer (Fv D.host.F v)).comp (Int.castRingHom _) =
        (rdQHom φ).comp (algebraMap ℤ D.host.E) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (Valuation.integer.integers w).mem_of_integral hO

end GlobalTheory.TameLiftChar

open GlobalTheory.TameLiftChar in
theorem GlobalTheory.tameLift_isTame_not_isUnram : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  intro D v φ PP ξ hP hξ ξl hl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (x : Fv D.host.F v) ((1 : (kP PP)ˣ) : kP PP) := by
      refine ⟨1, by simp, ?_⟩
      simpa [rdQ_one] using (val_lt_one_iff _).1 hx
    rw [hl x 1 hr, map_one]
  · intro hun
    obtain ⟨k, hk⟩ : ∃ k, ξ k ≠ 1 := by
      by_contra h; push_neg at h; exact hξ (MonoidHom.ext h)
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (k : kP PP)
    have hnot : x0 ∉ PP.asIdeal := by
      intro hm
      have : ((k : kP PP)) = 0 := by rw [← hx0]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact k.ne_zero this
    have hle := val_rdQ_le_one φ x0
    have hge : ¬ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := fun h => hnot ((hP x0).2 h)
    have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) = 1 := le_antisymm hle (not_lt.1 hge)
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    let u : (Fv D.host.F v)ˣ := Units.mk0 _ hne
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) := ⟨x0, hx0, by simp [u]⟩
    exact hk ((hl u k hr).symm.trans (hun u ((val_eq_one_iff _).2 h1)))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_lift_residue_character_isTame_not_unramified : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  first | exact @GlobalTheory.tameLift_isTame_not_isUnram | exact GlobalTheory.tameLift_isTame_not_isUnram | (intros; apply GlobalTheory.tameLift_isTame_not_isUnram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CenterScalar

theorem scalar_of_comm_unitary {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → U * C = C * U) : ∃ ζ : ℂ, C = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  open scoped Matrix.Norms.L2Operator in
  have hall : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * C = C * M := by
    intro M
    have hM : M ∈ Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [CStarAlgebra.span_unitary]; trivial
    induction hM using Submodule.span_induction with
    | mem U hU => exact h U hU.1
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
    | smul c a _ ha => rw [Matrix.smul_mul, Matrix.mul_smul, ha]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j _ => hall _)
  exact ⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem scalar_of_comm {n : ℕ} (G s B A : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) (hs : s = 1 ∨ s = -1)
    (hB : IsONBasis G s B p) (hA : Aᴴ * G * A = G)
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * G * M = G → M * A = A * M) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨ε, hε, h1, h2⟩ := hB
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with h | h <;> simp [h.1]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hdet
  have hBu : IsUnit B.det := (right_ne_zero_of_mul hdet).isUnit
  have hG : G.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have i1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBu
  have i2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Bᴴ * G * B = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have e : B⁻¹ * (s * B) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
      rw [h2, ← Matrix.mul_assoc, i1, Matrix.one_mul]
    rcases hs with rfl | rfl
    · exact ⟨1, by rw [h1, ← e, Matrix.one_mul, i1, one_smul]⟩
    · exact ⟨-1, by rw [h1, ← e, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, i1, neg_smul, one_smul]⟩
  have hG' : (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ = G := by
    calc _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [i2]; simp
  obtain ⟨ζ, hζ⟩ := scalar_of_comm_unitary (B⁻¹ * A * B) fun U hU => by
    have k := h (B * U * B⁻¹) (by
      calc _ = (B⁻¹)ᴴ * (Uᴴ * (Bᴴ * G * B) * U) * B⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by
            rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
        _ = G := hG')
    calc U * (B⁻¹ * A * B) = (B⁻¹ * B) * U * (B⁻¹ * A * B) := by rw [i1, Matrix.one_mul]
      _ = B⁻¹ * (B * U * B⁻¹ * A) * B := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * A * B * U * (B⁻¹ * B) := by rw [k]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [i1, Matrix.mul_one]
  have hAζ : A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc A = (B * B⁻¹) * A * (B * B⁻¹) := by rw [i2, Matrix.one_mul, Matrix.mul_one]
      _ = B * (B⁻¹ * A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hζ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, i2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  · refine ⟨ζ, ?_, hAζ⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG0 : G ≠ 0 := fun e => hG (by rw [e, Matrix.det_zero])
    rw [hAζ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at hA
    have e : ζ * star ζ = 1 := by
      by_contra hne
      apply hG0
      have : (ζ * star ζ - 1) • G = 0 := by rw [sub_smul, hA, one_smul, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have e2 : ‖ζ‖ * ‖ζ‖ = 1 := by simpa using congrArg norm e
    nlinarith [norm_nonneg ζ]

theorem center_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  intro D θ hθ S x hx z _ hz τ
  obtain ⟨p, hp⟩ := hx.onb τ
  refine scalar_of_comm (gramAt D S τ) (x.s τ) (x.B τ) _ p (hx.pm τ) hp
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S z τ) fun M hM => ?_
  have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (g := M) hM
  have hc := congrArg (infMat D.sp.cm.sig S.gram (θ τ)) (Subgroup.mem_center_iff.1 hz (atTau θ S τ M))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, ha.2.1] at hc
  exact hc

end GlobalTheory.CenterScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  first | exact @GlobalTheory.CenterScalar.center_scalar | exact GlobalTheory.CenterScalar.center_scalar | (intros; apply GlobalTheory.CenterScalar.center_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

theorem pair_eq_dot (n : ℕ) (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iA *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * W.gram i j * (o.qA *ᵥ y) j := by
  have hq : W.gram * o.qA = o.iAᴴ * B.gram := by
    rw [OrthDec.qA, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W)]
  rw [pair_eq_dot, pair_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hq]

theorem pair_iB {B W H : HSp D} (o : OrthDec B W H) (x : Fin H.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iB *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * H.gram i j * (o.qB *ᵥ y) j :=
  pair_iA o.symm x y

theorem split_vec {B W H : HSp D} (o : OrthDec B W H) (y : Fin B.rank → D.host.E) :
    o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.iA_qA_add, Matrix.one_mulVec]

theorem qA_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]

theorem qB_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add]

theorem iA_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) {LW : Lat W} (LH : Lat H) {x : Fin W.rank → D.host.E}
    (hx : x ∈ LW) : o.iA *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨x, hx, 0, zero_mem _, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem iB_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) {LH : Lat H} {x : Fin H.rank → D.host.E}
    (hx : x ∈ LH) : o.iB *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨0, zero_mem _, x, hx, by rw [Matrix.mulVec_zero, zero_add]⟩

theorem isLattice_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H)
    (hW : Submodule.IsLattice D.host.E LW) (hH : Submodule.IsLattice D.host.E LH) :
    Submodule.IsLattice D.host.E (sumLatO o LW LH) := by
  exact Submodule.IsLattice.of_fg D.host.E ((hW.fg.map _).sup (hH.fg.map _))

theorem selfDual_sumLatO : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H),
    IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  intro D B W H o LW LH hW hH
  refine ⟨isLattice_sumLatO o LW LH hW.1 hH.1, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := (mem_sumLatO o LW LH y).1 hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sumLatO o LW LH x).1 hx
    obtain ⟨b₁, hb₁⟩ := (hW.2 y₁).1 hy₁ x₁ hx₁
    obtain ⟨b₂, hb₂⟩ := (hH.2 y₂).1 hy₂ x₂ hx₂
    refine ⟨b₁ + b₂, ?_⟩
    have e : ∑ i, ∑ j, star ((o.iA *ᵥ x₁ + o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j =
        ∑ i, ∑ j, star ((o.iA *ᵥ x₁) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j +
          ∑ i, ∑ j, star ((o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, star_add]
      ring
    rw [e, pair_iA, pair_iB, qA_split, qB_split, ← hb₁, ← hb₂]
    push_cast
    ring
  · have hA : o.qA *ᵥ y ∈ LW := (hW.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iA_mem_sumLatO o LH hx)
      exact ⟨b, hb.trans (pair_iA o x y)⟩
    have hB : o.qB *ᵥ y ∈ LH := (hH.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iB_mem_sumLatO o LW hx)
      exact ⟨b, hb.trans (pair_iB o x y)⟩
    rw [← split_vec o y]
    exact (mem_sumLatO o LW LH _).2 ⟨_, hA, _, hB, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDualStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthDecSumLattice_selfDual : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H), IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | exact GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | (intros; apply GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

def conjJAt (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u →ₗ[ℂ] ℂ where
  toFun η := star (tr.J η z)
  map_add' η η' := by simp [map_add (f := _)]
  map_smul' c η := by simp [map_smulₛₗ]

def rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (conjJAt tr z))

theorem inner_rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) (η : X.Vpi u) :
    ⟪η, rieszJ tr z⟫_ℂ = tr.J η z := by
  rw [← inner_conj_symm]
  simp [rieszJ, conjJAt]


variable (X) in
def RepM (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ Formalism.L2.SG.ColDict.qA X wt j = ∑ i, ιA.symm (M i j) • Formalism.L2.SG.ColDict.qA X wt i

end GlobalTheory.Core.Mi

end

namespace GlobalTheory.Core.Mi

section Helpers

variable {D : D7}

theorem unitaryAdelicPointFiniteMatrix_base_space_mul (a b : GA D (D.sp.X 0)) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) =
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointFiniteMatrix_base_space_one : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) = 1 := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_base_space_mul (θ : InfFam D) (a b : GA D (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) τ =
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b τ := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointInfiniteMatrices_base_space_one (θ : InfFam D) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) τ = 1 := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, map_one, Units.val_one]
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_eq_one_of_finite (θ : InfFam D) (a : GA D (D.sp.X 0)) (ha : a ∈ GfC (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 := by
  have h1 : Formalism.L2.Theta.infHom (D.sp.X 0) a = 1 := ha
  unfold Formalism.L2.Theta.infHom at h1
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have h2 := congrArg (fun x : GL (Fin (D.sp.X 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => ((x.1).map (θ τ))) h1
  simp only [MonoidHom.comp_apply, Units.val_one] at h2
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = (M.map (infPart D)).map (θ τ) := fun M => by ext; rfl
  rw [e]
  have h3 : ((Formalism.L2.Theta.matHom (D.sp.X 0)) a).1.map (infPart D) =
      ((Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom)
        ((Formalism.L2.Theta.matHom (D.sp.X 0)) a) : GL _ _).1 := rfl
  rw [h3, h2]
  simp [Matrix.reindex_apply]

end Helpers

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem toH_mul {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D}
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (a b : GA D A) :
    B.toH (a * b) = B.toH a * B.toH b := by
  unfold SBes.toH
  ext <;> simp [map_mul]

theorem RepM_cancel {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F}
    {h k : X.B.I.Gf} {A M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)}
    (hA : RepM X wt ιA h A) (hAM : RepM X wt ιA (h * k) (A * M)) : RepM X wt ιA k M := by
  intro j
  have hmul : X.B.I.fmat (h * k) = X.B.I.fmat h * X.B.I.fmat k := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat h⁻¹ * X.B.I.fmat h = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j) =
      X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hAM j, Matrix.mulVec_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec_smul, hA, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  calc X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j
      = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l)) := by rw [key]
    _ = _ := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem span_rieszJ {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    Submodule.span ℂ (Set.range fun y => rieszJ tr (F.val0.eY y)) = ⊤ := by
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro η hη
  apply tr.J_injective c
  rw [map_zero]
  funext z
  obtain ⟨y, rfl⟩ := F.val0.eY.surjective z
  rw [← inner_rieszJ]
  exact (Submodule.mem_orthogonal' _ _).1 hη _ (Submodule.subset_span ⟨y, rfl⟩)

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem colDictL_eY_symm {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (c : (D.mem u).C.cls 0)
    (w : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) :
    Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) = tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w := by
  have : Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) (F.val0.eY (F.val0.eY.symm w)) := rfl
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.Core.Mi
end
