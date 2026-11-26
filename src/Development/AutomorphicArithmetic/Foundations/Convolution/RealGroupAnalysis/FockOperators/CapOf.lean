module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockOps
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

private def stab {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) :
    Subalgebra ℂ (Module.End ℂ (S4 F)) where
  carrier := {T | ∀ φ ∈ Fock δ, T φ ∈ Fock δ}
  mul_mem' := fun ha hb φ h => ha _ (hb φ h)
  add_mem' := fun ha hb φ h => Submodule.add_mem _ (ha φ h) (hb φ h)
  algebraMap_mem' := fun c φ h => by
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c h

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.fockOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Ops F), ∀ φ ∈ Fock D.δ, (∀ w i, O.x w i φ ∈ Fock D.δ) ∧ (∀ w i, O.d w i φ ∈ Fock D.δ) ∧ (∀ w, O.e D.δ w φ ∈ Fock D.δ) ∧
    (∀ w, O.f D.δ w φ ∈ Fock D.δ) ∧ (∀ w, O.h w φ ∈ Fock D.δ) ∧ (∀ τ i j, O.dE D τ i j φ ∈ Fock D.δ) ∧ ∀ Y, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O
  have hx : ∀ w i, O.x w i ∈ stab D.δ := fun w i => (fkLe F D.δ O).1 w i
  have hd : ∀ w i, O.d w i ∈ stab D.δ := by
    intro w i φ hφ
    obtain ⟨Λ, m, h⟩ := fockEx F E D O {φ} (Set.finite_singleton φ)
      (fun ψ hψ => (Set.mem_singleton_iff.1 hψ) ▸ hφ)
    exact (fkLe F D.δ O).2 _ inf_le_left (m + 1)
      (fkD F D.δ O _ inf_le_left m w i φ (h φ (Set.mem_singleton φ)))
  have he : ∀ w, O.e D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (mul_mem (hx w 2) (hx w 2))
      (Subalgebra.smul_mem _ (mul_mem (hx w 3) (hx w 3)) _)) (mul_mem (hx w 1) (hx w 0))) _
  have hf : ∀ w, O.f D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (Subalgebra.smul_mem _ (mul_mem (hd w 2) (hd w 2)) _)
      (Subalgebra.smul_mem _ (mul_mem (hd w 3) (hd w 3)) _)) (mul_mem (hd w 1) (hd w 0))) _
  have hh : ∀ w, O.h w ∈ stab D.δ := fun w =>
    add_mem (sum_mem fun i _ => mul_mem (hx w i) (hd w i)) (ofNat_mem _ 2)
  have hX : ∀ τ a b, O.X D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hx _ 1
    · exact add_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact sub_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact hx _ 0
  have hDX : ∀ τ a b, O.DX D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hd _ 1
    · exact Subalgebra.smul_mem _ (add_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact Subalgebra.smul_mem _ (sub_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact hd _ 0
  have hE : ∀ τ i j, O.dE D τ i j ∈ stab D.δ := by
    intro τ i j
    refine sub_mem (neg_mem ?_) (sum_mem fun b _ => mul_mem (hX τ j b) (hDX τ i b))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hL : ∀ Y, O.dL D Y ∈ stab D.δ := fun Y =>
    sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => Subalgebra.smul_mem _ (hE τ i j) _
  intro φ hφ
  exact ⟨fun w i => hx w i φ hφ, fun w i => hd w i φ hφ, fun w => he w φ hφ, fun w => hf w φ hφ,
    fun w => hh w φ hφ, fun τ i j => hE τ i j φ hφ, fun Y => hL Y φ hφ⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LamEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftLin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma th_add {F : Type} [Field F] [NumberField F] (a b : S4 F) :
    Th (a + b).1 = Th a.1 + Th b.1 := by
  have ha := (poisson_of_mem_schwartzBruhatPi a.2).1.of_norm
  have hb := (poisson_of_mem_schwartzBruhatPi b.2).1.of_norm
  exact ha.tsum_add hb

private lemma th_smul {F : Type} [Field F] [NumberField F] (c : ℂ) (a : S4 F) :
    Th (c • a).1 = c * Th a.1 :=
  tsum_mul_left

theorem UpperTheory.ConvolutionTheory.R2.Fo.liftLin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
    (∀ f' ∈ π.V, lift W M (f + f').1 φ = lift W M f.1 φ + lift W M f'.1 φ) ∧ (∀ φ' ∈ Fock D.δ, lift W M f.1 (φ + φ') = lift W M f.1 φ + lift W M f.1 φ') ∧
    ∀ c : ℂ, lift W M (c • f).1 φ = c • lift W M f.1 φ ∧ lift W M f.1 (c • φ) = c • lift W M f.1 φ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  have hI := fun f hf φ hφ h => (UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h).1
  refine ⟨fun f' hf' => ?_, fun φ' hφ' => ?_, fun c => ⟨?_, ?_⟩⟩
  · funext h
    have e : ∀ x, (f + f').1 x = f.1 x + f'.1 x := fun x => rfl
    simp only [lift, Pi.add_apply, e, add_mul]
    exact integral_add (hI f hf φ hφ h) (hI f' hf' φ hφ h)
  · funext h
    simp only [lift, Pi.add_apply, map_add (f := _), LinearMap.add_apply, th_add, mul_add]
    exact integral_add (hI f hf φ hφ h) (hI f hf φ' hφ' h)
  · funext h
    have e : ∀ x, (c • f).1 x = c * f.1 x := fun x => rfl
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, mul_assoc]
    exact integral_const_mul _ _
  · funext h
    simp only [lift, Pi.smul_apply, smul_eq_mul, map_smul, th_smul, mul_left_comm _ c]
    exact integral_const_mul _ _
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.lamEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∃ Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ := by
  intro F E _ _ _ _ _ _ _ D W M π
  have hs := UpperTheory.ConvolutionTheory.R2.smooth F E D W M π
  have hl := UpperTheory.ConvolutionTheory.R2.Fo.liftLin F E D W M π
  let G : π.V → Fock D.δ → Sm E 2 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose
  have hG : ∀ f φ, (G f φ).1 = lift W M f.1.1 φ.1 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose_spec
  let L : π.V →ₗ[ℂ] Fock D.δ →ₗ[ℂ] Sm E 2 := LinearMap.mk₂ ℂ G
    (fun f f' φ => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).1 f'.1 f'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).1
      rw [Submodule.coe_smul, hG, hG]
      exact h))
    (fun f φ φ' => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).2.1 φ'.1 φ'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).2
      rw [Submodule.coe_smul, hG, hG]
      exact h))
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective π.V.subtype (Submodule.ker_subtype _)
  obtain ⟨s, hs'⟩ := LinearMap.exists_leftInverse_of_injective (Fock D.δ).subtype (Submodule.ker_subtype _)
  refine ⟨L.compl₁₂ r s, fun f hf φ hφ => ?_⟩
  have e1 : r f = ⟨f, hf⟩ := LinearMap.congr_fun hr ⟨f, hf⟩
  have e2 : s φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hs' ⟨φ, hφ⟩
  rw [LinearMap.compl₁₂_apply, e1, e2]
  exact hG _ _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapLam
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftNegForm
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w, O.f D.δ w * W.Om (wW F) = -(W.Om (wW F) * O.e D.δ w) := by
  intro F E _ _ _ _ _ _ _ D W O w
  have hc : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have h2 : ∀ i j, O.d w i * O.d w j * W.Om (wW F) =
      W.Om (wW F) * (O.p D.δ w i * O.p D.δ w j) := fun i j => by
    calc
      _ = O.d w i * (W.Om (wW F) * O.p D.δ w j) := by rw [mul_assoc, dW F E D W O w j]
      _ = (O.d w i * W.Om (wW F)) * O.p D.δ w j := by rw [mul_assoc]
      _ = _ := by rw [dW F E D W O w i, mul_assoc]
  have comm : O.x w 0 * O.x w 1 = O.x w 1 * O.x w 0 := (weyl F O w w 0 1).1
  have p0 : O.p D.δ w 0 = (-cc) • O.x w 1 := rfl
  have p1 : O.p D.δ w 1 = (-cc) • O.x w 0 := rfl
  have p2 : O.p D.δ w 2 = (2 * cc) • O.x w 2 := rfl
  have p3 : O.p D.δ w 3 = (-2 * cw w (rt D.δ) * cc) • O.x w 3 := rfl
  have key : (4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
      (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) -
      O.p D.δ w 1 * O.p D.δ w 0 = cc • O.e D.δ w := by
    rw [p0, p1, p2, p3, Ops.e]
    simp only [smul_mul_smul_comm, comm]
    match_scalars <;> field_simp <;> ring
  have move : ((4 : ℂ)⁻¹ • (O.d w 2 * O.d w 2) - (4 * cw w (rt D.δ))⁻¹ • (O.d w 3 * O.d w 3) -
      O.d w 1 * O.d w 0) * W.Om (wW F) =
      W.Om (wW F) * ((4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
        (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) - O.p D.δ w 1 * O.p D.δ w 0) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, h2]
  rw [Ops.f, smul_mul_assoc, move, key, mul_smul_comm, smul_smul,
    neg_mul, inv_mul_cancel₀ hcc, neg_smul, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.SetIntegralMulRight
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma countable_gam (K : Type) [Field K] [NumberField K] : Countable (Gam K) := by
  haveI : Countable K := by
    have : Module.Finite ℚ K := inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ K
    exact hf.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Function.Injective.countable (f := fun g => (g.1 : Matrix (Fin 2) (Fin 2) K)) Subtype.val_injective
  unfold Gam
  exact (Set.countable_range (ratS K)).to_subtype

private lemma setIntegral_mul_right (K : Type) [Field K] [NumberField K] (M : Meas K) (u : G1 K → ℂ)
    (hu : ∀ γ g, u (ratS K γ * g) = u g) (k : G1 K) :
    ∫ g in M.D, u (g * k) ∂M.μ = ∫ g in M.D, u g ∂M.μ := by
  haveI := M.haar
  haveI := M.right
  haveI := countable_gam K
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 K → G1 K) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam K) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam K) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 K → G1 K) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv

theorem UpperTheory.ConvolutionTheory.R2.Fo.moveG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ), (∀ γ g, f (ratGL F 2 γ * g) = f g) → ∀ (φ : S4 F) (g₀ : G1 F),
    lift W M f (W.Om g₀ φ) = lift W M (fun x => f (x * gl g₀⁻¹)) φ := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀
  funext h
  have hu : ∀ γ g, (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) (ratS F γ * g) =
      (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) g := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * gl g₀⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := setIntegral_mul_right F M (fun g : G1 F => f (gl g * dM (nu F h) * gl g₀⁻¹) * Th (W.Om g (W.L h φ)).1) hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹ = gl g * dM (nu F h) := by
    have hi : gl g₀⁻¹ = (gl g₀)⁻¹ := map_inv Matrix.SpecialLinearGroup.toGL g₀
    rw [gl_mul, gl_cD, hi]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * gl g₀⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StableOfOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private theorem wInv_val : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, UpperTheory.ConvolutionTheory.R2.wW_val]
  simp

private theorem orth_w : InfOrth (wW F) := by
  intro i j
  rw [UpperTheory.ConvolutionTheory.R2.wW_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_wInv : InfOrth (wW F)⁻¹ := by
  intro i j
  rw [wInv_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_unitary (h : G1 F) (ho : InfOrth h) :
    (GeneralLinearGroup.map (TR.pInf F) (gl h)).val ∈ Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext1 i j
  have e : TR.pInf F ((h.1 * h.1ᵀ) i j) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) :=
    congrArg (TR.infEq F).symm (ho i j)
  have e1 : ((GeneralLinearGroup.map (TR.pInf F) (gl h)).val * star (GeneralLinearGroup.map (TR.pInf F) (gl h)).val) i j =
      TR.pInf F ((h.1 * h.1ᵀ) i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
      Matrix.transpose_apply]
    rfl
  have e2 : TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e, e2]

private theorem rt_split (g : GL (Fin 2) (A F)) :
    TR.rt F 2 g = TR.rt F 2 (TR.infGL F 2 (GeneralLinearGroup.map (TR.pInf F) g)) *
      TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) g)) := by
  rw [← map_mul, TR.infGL_mul_finGL]

private theorem stable_of_orth (π : TR.CuspSub F 2) {h : G1 F} (ho : InfOrth h) {f : TR.Sm F 2} (hf : f ∈ π.V) :
    TR.rt F 2 (gl h) f ∈ π.V := by
  rw [rt_split, Module.End.mul_apply]
  have h1 := π.stable (.fin (GeneralLinearGroup.map (pFin F) (gl h))) f hf
  have h2 := π.stable (.cpt ⟨_, orth_unitary h ho⟩) _ h1
  have e : Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2) = GeneralLinearGroup.map (TR.pInf F) (gl h) :=
    Units.ext rfl
  change TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2)))
    (TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) (gl h))) f) ∈ π.V at h2
  rwa [e] at h2

private theorem ad_eop (v : InfinitePlace F) :
    TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F))) := by
  have hy : (GeneralLinearGroup.map (TR.pInf F) (gl (wW F))).val = !![0, 1; -1, 0] := by
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.ConvolutionTheory.R2.wW_val]
  have hyi : ((GeneralLinearGroup.map (TR.pInf F) (gl (wW F)))⁻¹).val = !![0, -1; 1, 0] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hfin : ∀ k : GL (Fin 2) (Af F), TR.rt F 2 (finGL F 2 k) * TR.Eop v 0 1 = TR.Eop v 0 1 * TR.rt F 2 (finGL F 2 k) :=
    fun k => (TR.lie_rt_fin _ k).symm
  rw [rt_split (gl (wW F)), mul_assoc, hfin, ← mul_assoc, TR.Cen.rt_Eop, hy, hyi]
  simp [Fin.sum_univ_two, mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.adW :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, TR.rt F 2 (gl (wW F)) f ∈ π.V ∧ TR.rt F 2 (gl (wW F)⁻¹) f ∈ π.V) ∧
    (∀ v, TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F)))) ∧ InfOrth (wW F)⁻¹ := by
  intro F _ _ _
  exact ⟨fun π f hf => ⟨stable_of_orth π orth_w hf, stable_of_orth π orth_wInv hf⟩, ad_eop, orth_wInv⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem lift_neg_form {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (M : Meas F) (u : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) :
    lift W M (fun x => -u x) φ h = -lift W M u φ h := by
  unfold lift
  simp only [neg_mul]
  exact integral_neg _

private theorem lift_neg_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (M : Meas F) (u : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) :
    lift W M u (-φ) h = -lift W M u φ h := by
  unfold lift
  have e : ∀ χ : S4 F, Th (-χ).1 = -Th χ.1 := fun χ => by
    unfold Th
    exact tsum_neg
  simp only [map_neg, e, mul_neg]
  exact integral_neg _

theorem UpperTheory.ConvolutionTheory.R2.Fo.moveF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F), MoveE O W M π →
    ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ w h, lift W M f.1 (O.f D.δ w φ) h = -lift W M (TR.Eop w 1 0 f).1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π O hE f hf φ hφ v h
  obtain ⟨hV, hAd, hO⟩ := UpperTheory.ConvolutionTheory.R2.Fo.adW F
  have left : ∀ u ∈ π.V, ∀ γ g, u.1 (ratGL F 2 γ * g) = u.1 g := fun u hu => (π.cusp u hu).1.left
  set f' := TR.rt F 2 (gl (wW F)⁻¹) f with hf'def
  have hf' : f' ∈ π.V := (hV π f hf).2
  set φ' := W.Om (wW F)⁻¹ φ with hφ'def
  have hφ' : φ' ∈ Fock D.δ := by
    obtain ⟨U, hU, -, hk⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφ {(wW F)⁻¹} isCompact_singleton
      (by rintro k rfl; exact hO)
    exact hU (hk _ rfl)
  set f'' := TR.Eop v 0 1 f' with hf''def
  have hf'' : f'' ∈ π.V := π.stable (.lie _) f' hf'
  have e1 : φ = W.Om (wW F) φ' := by
    rw [hφ'def, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e2 : O.f D.δ v φ = -W.Om (wW F) (O.e D.δ v φ') := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ') (UpperTheory.ConvolutionTheory.R2.Fo.fW F E D W O v)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at this
    rw [← e1] at this
    exact this
  have e3 : lift W M f.1 (W.Om (wW F) (O.e D.δ v φ')) = lift W M f'.1 (O.e D.δ v φ') :=
    UpperTheory.ConvolutionTheory.R2.Fo.moveG F E D W M f.1 (left f hf) _ _
  have e4 : lift W M f''.1 φ' = lift W M (TR.rt F 2 (gl (wW F)) f'').1 φ := by
    have := UpperTheory.ConvolutionTheory.R2.Fo.moveG F E D W M f''.1 (left f'' hf'') φ (wW F)⁻¹
    rw [inv_inv] at this
    exact this
  have e5 : TR.rt F 2 (gl (wW F)) f'' = -TR.Eop v 1 0 f := by
    have a := congrArg (fun T : Module.End ℂ (TR.Sm F 2) => T f') (hAd v)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at a
    have b : TR.rt F 2 (gl (wW F)) f' = f := by
      rw [hf'def, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
    rw [b] at a
    exact a
  have e6 : (TR.rt F 2 (gl (wW F)) f'').1 = fun x => -(TR.Eop v 1 0 f).1 x := by
    rw [e5]; rfl
  rw [e2, lift_neg_data, e3, hE f' hf' φ' hφ' v h, neg_neg, e4, e6, lift_neg_form]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.EopLift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem coord_half {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ τ : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord σ (atEmb τ 1) - Complex.I * coord σ (atEmb τ Complex.I)) = if σ = τ then 1 else 0 := by
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · subst e
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h' =>
        InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
          (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h'))
      obtain rfl : σ = ComplexEmbedding.conjugate τ := by
        rw [← e]; exact (star_star σ).symm
      rw [if_neg hne, GlobalTheory.IsoPull.coord_conj, GlobalTheory.IsoPull.coord_conj, coord_atEmb, coord_atEmb]
      simp
  · rw [GlobalTheory.IsoPull.coord_atEmb_of_ne h, GlobalTheory.IsoPull.coord_atEmb_of_ne h, if_neg (fun e => h (by rw [e]))]
    simp

private theorem coord_single {E : Type} [Field E] (σ : E →+* ℂ) (i j k l : Fin 2) (c : Cinf E) :
    coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) = if k = i ∧ l = j then coord σ c else 0 := by
  change coord σ (Matrix.single i j c k l) = _
  rw [Matrix.single_apply]
  by_cases h : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (fun e => h ⟨e.1.symm, e.2.symm⟩), map_zero]

private theorem half_comb {E N : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [AddCommGroup N] [Module ℂ N]
    (R : (E →+* ℂ) → Fin 2 → Fin 2 → N) (τ : E →+* ℂ) (i j : Fin 2) (x y : N)
    (hx : x = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ 1)) : Lie E 2) k l) • R σ k l)
    (hy : y = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ Complex.I)) : Lie E 2) k l) • R σ k l) :
    (1 / 2 : ℂ) • (x - Complex.I • y) = R τ i j := by
  have e : ∀ c : Cinf E, ∀ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) • R σ k l = coord σ c • R σ i j := by
    intro c σ
    simp only [coord_single, ite_smul, zero_smul, ite_and]
    simp
  simp only [e] at hx hy
  have hz : ∀ σ : E →+* ℂ, (1 / 2 : ℂ) • (coord σ (atEmb τ 1) • R σ i j - Complex.I • coord σ (atEmb τ Complex.I) • R σ i j) =
      if σ = τ then R σ i j else 0 := by
    intro σ
    rw [smul_smul, ← sub_smul, smul_smul, coord_half]
    split_ifs <;> simp
  rw [hx, hy, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [hz]
  simp

theorem UpperTheory.ConvolutionTheory.R2.Fo.eopLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π →
    ∀ (τ : E →+* ℂ) i j, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, Eop τ i j (Λ f φ) = Λ f (O.dE D τ i j φ) + if i = j then Λ (TR.Eop (pl F τ) 1 1 f) φ else 0 := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL τ i j f hf φ hφ
  have hE : ∀ σ : E →+* ℂ, TR.Eop (pl F σ) 1 1 f ∈ π.V := fun σ => π.stable (.lie _) f hf
  have key : ∀ Y : Lie E 2, lie E 2 Y (Λ f φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) •
      (Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) := by
    intro Y
    have h1 := (fockOps F E D O φ hφ).2.2.2.2.2.2 Y
    have h2 : lie E 2 Y (Λ f φ) = Λ f (O.dL D Y φ) +
        ∑ σ : E →+* ℂ, coord σ (Y 0 0 + Y 1 1) • Λ (TR.Eop (pl F σ) 1 1 f) φ := by
      refine Subtype.ext (funext fun h => ?_)
      rw [hL f hf φ hφ (Λ f φ) (hΛ f hf φ hφ) Y h]
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, hΛ _ (hE _) φ hφ, hΛ f hf _ h1]
    have h3 : Λ f (O.dL D Y φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) • Λ f (O.dE D σ k l φ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Ops.dL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [h2, h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.sum_univ_two, smul_add, map_add (f := _), add_smul]
    simp
    abel
  have hEop : Eop τ i j = (1 / 2 : ℂ) • (lie E 2 (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • lie E 2 (toL (Matrix.single i j (atEmb τ Complex.I)))) := rfl
  rw [hEop]
  exact half_comb (fun σ k l => Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) τ i j _ _
    (key _) (key _)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XaCommCoord
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PForm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma p_form {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w : InfinitePlace F) (i : Fin 4) : ∃ (c : ℂ) (k : Fin 4), O.p δ w i = c • O.x w k := by
  fin_cases i
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private lemma p_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) (δ : F)
    (w w' : InfinitePlace F) (i j : Fin 4) :
    O.p δ w i * O.p δ w' j = O.p δ w' j * O.p δ w i := by
  obtain ⟨c, k, h⟩ := p_form O δ w i
  obtain ⟨c', k', h'⟩ := p_form O δ w' j
  have hx : O.x w k * O.x w' k' = O.x w' k' * O.x w k := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w k (O.x w' k' φ)).1 v = (O.x w' k' (O.x w k φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  rw [h, h']
  simp only [smul_mul_smul, hx, mul_comm c c']

theorem UpperTheory.ConvolutionTheory.R2.Fo.dComm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w w' i j, O.d w i * O.d w' j = O.d w' j * O.d w i := by
  intro F E _ _ _ _ _ _ _ D W O w w' i j
  have hinv : W.Om (wW F) * W.Om (wW F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : O.d w i * O.d w' j * W.Om (wW F) = O.d w' j * O.d w i * W.Om (wW F) := by
    calc O.d w i * O.d w' j * W.Om (wW F)
        = O.d w i * (O.d w' j * W.Om (wW F)) := mul_assoc _ _ _
      _ = O.d w i * (W.Om (wW F) * O.p D.δ w' j) := congrArg (O.d w i * ·) (dW F E D W O w' j)
      _ = (O.d w i * W.Om (wW F)) * O.p D.δ w' j := (mul_assoc _ _ _).symm
      _ = (W.Om (wW F) * O.p D.δ w i) * O.p D.δ w' j := congrArg (· * O.p D.δ w' j) (dW F E D W O w i)
      _ = W.Om (wW F) * (O.p D.δ w i * O.p D.δ w' j) := mul_assoc _ _ _
      _ = W.Om (wW F) * (O.p D.δ w' j * O.p D.δ w i) := by rw [p_comm O D.δ w w' i j]
      _ = (W.Om (wW F) * O.p D.δ w' j) * O.p D.δ w i := (mul_assoc _ _ _).symm
      _ = (O.d w' j * W.Om (wW F)) * O.p D.δ w i := congrArg (· * O.p D.δ w i) (dW F E D W O w' j).symm
      _ = O.d w' j * (W.Om (wW F) * O.p D.δ w i) := mul_assoc _ _ _
      _ = O.d w' j * (O.d w i * W.Om (wW F)) := congrArg (O.d w' j * ·) (dW F E D W O w i).symm
      _ = O.d w' j * O.d w i * W.Om (wW F) := (mul_assoc _ _ _).symm
  calc O.d w i * O.d w' j
      = O.d w i * O.d w' j * (W.Om (wW F) * W.Om (wW F)⁻¹) := by rw [hinv, mul_one]
    _ = O.d w i * O.d w' j * W.Om (wW F) * W.Om (wW F)⁻¹ := (mul_assoc _ _ _).symm
    _ = O.d w' j * O.d w i * W.Om (wW F) * W.Om (wW F)⁻¹ := by rw [key]
    _ = O.d w' j * O.d w i * (W.Om (wW F) * W.Om (wW F)⁻¹) := mul_assoc _ _ _
    _ = O.d w' j * O.d w i := by rw [hinv, mul_one]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section Abstract

variable {A : Type*} [Ring A] [Algebra ℂ A]

private def Xa (θ : ℂ) (x : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![x 1, x 2 + θ • x 3], ![x 2 - θ • x 3, x 0]]

private noncomputable def Da (θ : ℂ) (d : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![d 1, (2 : ℂ)⁻¹ • (d 2 + θ⁻¹ • d 3)], ![(2 : ℂ)⁻¹ • (d 2 - θ⁻¹ • d 3), d 0]]

private lemma Xa_comm_coord (θ : ℂ) {x y : Fin 4 → A} (h : ∀ i j, Commute (x i) (y j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Xa θ x a b) (y j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact (h 2 j).add_left ((h 3 j).smul_left θ)
  · exact (h 2 j).sub_left ((h 3 j).smul_left θ)
  · exact h 0 j

private lemma Xa_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Xa θ x a b) (Xa θ x c d) := by
  have h' := Xa_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact (h' 2).add_right ((h' 3).smul_right θ)
  · exact (h' 2).sub_right ((h' 3).smul_right θ)
  · exact h' 0

private lemma Da_comm_coord (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Da θ x a b) (x j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact ((h 2 j).add_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact ((h 2 j).sub_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact h 0 j

private lemma Da_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Da θ x a b) (Da θ x c d) := by
  have h' := Da_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact ((h' 2).add_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact ((h' 2).sub_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact h' 0

private lemma Da_Xa (θ : ℂ) (hθ : θ ≠ 0) {x d : Fin 4 → A}
    (hw : ∀ i j, d i * x j = x j * d i + if i = j then 1 else 0) (a b c e : Fin 2) :
    Da θ d a b * Xa θ x c e = Xa θ x c e * Da θ d a b + if a = c ∧ b = e then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp only [Xa, Da, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, hw] <;>
    simp <;> match_scalars <;> field_simp <;> ring

private lemma Xa_det (θ c : ℂ) (hc : θ ^ 2 = c) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) :
    Xa θ x 0 1 * Xa θ x 1 0 - Xa θ x 0 0 * Xa θ x 1 1 = x 2 * x 2 - c • (x 3 * x 3) - x 1 * x 0 := by
  have h32 : x 3 * x 2 = x 2 * x 3 := h 3 2
  subst hc
  simp only [Xa, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> ring

private lemma Da_det (θ c : ℂ) (hθ : θ ≠ 0) (hc : θ ^ 2 = c) {d : Fin 4 → A} (h : ∀ i j, Commute (d i) (d j)) :
    Da θ d 0 1 * Da θ d 1 0 - Da θ d 0 0 * Da θ d 1 1 =
      (4 : ℂ)⁻¹ • (d 2 * d 2) - (4 * c)⁻¹ • (d 3 * d 3) - d 1 * d 0 := by
  have h32 : d 3 * d 2 = d 2 * d 3 := h 3 2
  subst hc
  simp only [Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> field_simp <;> ring

private lemma Xa_Da_sum (θ : ℂ) (hθ : θ ≠ 0) (x d : Fin 4 → A) :
    ∑ a, ∑ b, Xa θ x a b * Da θ d a b = ∑ i, x i * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four, Xa, Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp <;> ring

end Abstract

theorem UpperTheory.ConvolutionTheory.R2.Fo.weylX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (τ : E →+* ℂ),
    (∀ a b c d, O.X D τ a b * O.X D τ c d = O.X D τ c d * O.X D τ a b) ∧ (∀ a b c d, O.DX D τ a b * O.DX D τ c d = O.DX D τ c d * O.DX D τ a b) ∧
    (∀ a b c d, O.DX D τ a b * O.X D τ c d = O.X D τ c d * O.DX D τ a b + if a = c ∧ b = d then 1 else 0) ∧
    O.e D.δ (pl F τ) = cc • (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1) ∧
    O.f D.δ (pl F τ) = (-cc⁻¹) • (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) ∧
    O.h (pl F τ) = (∑ a, ∑ b, O.X D τ a b * O.DX D τ a b) + 2 := by
  intro F E _ _ _ _ _ _ _ D W O τ
  obtain ⟨hsq, -, hθ⟩ := (coordMk F E D).2.1 τ
  have hx : ∀ i j, Commute (O.x (pl F τ) i) (O.x (pl F τ) j) := fun i j => (weyl F O _ _ i j).1
  have hd : ∀ i j, Commute (O.d (pl F τ) i) (O.d (pl F τ) j) := fun i j => dComm F E D W O _ _ i j
  have hw : ∀ i j, O.d (pl F τ) i * O.x (pl F τ) j = O.x (pl F τ) j * O.d (pl F τ) i + if i = j then 1 else 0 := by
    intro i j
    simpa using (weyl F O (pl F τ) (pl F τ) i j).2
  have eX : O.X D τ = Xa (τ D.θ) (O.x (pl F τ)) := rfl
  have eD : O.DX D τ = Da (τ D.θ) (O.d (pl F τ)) := rfl
  rw [eX, eD]
  refine ⟨fun a b c d => Xa_comm _ hx a b c d, fun a b c d => Da_comm _ hd a b c d,
    fun a b c d => Da_Xa _ hθ hw a b c d, ?_, ?_, ?_⟩
  · rw [Xa_det _ _ hsq hx]; rfl
  · rw [Da_det _ _ hθ hsq hd]; rfl
  · rw [Xa_Da_sum _ hθ]; rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Capelli
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capelli :
    ∀ (A : Type) [Ring A] (X D a : Fin 2 → Fin 2 → A) (q Δ h : A), (∀ i j k l, X i j * X k l = X k l * X i j) → (∀ i j k l, D i j * D k l = D k l * D i j) →
    (∀ i j k l, D i j * X k l = X k l * D i j + if i = k ∧ j = l then 1 else 0) →
    (∀ i j, a i j = -(if i = j then 1 else 0) - ∑ b, X j b * D i b) → q = X 0 1 * X 1 0 - X 0 0 * X 1 1 → Δ = D 0 1 * D 1 0 - D 0 0 * D 1 1 →
    h = (∑ i, ∑ j, X i j * D i j) + 2 →
    Δ * q - q * Δ = h ∧ a 0 0 + a 1 1 = -h ∧
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h - 2 * (q * Δ + Δ * q) := by
  intro A _ X D a q Δ h hX hD hDX ha hq hΔ hh
  have hDX' : ∀ i j k l z, D i j * (X k l * z) = X k l * (D i j * z) + if i = k ∧ j = l then z else 0 := by
    intro i j k l z
    rw [← mul_assoc, hDX, add_mul, mul_assoc]
    split_ifs <;> simp
  have hX' : ∀ i j k l z, X i j * (X k l * z) = X k l * (X i j * z) := by
    intro i j k l z
    rw [← mul_assoc, hX, mul_assoc]
  have h2 : (2 : A) = 1 + 1 := by norm_num
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  subst hq hΔ hh
  simp only [ha, Fin.sum_univ_two, h2, h01, h10, if_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    try simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_zero, zero_sub, neg_neg, mul_one, one_mul, mul_assoc, hDX, hDX', h01, h10, and_self, and_true, true_and, and_false, false_and, if_true, if_false, add_zero,
      hX 1 1 0 0, hX 1 1 0 1, hX 1 1 1 0, hX 1 0 0 0, hX 1 0 0 1, hX 0 1 0 0,
      hX' 1 1 0 0, hX' 1 1 0 1, hX' 1 1 1 0, hX' 1 0 0 0, hX' 1 0 0 1, hX' 0 1 0 0,
      hD 1 1 0 0, hD 1 1 0 1, hD 1 1 1 0, hD 1 0 0 0, hD 1 0 0 1, hD 0 1 0 0]
  all_goals abel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapAbs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem qdet_fin_two {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V) (u : ℂ) :
    Formalism.REAL.qdet X u = (algebraMap ℂ (Module.End ℂ V) u + X 0 0) * (algebraMap ℂ (Module.End ℂ V) (u - 1) + X 1 1) - X 1 0 * X 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, hp, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem four_qdet {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (u : ℂ) (w : V) :
    (4 : ℂ) • Formalism.REAL.qdet X u w = ((2 * u - 1) ^ 2 - 1) • w + (2 * (2 * u - 1)) • (X 0 0 + X 1 1) w
      + (X 0 0 + X 1 1) ((X 0 0 + X 1 1) w)
      - ((X 0 0 - X 1 1) ((X 0 0 - X 1 1) w) + (2 : ℂ) • (X 0 1 (X 1 0 w) + X 1 0 (X 0 1 w))) := by
  have r1 : X 0 0 (X 1 1 w) - X 1 1 (X 0 0 w) = 0 := by
    simpa using LinearMap.congr_fun (hX 0 0 1 1) w
  have r2 : X 0 1 (X 1 0 w) - X 1 0 (X 0 1 w) = X 0 0 w - X 1 1 w := by
    simpa using LinearMap.congr_fun (hX 0 1 1 0) w
  rw [qdet_fin_two]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_sub, map_smul]
  linear_combination (norm := module) (2 : ℂ) • r1 + (2 : ℂ) • r2

theorem UpperTheory.ConvolutionTheory.R2.Fo.capAbs :
    ∀ (V S T : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    (V₀ : Submodule ℂ V) (S₀ : Submodule ℂ S) (Λ : V →ₗ[ℂ] S →ₗ[ℂ] T) (E : Fin 2 → Fin 2 → Module.End ℂ V) (P : Fin 2 → Fin 2 → Module.End ℂ T)
    (a : Fin 2 → Fin 2 → Module.End ℂ S) (e f h : Module.End ℂ S), Formalism.REAL.GlRel E → Formalism.REAL.GlRel P →
    (∀ i j, ∀ v ∈ V₀, E i j v ∈ V₀) → (∀ i j, ∀ s ∈ S₀, a i j s ∈ S₀) → (∀ s ∈ S₀, e s ∈ S₀) → (∀ s ∈ S₀, f s ∈ S₀) →
    (∀ i j, ∀ v ∈ V₀, ∀ s ∈ S₀, P i j (Λ v s) = Λ v (a i j s) + if i = j then Λ (E 1 1 v) s else 0) →
    (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e s) = -Λ (E 0 1 v) s) → (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f s) = -Λ (E 1 0 v) s) →
    e * f - f * e = h → a 0 0 + a 1 1 = -h →
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h + 2 * (e * f + f * e) →
    ∀ u, ∀ v ∈ V₀, ∀ s ∈ S₀, Formalism.REAL.qdet P u (Λ v s) = Λ (Formalism.REAL.qdet E u v) s := by
  intro V S T _ _ _ _ _ _ V₀ S₀ Λ E P a e f h hE hP hEV haS heS hfS hPΛ heΛ hfΛ hh hz hb u v hv s hs
  have hH : ∀ w, E 0 1 (E 1 0 w) - E 1 0 (E 0 1 w) = (E 0 0 - E 1 1) w := fun w => by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) w
  have hef : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e (f s)) = Λ (E 1 0 (E 0 1 v)) s := fun v hv s hs => by
    rw [heΛ v hv _ (hfS s hs), hfΛ _ (hEV 0 1 v hv) s hs, neg_neg]
  have hfe : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f (e s)) = Λ (E 0 1 (E 1 0 v)) s := fun v hv s hs => by
    rw [hfΛ v hv _ (heS s hs), heΛ _ (hEV 1 0 v hv) s hs, neg_neg]
  have hhS : ∀ s ∈ S₀, h s ∈ S₀ := fun s hs => by
    rw [← hh]
    exact S₀.sub_mem (heS _ (hfS s hs)) (hfS _ (heS s hs))
  have hHV : ∀ v ∈ V₀, (E 0 0 - E 1 1) v ∈ V₀ := fun v hv =>
    V₀.sub_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hZV : ∀ v ∈ V₀, (E 0 0 + E 1 1) v ∈ V₀ := fun v hv =>
    V₀.add_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hhΛ : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (h s) = -Λ ((E 0 0 - E 1 1) v) s := fun v hv s hs => by
    rw [← hh, ← hH v, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hef v hv s hs,
      hfe v hv s hs, map_sub, LinearMap.sub_apply, neg_sub]
  have hZ : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 + P 1 1) (Λ v s) = Λ ((E 0 0 + E 1 1) v) s := fun v hv s hs => by
    have h1 : a 0 0 s + a 1 1 s = -h s := by simpa using LinearMap.congr_fun hz s
    have h2 : Λ v (a 0 0 s) + Λ v (a 1 1 s) = Λ ((E 0 0 - E 1 1) v) s := by
      rw [← map_add (f := _), h1, map_neg, hhΛ v hv s hs, neg_neg]
    simp only [LinearMap.add_apply, hPΛ _ _ v hv s hs, if_true, map_add (f := _)]
    simp only [LinearMap.sub_apply, map_sub] at h2
    linear_combination (norm := module) h2
  have hHP : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 - P 1 1) (Λ v s) = Λ v ((a 0 0 - a 1 1) s) := fun v hv s hs => by
    simp only [LinearMap.sub_apply, hPΛ _ _ v hv s hs, if_true, map_sub]
    abel
  have hA : ∀ s ∈ S₀, (a 0 0 - a 1 1) s ∈ S₀ := fun s hs => S₀.sub_mem (haS 0 0 s hs) (haS 1 1 s hs)
  have hBr : (P 0 0 - P 1 1) ((P 0 0 - P 1 1) (Λ v s)) + (2 : ℂ) • (P 0 1 (P 1 0 (Λ v s)) + P 1 0 (P 0 1 (Λ v s)))
      = Λ ((E 0 0 - E 1 1) ((E 0 0 - E 1 1) v) + (2 : ℂ) • (E 0 1 (E 1 0 v) + E 1 0 (E 0 1 v))) s := by
    have p10 : P 1 0 (Λ v s) = Λ v (a 1 0 s) := by simpa using hPΛ 1 0 v hv s hs
    have p01 : P 0 1 (Λ v s) = Λ v (a 0 1 s) := by simpa using hPΛ 0 1 v hv s hs
    have p01' : P 0 1 (Λ v (a 1 0 s)) = Λ v (a 0 1 (a 1 0 s)) := by
      simpa using hPΛ 0 1 v hv _ (haS 1 0 s hs)
    have p10' : P 1 0 (Λ v (a 0 1 s)) = Λ v (a 1 0 (a 0 1 s)) := by
      simpa using hPΛ 1 0 v hv _ (haS 0 1 s hs)
    have hb' : (a 0 0 - a 1 1) ((a 0 0 - a 1 1) s) + (2 : ℂ) • (a 0 1 (a 1 0 s) + a 1 0 (a 0 1 s))
        = h (h s) + (2 : ℂ) • (e (f s) + f (e s)) := by
      have := LinearMap.congr_fun hb s
      simp only [two_mul, LinearMap.add_apply, Module.End.mul_apply] at this
      rw [two_smul, two_smul]
      exact this
    rw [hHP v hv s hs, hHP v hv _ (hA s hs), p10, p01, p01', p10', ← map_add (f := _), ← map_smul, ← map_add (f := _), hb', map_add (f := _), map_smul,
      map_add, hef v hv s hs, hfe v hv s hs, hhΛ v hv _ (hhS s hs), hhΛ _ (hHV v hv) s hs, neg_neg,
      map_add, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.add_apply, add_comm (Λ (E 1 0 _) s)]
  have key : (4 : ℂ) • Formalism.REAL.qdet P u (Λ v s) = (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s := by
    have k2 : (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s = Λ ((4 : ℂ) • Formalism.REAL.qdet E u v) s := by
      rw [map_smul, LinearMap.smul_apply]
    rw [k2, four_qdet P hP u, four_qdet E hE u v, hBr, hZ v hv s hs, hZ _ (hZV v hv) s hs]
    simp only [map_add (f := _), map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  exact smul_right_injective T (by norm_num : (4 : ℂ) ≠ 0) key
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capLam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π → MoveE O W M π →
    ∀ (τ : E →+* ℂ) u, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, cap τ u (Λ f φ) = Λ (TR.cap (pl F τ) u f) φ := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL hE τ u f hf φ hφ
  obtain ⟨hXX, hDD, hDX, he, hfo, hh⟩ := weylX F E D W O τ
  obtain ⟨c1, c2, c3⟩ := capelli (Module.End ℂ (S4 F)) (O.X D τ) (O.DX D τ) (O.dE D τ)
    (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1)
    (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) (O.h (pl F τ))
    hXX hDD hDX (fun _ _ => rfl) rfl rfl hh
  generalize O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1 = q at he c1 c3
  generalize O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1 = Δ at hfo c1 c3
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hk : cc * -cc⁻¹ = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hcc]
  have k' : -cc⁻¹ * cc = -1 := by
    rw [neg_mul, inv_mul_cancel₀ hcc]
  have hef : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) = -(q * Δ) := by
    rw [he, hfo, smul_mul_smul_comm, hk, neg_smul, one_smul]
  have hfe : O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = -(Δ * q) := by
    rw [he, hfo, smul_mul_smul_comm, k', neg_smul, one_smul]
  have hP : Formalism.REAL.GlRel (Eop (a := 2) τ) := by
    intro i j k l
    have h := congrArg (Cm.uC E 2) (Cm.glRel_genC (a := 2) τ i j k l)
    simpa only [map_sub, map_mul, Cm.uC_genC, apply_ite (Cm.uC E 2), map_zero] using h
  have hst : ∀ i j, ∀ v ∈ π.V, TR.Eop (pl F τ) i j v ∈ π.V := fun i j v hv =>
    π.stable (.lie _) v hv
  have hfock := fun s hs => fockOps F E D O s hs
  have hme : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.e D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 0 1 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.e D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 0 1 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.1 _), hΛ _ (hst 0 1 v hv) s hs]
    exact hE v hv s hs _ g
  have hmf : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.f D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 1 0 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.f D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 1 0 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.2.1 _), hΛ _ (hst 1 0 v hv) s hs]
    exact moveF F E D W M π O hE v hv s hs _ g
  have h1 : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) - O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = O.h (pl F τ) := by
    rw [hef, hfe, ← c1]
    abel
  have h3 : (O.dE D τ 0 0 - O.dE D τ 1 1) * (O.dE D τ 0 0 - O.dE D τ 1 1) +
      2 * (O.dE D τ 0 1 * O.dE D τ 1 0 + O.dE D τ 1 0 * O.dE D τ 0 1) =
      O.h (pl F τ) * O.h (pl F τ) + 2 * (O.e D.δ (pl F τ) * O.f D.δ (pl F τ) + O.f D.δ (pl F τ) * O.e D.δ (pl F τ)) := by
    rw [c3, hef, hfe]
    noncomm_ring
  exact capAbs (TR.Sm F 2) (S4 F) (Sm E 2) π.V (Fock D.δ) Λ (TR.Eop (pl F τ)) (Eop τ) (O.dE D τ)
    (O.e D.δ (pl F τ)) (O.f D.δ (pl F τ)) (O.h (pl F τ)) (TR.glRel_Eop _) hP hst
    (fun i j s hs => (hfock s hs).2.2.2.2.2.1 τ i j) (fun s hs => (hfock s hs).2.2.1 _)
    (fun s hs => (hfock s hs).2.2.2.1 _)
    (fun i j v hv s hs => eopLift F E D W M π O Λ hΛ hL τ i j v hv s hs) hme hmf h1 c2 h3
    (u + ((2 : ℕ) - 1) / 2) f hf φ hφ
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), (∀ O, LieLift O W M π) → (∀ O, MoveE O W M π) → St.Cap W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h1 h2 τ m hm u Φ hΦ
  obtain ⟨O⟩ := opsEx F
  obtain ⟨Λ, hΛ⟩ := lamEx F E D W M π
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    obtain rfl : Φ = Λ f φ := Subtype.ext (e.trans (hΛ f hf φ hφ).symm)
    rw [capLam F E D W M π O Λ hΛ (h1 O) (h2 O) τ u f hf φ hφ]
    have := hm.2 u f hf
    rw [show pl F τ = InfinitePlace.mk (τ.comp (algebraMap F E)) from rfl, this, map_smul, LinearMap.smul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]
