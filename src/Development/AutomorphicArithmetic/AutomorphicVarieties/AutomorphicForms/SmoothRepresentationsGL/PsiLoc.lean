module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem psiL_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) : psiL w x = 1 ↔ GroundTheory.Global.localAdelicChar E w x = 1 := by
  have h : psiL w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := rfl
  rw [h]
  exact Circle.coe_eq_one

private theorem exists_psiL_ne_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (z : w.adicCompletion E) (hz : z ∉ GroundTheory.Global.localInvDifferent w) :
    ∃ a ∈ w.adicCompletionIntegers E, psiL w (a * z) ≠ 1 := by
  by_contra hc
  refine hz ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff w z).1 fun a ha => ?_)
  rw [← psiL_eq_one_iff]
  by_contra h
  exact hc ⟨a, ha, h⟩

theorem UpperTheory.V.Af.Smo.psiLoc :
    UpperTheory.V.Af.Smo.PsiLoc := by
  intro E _ _
  refine ⟨fun w => ⟨?_, fun h => ?_⟩, ?_⟩
  · filter_upwards [(GroundTheory.Global.isOpen_localInvDifferent w).mem_nhds (zero_mem _)] with x hx
    exact (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem hx)
  · obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
      (WithZero.exp (FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) + 1))
    obtain ⟨a, -, ha⟩ := exists_psiL_ne_one w z (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp]
      omega)
    exact ha (by rw [h]; rfl)
  · filter_upwards [FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)] with w hw
    refine ⟨fun x hx => (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem
      (GroundTheory.Global.mem_localInvDifferent_of_mem hx)), fun ϖ hϖ => ?_⟩
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨a, haO, ha⟩ := exists_psiL_ne_one w ϖ⁻¹ (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hw, map_inv₀, hv, ← WithZero.exp_neg,
        WithZero.exp_le_exp]
      omega)
    refine ⟨a * ϖ⁻¹, ?_, ha⟩
    rw [mul_left_comm, mul_inv_cancel₀ h0, mul_one]
    exact haO
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic
open scoped ValuativeRel

namespace UpperTheory.V.Af.Smo

def SphDict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
    GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) ∧
    Formalism.UG.IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ∧
    (∀ r ≤ n, Spherical.sqrtQ (w.adicCompletion E) ^ (r * (n - r)) =
      (Formalism.UG.qV E w : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2)) ∧
    ∀ u ∈ Iwasawa.unipotent (w.adicCompletion E) n, IsY 0 u.val ∧
      ∀ ψ : AddChar (w.adicCompletion E) ℂ, Whittaker.psiN ψ u = ψ (supN u.val)

def TjSet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∀ r ≤ n,
    Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (Spherical.minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ)

end UpperTheory.V.Af.Smo
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.eigOfSat :
    UpperTheory.V.Af.Smo.EigOfSat := by
  intro E _ _ _ n π w B hB φ hφ hK g
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, map_mul, ← mul_assoc, hK _ k hk]
  · by_cases h0 : φ = 0
    · subst h0
      simp
    have he := (hB.2 (⟨φ, hφ⟩ : π.V)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => hK x k hk))) fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
    let ev : π.V →+ ℂ :=
      { toFun := fun ψ => ψ.1.1 (g * finGL E n (locGL E n w y))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (π.locRep w) ⟨φ, hφ⟩)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
    rw [map_mul, map_mul, ← mul_assoc]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LevelS
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.levelS :
    UpperTheory.V.Af.Smo.LevelS := by
  intro E _ _ n V
  let e := AdelicGLn.finiteRestrictedEquiv E n
  let f : (∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) →
      GL (Fin n) (Af E) := fun x => e.symm (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hf : Continuous f := e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  let o : ∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E))) :=
    fun v => ⟨1, one_mem _⟩
  have ho : f o = 1 := by
    refine e.symm_apply_eq.2 ?_
    rw [map_one]
    rfl
  have hV : f ⁻¹' (V : Set (GL (Fin n) (Af E))) ∈ 𝓝 o := hf.continuousAt.preimage_mem_nhds (ho ▸ V.mem_nhds_one)
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨S, t, ht, hS⟩ := hV
  refine ⟨S, fun k hk => ?_⟩
  have hek : ∀ v, e k v = cmp v k := fun v => Units.ext (Matrix.ext fun _ _ => rfl)
  have hi : ∀ v : HeightOneSpectrum (𝓞 E), cmp v k ∈ GLnLocal.integralGL (v.adicCompletion E) n := fun v => by
    have h := GlobalTheory.AdelicU.mem_GLint_iff.1 (hk.2 v)
    rw [GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    exact h
  have hx : f (fun v => ⟨cmp v k, hi v⟩) = k := by
    refine e.symm_apply_eq.2 (DFunLike.ext _ _ fun v => ?_)
    exact (hek v).symm
  rw [← hx]
  refine hS fun v hv => ?_
  have : (⟨cmp v k, hi v⟩ : (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) = o v :=
    Subtype.ext (hk.1 v hv)
  exact this ▸ mem_of_mem_nhds (ht v)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_equiv_mod {M : Type} [AddCommGroup M] [Module ℂ M] (U U' D : Submodule ℂ M)
    (h : U ⊓ D = ⊥) (h' : U' ⊓ D = ⊥) (e : U ⊔ D = U' ⊔ D) :
    ∃ T : U ≃ₗ[ℂ] U', ∀ u, (T u).1 - u.1 ∈ D := by
  have inj : ∀ W : Submodule ℂ M, W ⊓ D = ⊥ → Function.Injective (D.mkQ ∘ₗ W.subtype) := fun W hW => by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have hx' : x.1 ∈ W ⊓ D := ⟨x.2, (Submodule.Quotient.mk_eq_zero D).1 hx⟩
    rw [hW] at hx'
    exact Subtype.ext hx'
  have rg : ∀ W : Submodule ℂ M, LinearMap.range (D.mkQ ∘ₗ W.subtype) = (W ⊔ D).map D.mkQ := fun W => by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have er : LinearMap.range (D.mkQ ∘ₗ U.subtype) = LinearMap.range (D.mkQ ∘ₗ U'.subtype) := by
    rw [rg, rg, e]
  refine ⟨(LinearEquiv.ofInjective _ (inj U h)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (inj U' h')).symm), fun u => ?_⟩
  refine (Submodule.Quotient.eq D).1 ?_
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (inj U' h')).apply_symm_apply
    (LinearEquiv.ofEq _ _ er (LinearEquiv.ofInjective _ (inj U h) u)))

private theorem iso_of_compl {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π π' : CuspSub E n)
    (D : Submodule ℂ (TR.Sm E n)) (hD : TR.IsStable D) (h : π.V ⊓ D = ⊥) (h' : π'.V ⊓ D = ⊥)
    (hle : π'.V ≤ π.V ⊔ D) : π.Iso π' := by
  have hst : TR.IsStable (π.V ⊓ (π'.V ⊔ D)) := by
    rintro o φ ⟨h1, h2⟩
    refine ⟨π.stable o φ h1, ?_⟩
    obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.1 h2
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (π'.stable o x hx) (hD o d hd)
  have hge : π.V ≤ π'.V ⊔ D := by
    rcases π.irred _ inf_le_left hst with h0 | h0
    · refine absurd (eq_bot_iff.2 fun x hx => ?_) π'.ne_bot
      obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hle hx)
      have hu' : u ∈ π.V ⊓ (π'.V ⊔ D) := ⟨hu, by
        have := Submodule.add_mem_sup hx (D.neg_mem hd)
        rwa [add_neg_cancel_right] at this⟩
      rw [h0, Submodule.mem_bot] at hu'
      rw [← h']
      refine ⟨hx, ?_⟩
      rw [hu', zero_add]
      exact hd
    · exact inf_eq_left.1 h0
  obtain ⟨T, hT⟩ := exists_equiv_mod π.V π'.V D h h'
    (le_antisymm (sup_le hge le_sup_right) (sup_le hle le_sup_right))
  refine ⟨T, fun o φ => Subtype.ext (sub_eq_zero.1 ?_)⟩
  rw [← Submodule.mem_bot ℂ, ← h']
  refine ⟨π'.V.sub_mem (T _).2 (π'.op o _).2, ?_⟩
  have h1 := D.sub_mem (hT (π.op o φ)) (hD o _ (hT φ))
  rw [map_sub, TR.CuspSub.op_val, sub_sub_sub_cancel_right] at h1
  exact h1

private theorem stab_orthRel {E : Type} [Field E] [NumberField E] {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : cuspForms E n →ₗ[ℂ] H)
    (hρ : ∀ X, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp E n).ρ X c)) = 0)
    (hσ : ∀ k, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι ((gkModuleCusp E n).σ k a)) (ι ((gkModuleCusp E n).σ k c)) = inner ℂ (ι a) (ι c))
    (hτ : ∀ g, ∀ a ∈ centralCuspForms E n, ∀ c ∈ centralCuspForms E n,
      inner ℂ (ι (finRepCusp E n g a)) (ι (finRepCusp E n g c)) = inner ℂ (ι a) (ι c))
    {U : Submodule ℂ (cuspForms E n)} (hU : U ≤ centralCuspForms E n) (hs : Fb.Stab U) :
    Fb.Stab (orthRel ι (centralCuspForms E n) U) := by
  refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
  · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
      (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
    rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
    exact hρ X x (hU hx) y hy
  · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
      (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
    rw [← hσ k _ (hU (hs.σ k⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
      (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
    rw [← hτ g _ (hU (hs.τ g⁻¹ x hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]

private theorem carrier_le_of_not_iso {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ}
    (π π' : CuspSub E n) (hi : ¬ π.Iso π') (C : Submodule ℂ (cuspForms E n)) (hC : Fb.Stab C)
    (hinf : Fb.carrier π ⊓ C = ⊥) (hle : Fb.carrier π' ≤ Fb.carrier π ⊔ C) : Fb.carrier π' ≤ C := by
  have hst : TR.IsStable (π'.V ⊓ C.map (Fb.ofCusp E n)) := fun o x hx =>
    ⟨π'.stable o x hx.1, hC.map o x hx.2⟩
  rcases π'.irred _ inf_le_left hst with h0 | h0
  · refine absurd (iso_of_compl π π' _ hC.map ?_ h0 ?_) hi
    · rw [← Fb.map_carrier, ← Submodule.map_inf _ Fb.ofCusp_injective, hinf, Submodule.map_bot]
    · rw [← Fb.map_carrier, ← Fb.map_carrier, ← Submodule.map_sup]
      exact Submodule.map_mono hle
  · intro φ' hφ'
    obtain ⟨ψ, hψ, e⟩ := inf_eq_left.1 h0 (Fb.mem_carrier.1 hφ')
    obtain rfl := Fb.ofCusp_injective e
    exact hψ

theorem UpperTheory.V.Af.Smo.innerZero :
    UpperTheory.V.Af.Smo.InnerZero := by
  intro E _ _ _ n μ _ π π' hc hc' hi φ hφ φ' hφ'
  have l := Fb.carrier_le_central π hc
  have l' := Fb.carrier_le_central π' hc'
  have hs := Fb.stab_carrier π
  have hC := stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l hs
  have hsup := CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l hs.ρ hs.τ
  have hinf := inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l fun a ha h0 =>
    CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0
  exact (carrier_le_of_not_iso π π' hi _ hC hinf (l'.trans hsup.ge) hφ').2 φ hφ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthTr
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open CuspidalSpectrum RightCosetSpace in
private theorem UpperTheory.V.Af.Smo.coeFn_tr {E : Type} [Field E] [NumberField E] {n : ℕ}
    (μ : Measure (Reduction.normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] {φ : cuspForms E n} (hφ : φ ∈ centralCuspForms E n)
    (g : AdelicGLn.AdelicGL E n) :
    (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)) : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ] quotTr φ g := by
  rw [toLp_cuspRepT, rightRegularRep_apply, toLp_cuspVecL, quotTr_eq_comp hφ, quotTr_one]
  refine (coeFn_rightTranslate _ μ _ _).trans ?_
  exact (measurePreserving_rightMul μ (toOne g)).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)

private theorem UpperTheory.V.Af.Smo.inner_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {S T : Submodule ℂ H} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0) {x y : H}
    (hx : x ∈ S.topologicalClosure) (hy : y ∈ T.topologicalClosure) : inner ℂ x y = 0 := by
  have h1 : T ≤ S.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact fun b hb => (Submodule.mem_orthogonal _ _).2 fun a ha => h a ha b hb
  exact (Submodule.mem_orthogonal _ _).1
    (Submodule.topologicalClosure_minimal T h1 (Submodule.isClosed_orthogonal _) hy) x hx

open CuspidalSpectrum RightCosetSpace in
theorem UpperTheory.V.Af.Smo.orthTr :
    UpperTheory.V.Af.Smo.OrthTr := by
  intro E _ _ n μ _ U U' hU hU' sU sU' h φ hφ φ' hφ' g g'
  have i1 := isInvariant_topologicalClosure_map μ hU sU.ρ sU.σ sU.τ
  have i2 := isInvariant_topologicalClosure_map μ hU' sU'.ρ sU'.σ sU'.τ
  have m1 := i1 (toOne g) _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ))
  have m2 := i2 (toOne g') _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ'))
  have h0 := UpperTheory.V.Af.Smo.inner_closure (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact h a ha b hb) m1 m2
  have h1 : inner ℂ (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)))
      (toLp μ (cuspRepT μ (toOne g') (cuspVecL μ φ'))) = 0 := h0
  rw [MeasureTheory.L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [UpperTheory.V.Af.Smo.coeFn_tr μ (hU hφ) g, UpperTheory.V.Af.Smo.coeFn_tr μ (hU' hφ') g'] with q e1 e2
  rw [e1, e2, RCLike.inner_apply']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AvgChar
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.avgChar :
    UpperTheory.V.Af.Smo.AvgChar := by
  intro A _ L₀ L _ hidx
  classical
  let H : AddSubgroup L := L₀.addSubgroupOf L
  haveI : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero hidx
  let r : L ⧸ H → A := fun q => ((Quotient.out q : L) : A)
  have hr : Function.Injective r := Subtype.coe_injective.comp Quotient.out_injective
  refine ⟨Finset.univ.image r, Finset.univ_nonempty.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro χ hχ ⟨x, hxL, hx⟩
    have hχeq : ∀ a b : L, (a : L ⧸ H) = b → χ a = χ b := by
      intro a b hab
      have hm : -a + b ∈ H := QuotientAddGroup.eq.mp hab
      have hm' : ((-a + b : L) : A) ∈ L₀ := AddSubgroup.mem_addSubgroupOf.mp hm
      have h1 : χ ((-a + b : L) : A) = 1 := hχ _ hm'
      have h2 : (b : A) = a + ((-a + b : L) : A) := by simp
      rw [h2, AddChar.map_add_eq_mul, h1, mul_one]
    rw [Finset.sum_image (fun q _ q' _ h => hr h)]
    let xL : L := ⟨x, hxL⟩
    have hshift : ∀ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) = χ (r q) * χ x := by
      intro q
      have h3 : ((Quotient.out (q + (xL : L ⧸ H)) : L) : L ⧸ H) = ((Quotient.out q + xL : L) : L ⧸ H) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have h4 := hχeq _ _ h3
      simp only [r]
      rw [h4, AddSubgroup.coe_add, AddChar.map_add_eq_mul]
    have hS : ∑ q : L ⧸ H, χ (r q) = (∑ q : L ⧸ H, χ (r q)) * χ x := by
      calc ∑ q : L ⧸ H, χ (r q) = ∑ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) :=
            (Equiv.sum_comp (Equiv.addRight (xL : L ⧸ H)) (fun q => χ (r q))).symm
        _ = ∑ q : L ⧸ H, χ (r q) * χ x := Finset.sum_congr rfl (fun q _ => hshift q)
        _ = (∑ q : L ⧸ H, χ (r q)) * χ x := (Finset.sum_mul _ _ _).symm
    have h5 : (∑ q : L ⧸ H, χ (r q)) * (χ x - 1) = 0 := by
      rw [mul_sub, mul_one, ← hS, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h6
    · exact absurd (sub_eq_zero.mp h6) hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AwayInd
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem fin_bad {E : Type} [Field E] [NumberField E] {n : ℕ} (k : GL (Fin n) (Af E)) :
    {w | cmp w k ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite := by
  have h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w := fun x => x.2
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w a b
    rw [GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]
    exact ⟨a, b⟩
  exact h3

theorem UpperTheory.V.Af.Smo.awayInd :
    UpperTheory.V.Af.Smo.AwayInd := by
  intro E _ _ n S P h0 h1
  classical
  suffices H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n)) → P k by
    intro k hk
    refine H (fin_bad k).toFinset k hk fun w hw => ?_
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩
  | insert w T hw ih =>
    intro k hk h
    by_cases hS : w ∈ S
    · refine ih k hk fun v hv => ?_
      by_cases e : v = w
      · subst e; rw [hk v hS]; exact one_mem _
      · exact h v (by simp [e, hv])
    · have e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1 := by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]
      have e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k := fun v e => by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]
      have a : Away S (k * (locGL E n w (cmp w k))⁻¹) := fun v hv => by
        rw [e2 v (fun e => hS (e ▸ hv)), hk v hv]
      have p := ih _ a fun v hv => by
        by_cases e : v = w
        · subst e; rw [e1]; exact one_mem _
        · rw [e2 v e]; exact h v (by simp [e, hv])
      have q := h1 w hS _ a e1 p (cmp w k)
      rwa [inv_mul_cancel_right] at q
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.WhBasic
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open GroundTheory.Automorphic.FourierWhittaker in
private theorem exists_uGL {E : Type} [Field E] [NumberField E] {n : ℕ} (ν : GA E n) (hν : IsY 0 ν.val) :
    ∃ X : Pos n → Ad E, ν = uGL X ∧ supN ν.val = supSum 0 X := by
  classical
  refine ⟨fun p => ν.val p.1.1 p.1.2, Units.ext (Matrix.ext fun a b => ?_), ?_⟩
  · rw [coe_uGL, uMat_apply]
    split_ifs with h1 h2
    · subst h1; exact (hν a (Nat.zero_le _)).1
    · rfl
    · exact (hν a (Nat.zero_le _)).2 b (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1))
  · unfold supN supSum
    rw [← Finset.sum_product', ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
      omega
    · intro p _ q _ h
      exact Subtype.ext h
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hq
      refine ⟨⟨q, by rw [Fin.lt_def]; omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro p _
      rfl

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.whBasic :
    UpperTheory.V.Af.Smo.WhBasic := by
  intro E _ _ n f hf
  refine ⟨?_, ?_, ?_⟩
  · have : whittaker f = partialCoeff f 0 := funext fun g => whittaker_eq_partialCoeff_zero hf.cont g
    rw [this]
    exact continuous_partialCoeff hf.cont 0
  · obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨C, fun g => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos n)) (s := vecDomain E (Pos n))
      (f := fun X => f (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (C := C)
      (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) fun X _ => by
        rw [norm_mul, Circle.norm_coe, mul_one]
        exact hC _
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one] at h
  · intro ν hν g
    obtain ⟨X, h1, h2⟩ := exists_uGL ν hν
    rw [h2, h1]
    exact GroundTheory.Automorphic.MultiplicityOne.whittaker_uGL_mul hf.cont hf.left X g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaSch
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.betaSch :
    UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch := by
  intro hP V M _ _ _ _ _ _ _ _ B hB K
  set Φ : V × M → V × M := fun z => (z.1, z.2 - B z.1 z.2) with hΦdef
  have hΦ : Function.HasTemperateGrowth Φ := by
    let B2 : V →L[ℝ] M →L[ℝ] V × M :=
      (ContinuousLinearMap.compL ℝ M M (V × M) (ContinuousLinearMap.inr ℝ V M)).comp B
    have h1 : Function.HasTemperateGrowth (fun z : V × M => B2 z.1 z.2) :=
      B2.bilinear_hasTemperateGrowth (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
        (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
    have h2 := (ContinuousLinearMap.id ℝ (V × M)).hasTemperateGrowth.add h1.neg
    convert h2 using 1
    funext z
    ext <;> simp [Φ, B2, sub_eq_add_neg]
  have hbd : ∃ (k : ℕ) (C : ℝ), ∀ z : V × M, ‖z‖ ≤ C * (1 + ‖Φ z‖) ^ k := by
    refine ⟨2, 1 + ‖B‖, fun z => ?_⟩
    obtain ⟨u, x⟩ := z
    set t := ‖Φ (u, x)‖ with ht
    have hu : ‖u‖ ≤ t := norm_fst_le (Φ (u, x))
    have hy : ‖x - B u x‖ ≤ t := norm_snd_le (Φ (u, x))
    have hx : x = (x - B u x) + B u (x - B u x) := by
      rw [map_sub, hB, sub_zero, sub_add_cancel]
    have hBu : ‖B u (x - B u x)‖ ≤ ‖B‖ * ‖u‖ * ‖x - B u x‖ := B.le_opNorm₂ _ _
    have hxle : ‖x‖ ≤ t + ‖B‖ * t * t := by
      calc ‖x‖ = ‖(x - B u x) + B u (x - B u x)‖ := by rw [← hx]
        _ ≤ ‖x - B u x‖ + ‖B u (x - B u x)‖ := norm_add_le _ _
        _ ≤ t + ‖B‖ * t * t := by
          have := norm_nonneg B
          have := norm_nonneg u
          have := norm_nonneg (x - B u x)
          nlinarith [mul_le_mul hu hy (norm_nonneg _) (le_trans (norm_nonneg _) hu)]
    have ht0 : 0 ≤ t := norm_nonneg _
    have hB0 := norm_nonneg B
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  let K' : 𝓢(V × M, ℂ) := SchwartzMap.compCLM ℂ hΦ hbd K
  obtain ⟨L, hL⟩ := hP V M K'
  have hι : Function.HasTemperateGrowth (fun x : M => ((0 : V), x)) := by
    convert (ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth using 1
    funext x
    rfl
  have hιb : ∃ (k : ℕ) (C : ℝ), ∀ x : M, ‖x‖ ≤ C * (1 + ‖((0 : V), x)‖) ^ k := by
    refine ⟨1, 1, fun x => ?_⟩
    have h := norm_snd_le ((0 : V), x)
    simp only [pow_one, one_mul]
    linarith
  refine ⟨K', SchwartzMap.compCLM ℂ hι hιb L, fun u x => rfl, fun x => ?_⟩
  change L ((0 : V), x) = _
  rw [hL]
  simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigMap
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}

private theorem sum_Tj {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n)),
      ∀ F : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_zero (h : B.card = n) : Eig w B (fun _ : GL (Fin n) (w.adicCompletion E) => (0 : ℂ)) :=
  ⟨h, fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

private theorem eig_sub {W W' : GL (Fin n) (w.adicCompletion E) → ℂ} (h : Eig w B W) (h' : Eig w B W') :
    Eig w B (fun y => W y - W' y) := by
  refine ⟨h.card, fun g k hk => by simp only [h.inv g k hk, h'.inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  have e := h.eig ϖ hϖ j hj g
  have e' := h'.eig ϖ hϖ j hj g
  rw [hs] at e e' ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, e, e']

private theorem eig_int {X : Type} [MeasurableSpace X] (μ : Measure X) (hB : B.card = n)
    (F : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ) (h : ∀ x, Eig w B (F x))
    (hi : ∀ y, Integrable (fun x => F x y * a x) μ) : Eig w B (fun y => ∫ x, F x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.eigMap :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.EigMap := by
  intro hC E _ _ _ n w B f hf
  refine ⟨fun hN g => ?_, fun hN α g => ?_, fun f' hf' g => eig_sub (hf g) (hf' g)⟩
  · refine eig_int ((vecMeasure E (Pos n)).restrict (vecDomain E (Pos n))) (hf 1).card
      (fun X y => f (uGL X * (g * finGL E n (locGL E n w y))))
      (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (fun X => ?_) fun y => ?_
    · simpa only [mul_assoc] using hf (uGL X * g)
    · have hc : Continuous fun X : Pos n → Ad E => f (uGL X * (g * finGL E n (locGL E n w y))) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
        (hN.cont.comp (continuous_uGL.mul continuous_const)).mul
          (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg))
      exact (hc.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  · refine eig_int volume (hf 1).card (fun x y => chart f (g * finGL E n (locGL E n w y)) x) α (fun x => ?_) fun y => ?_
    · by_cases hx : IsUnit (Matrix.of x)
      · have := hf (g * infGL E n hx.unit)
        simpa only [chart, dif_pos hx, mul_assoc, TR.infGL_comm] using this
      · simpa only [chart, dif_neg hx] using eig_zero (w := w) (hf 1).card
    · obtain ⟨C, hC'⟩ := hN.bdd
      haveI : BorelSpace (Lie E n) := inferInstance
      haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
      haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      refine α.integrable.bdd_mul (c := C) ((hC E n f hN.cont).2 _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      unfold chart
      split_ifs
      · exact hC' _
      · simpa using (norm_nonneg _).trans (hC' 1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaInt
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem slice_int {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup M] [NormedSpace ℝ M] (G : 𝓢(V × M, ℂ)) (y : M) :
    Integrable (fun ξ : V => G (ξ, y)) := by
  have h1 : Function.HasTemperateGrowth (fun ξ : V => (ξ, y)) := by
    have := (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : V), y))
    convert this using 1
    ext ξ <;> simp
  have h2 : AntilipschitzWith 1 (fun ξ : V => (ξ, y)) := (Isometry.antilipschitz (by
    refine Isometry.of_dist_eq fun a b => ?_
    simp [Prod.dist_eq]))
  exact (SchwartzMap.compCLMOfAntilipschitz ℝ h1 h2 G).integrable

private theorem shear_int {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [μ.IsAddHaarMeasure] (N : M →L[ℝ] M)
    (hN : ∀ x, N (N x) = 0) (f : M → ℂ) : ∫ x, f (x + N x) ∂μ = ∫ x, f x ∂μ := by
  let L : M →ₗ[ℝ] M := 1 + (N : M →ₗ[ℝ] M)
  have hnil : IsNilpotent (-(N : M →ₗ[ℝ] M) : Module.End ℝ M) := ⟨2, by
    ext x
    simp [pow_two, hN]⟩
  have hdet : LinearMap.det L = 1 := by
    have := LinearMap.eval_charpoly (-(N : M →ₗ[ℝ] M)) 1
    rw [(LinearMap.isNilpotent_iff_charpoly _).1 hnil] at this
    simpa [L] using this.symm
  have hmap : Measure.map L μ = μ := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let e : M ≃ₜ M :=
    { toFun := fun x => x + N x
      invFun := fun x => x - N x
      left_inv := fun x => by simp [hN]
      right_inv := fun x => by simp [hN]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hp : MeasurePreserving e.toMeasurableEquiv μ μ := ⟨e.toMeasurableEquiv.measurable, hmap⟩
  exact hp.integral_comp' f

theorem UpperTheory.V.Af.Smo.betaInt :
    UpperTheory.V.Af.Smo.BetaInt := by
  intro V M _ _ _ _ _ _ _ _ _ _ μ _ B hB G K K' hK hK' w η hw ⟨C, hC⟩ hwB
  have hint : ∀ (F : 𝓢(V × M, ℂ)) (a : V × M → ℂ), Measurable a → (∀ z, ‖a z‖ ≤ C) →
      ∫ u, ∫ x, a (u, x) * F (u, x) ∂μ = ∫ x, (∫ u, a (u, x) * F (u, x)) ∂μ := by
    intro F a ha haC
    refine integral_integral_swap (f := fun u x => a (u, x) * F (u, x)) ?_
    have : Integrable F ((volume : Measure V).prod μ) := F.integrable
    exact this.bdd_mul ha.aestronglyMeasurable (Filter.Eventually.of_forall haC)
  have h1 := hint K' (fun z => w z.2) (hw.comp measurable_snd) (fun z => hC _)
  have h2 := hint K (fun z => (𝐞 ⟪η, z.1⟫ : ℂ) * w z.2)
    (Measurable.mul (Continuous.measurable (by fun_prop)) (hw.comp measurable_snd)) (fun z => by rw [norm_mul, Circle.norm_coe, one_mul]; exact hC _)
  simp only [integral_const_mul] at h1
  rw [← h1]
  have h3 : ∀ u, ∫ x, w x * K' (u, x) ∂μ = ∫ x, (𝐞 ⟪η, u⟫ : ℂ) * w x * K (u, x) ∂μ := by
    intro u
    rw [← shear_int μ (B u) (hB u)]
    congr 1
    ext x
    rw [hwB, hK']
    simp [hB]
  simp only [h3]
  rw [h2]
  congr 1
  ext x
  have hF : 𝓕 (fun ξ => G (ξ, x)) = fun u => K (u, x) := by
    ext u
    rw [hK]; rfl
  have h4 := Continuous.fourierInv_fourier_eq (f := fun ξ => G (ξ, x)) (by fun_prop) (slice_int G x)
    (by rw [hF]; exact slice_int K x)
  have h5 := congrFun h4 η
  rw [hF, Real.fourierInv_eq] at h5
  rw [← h5, ← integral_const_mul]
  congr 1
  ext u
  rw [Circle.smul_def, smul_eq_mul, real_inner_comm]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentLoc
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem scalar_comm' {K : Type} [Field K] {n : ℕ} (y : Kˣ) (g : GL (Fin n) K) :
    GeneralLinearGroup.scalar (Fin n) y * g = g * GeneralLinearGroup.scalar (Fin n) y :=
  Units.ext (Matrix.scalar_commute (y : K) (fun _ => Commute.all _ _) g.val).eq

private theorem finsum_top {K : Type} [Field K] {n : ℕ} (O : Subring K) (ϖ : Kˣ) (W : GL (Fin n) K → ℂ)
    (hW : ∀ g, ∀ k ∈ Formalism.UG.GLint (Fin n) O, W (g * k) = W g) (g : GL (Fin n) K) :
    ∑ᶠ c : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O, Formalism.UG.Tj ℂ n O (ϖ : K) n c.out * W (g * c.out) =
      W (g * GeneralLinearGroup.scalar (Fin n) ϖ) := by
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ϖ with hz
  have hd : Formalism.UG.diagJ n (ϖ : K) n = z.val := by
    simp [Formalism.UG.diagJ, hz]
  rw [finsum_eq_single _ (z : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Formalism.UG.GLint (Fin n) O) z
    rw [hk, ← mul_assoc, hW _ _ k.2, Formalism.UG.Tj, Set.indicator_of_mem, Pi.one_apply, one_mul]
    exact ⟨1, one_mem _, k, k.2, by simp [hd]⟩
  · intro c hc
    rw [Formalism.UG.Tj, Set.indicator_of_notMem, zero_mul]
    rintro ⟨a, ha, b, hb, e⟩
    refine hc ?_
    have e' : c.out = z * (a * b) := by
      rw [← mul_assoc, hz, scalar_comm', ← hz]
      exact Units.ext (by rw [e, hd]; rfl)
    rw [← QuotientGroup.out_eq' c, e']
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem ha hb)

private theorem scalar_mem {K : Type} [Field K] {n : ℕ} (O : Subring K) (u : Kˣ) (h : (u : K) ∈ O)
    (h' : ((u⁻¹ : Kˣ) : K) ∈ O) : GeneralLinearGroup.scalar (Fin n) u ∈ Formalism.UG.GLint (Fin n) O := by
  have key : ∀ x : Kˣ, (x : K) ∈ O → ∀ i j, (GeneralLinearGroup.scalar (Fin n) x).val i j ∈ O := fun x hx i j => by
    change Matrix.diagonal (fun _ => (x : K)) i j ∈ O
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hx
    · exact zero_mem _
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨key u h, ?_⟩
  rw [← map_inv]
  exact key _ h'

theorem UpperTheory.V.Af.Smo.centLoc :
    UpperTheory.V.Af.Smo.CentLoc := by
  intro E _ _ n w B y
  by_cases hB : B.card = n
  swap
  · exact ⟨0, fun W hW => absurd hW.card hB⟩
  let H : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {y | ∃ c : ℂ, c ≠ 0 ∧ ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, Eig w B W →
        ∀ g, W (g * GeneralLinearGroup.scalar (Fin n) y) = c * W g}
      one_mem' := ⟨1, one_ne_zero, fun W _ g => by simp⟩
      mul_mem' := by
        rintro a b ⟨c, hc, h⟩ ⟨d, hd, h'⟩
        exact ⟨d * c, mul_ne_zero hd hc, fun W hW g => by rw [map_mul, ← mul_assoc, h' W hW, h W hW, mul_assoc]⟩
      inv_mem' := by
        rintro a ⟨c, hc, h⟩
        refine ⟨c⁻¹, inv_ne_zero hc, fun W hW g => ?_⟩
        have := h W hW (g * GeneralLinearGroup.scalar (Fin n) a⁻¹)
        rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
        rw [this, inv_mul_cancel_left₀ hc] }
  suffices hy : y ∈ H from hy.imp fun _ h => h.2
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV E w p := w.valuedAdicCompletion_surjective E _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hne : GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B n ≠ 0 := by
    have hq := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
    rw [Multiset.card_map, hB] at hq
    simp [GlobalTheory.LFun.satEig, Multiset.esymm, hq]
  have hpH : Units.mk0 p hp0 ∈ H := ⟨_, hne, fun W hW g =>
    (finsum_top (Formalism.UG.Ov E w) (Units.mk0 p hp0) W hW.inv g).symm.trans (hW.eig p hp n le_rfl g)⟩
  have hu : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 → u ∈ H := fun u h =>
    ⟨1, one_ne_zero, fun W hW g => by
      rw [one_mul]
      refine hW.inv g _ (scalar_mem (Formalism.UG.Ov E w) u h.le ?_)
      change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]⟩
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := by simp
  have := hu (y * Units.mk0 p hp0 ^ WithZero.log (Valued.v (y : w.adicCompletion E))) (by
    have hp' : Valued.v p = WithZero.exp (-1 : ℤ) := hp
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hp', ← WithZero.exp_zsmul]
    simp only [zsmul_neg, zsmul_one, Int.cast_id]
    rw [WithZero.exp_neg, WithZero.exp_log hy0, mul_inv_cancel₀ hy0])
  exact (H.mul_mem_cancel_right (H.zpow_mem hpH _)).1 this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CornerIsY
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem corner_isY {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (m : ℕ) (s : R →ₙ+* S) (y : GL (Fin n) R)
    (h : IsY m y.val) :
    IsY m (GlobalTheory.CuspRep.cornerGL n s y).val ∧ supN (GlobalTheory.CuspRep.cornerGL n s y).val = s (supN y.val) := by
  have e : ∀ i j, (GlobalTheory.CuspRep.cornerGL n s y).val i j =
      (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s (y.val i j) := fun _ _ => rfl
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [e, (h i hi).1]; simp
  · rw [e, (h i hi).2 j hj, Matrix.one_apply_ne hj.ne', Matrix.one_apply_ne hj.ne']; simp
  · unfold supN
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := fun h' => by subst h'; omega
      rw [e, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne]; simp
    · simp

theorem UpperTheory.V.Af.Smo.embY :
    UpperTheory.V.Af.Smo.EmbY := by
  intro E _ _ _ n m
  exact ⟨fun w y h => corner_isY m (sLoc E w) y h, fun y h => corner_isY m (sFin E) y h,
    fun y h => corner_isY m (sInf E) y h, fun w => GlobalTheory.CuspRep.CuspSub.continuous_locGL w⟩
end
