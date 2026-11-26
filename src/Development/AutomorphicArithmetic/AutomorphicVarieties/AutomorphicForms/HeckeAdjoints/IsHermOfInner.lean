module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
noncomputable section

open NumberField MeasureTheory UpperTheory.V.TR GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.Gk

def ToFound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : Sm F a), TR.IsCuspForm φ → φ.1 ∈ cuspForms F a

def LieMatch : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ),
    ∃ e : TR.Lie F a →ₗ[ℝ] (isExpLieAlgebra F a).lieSubalgebra, centralZ F a = centralExp F a • e (oneL F a) ∧
      ∀ X (φ : Sm F a) (h : φ.1 ∈ cuspForms F a), (lieActionCusp F a (e X) ⟨φ.1, h⟩).1 = (TR.lie F a X φ).1

private theorem isHerm_of_inner {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π : CuspSub F a} {L : Type}
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] (p : π.V →ₗ[ℂ] L) (h1 : ∀ φ, inner ℂ (p φ) (p φ) = 0 → φ = 0)
    (h2 : ∀ k φ ψ, inner ℂ (p (π.op (.fin k) φ)) (p (π.op (.fin k) ψ)) = inner ℂ (p φ) (p ψ))
    (h3 : ∀ k φ ψ, inner ℂ (p (π.op (.cpt k) φ)) (p (π.op (.cpt k) ψ)) = inner ℂ (p φ) (p ψ))
    (h4 : ∀ X φ ψ, inner ℂ (p (π.op (.lie X) φ)) (p ψ) + inner ℂ (p φ) (p (π.op (.lie X) ψ)) = 0) : ∃ H, IsHerm π H :=
  ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => inner ℂ (p φ) (p ψ))
    (fun _ _ _ => by rw [map_add (f := _), inner_add_left]) (fun _ _ _ => by rw [map_smul, inner_smul_left]; rfl)
    (fun _ _ _ => by rw [map_add (f := _), inner_add_right]) (fun _ _ _ => by rw [map_smul, inner_smul_right]; rfl), h1, h2, h3, h4⟩

theorem hermEx_of (h1 : ToFound) (h2 : LieMatch) : HermEx := by
  intro F _ _ _ a _ π h0
  obtain ⟨e, hz, he⟩ := h2 F a
  let μ : Measure (Reduction.normOneGL (K := F) (n := a)) := Measure.haar
  let j : π.V →ₗ[ℂ] cuspForms F a :=
    ((Sm F a).subtype ∘ₗ π.V.subtype).codRestrict _ fun φ => h1 F a φ.1 (π.cusp _ φ.2)
  have hl : ∀ X φ, (gkModuleCusp F a).ρ (e X) (j φ) = j (π.op (.lie X) φ) := fun X φ => Subtype.ext (he X φ.1 _)
  have hc : ∀ φ, j φ ∈ centralCuspForms F a := fun φ => mem_centralCuspForms.mpr fun s x => by
    have h3 : lieActionCusp F a (e (oneL F a)) (j φ) = 0 :=
      Subtype.ext ((he _ φ.1 _).trans (congrArg Subtype.val (h0 _ φ.2)))
    have h4 : lieActionCusp F a (centralZ F a) (j φ) = (0 : ℂ) • j φ := by
      rw [hz, map_smul, LinearMap.smul_apply, h3, smul_zero, zero_smul]
    rw [Reduction.centralSection_mul_comm, apply_mul_centralSection h4]
    simp
  let p := CuspidalSpectrum.cuspToL2 μ ∘ₗ j
  have hr : ∀ (g : GlobalTheory.CuspRep.GA F a) (φ φ' ψ ψ' : π.V), φ'.1 = rt F a g φ.1 → ψ'.1 = rt F a g ψ.1 →
      inner ℂ (p φ') (p ψ') = inner ℂ (p φ) (p ψ) := fun g φ φ' ψ ψ' e1 e2 =>
    (congrArg₂ (inner ℂ) (cuspFormLp_rightTranslate_eq_rep μ (hc φ) g (ψ := j φ') (congrArg Subtype.val e1))
      (cuspFormLp_rightTranslate_eq_rep μ (hc ψ) g (ψ := j ψ') (congrArg Subtype.val e2))).trans
      (UnitaryRep.inner_map_map (CuspidalSpectrum.cuspRep μ) _ _ _)
  refine isHerm_of_inner p (fun φ h => ?_) (fun k φ ψ => hr _ _ _ _ _ rfl rfl) (fun k φ ψ => hr _ _ _ _ _ rfl rfl)
    fun X φ ψ => ?_
  · have h5 : (j φ).1 = (0 : cuspForms F a).1 := congrArg Subtype.val (eq_zero_of_petersson_inner_self_eq_zero μ (hc φ) h)
    exact Subtype.ext (Subtype.ext h5)
  · have e1 : p (π.op (.lie X) φ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j φ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X φ).symm
    have e2 : p (π.op (.lie X) ψ) = CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp F a).ρ (e X) (j ψ)) :=
      congrArg (CuspidalSpectrum.cuspToL2 μ) (hl X ψ).symm
    exact (congrArg₂ (· + ·) (congrArg (inner ℂ · (p ψ)) e1) (congrArg (inner ℂ (p φ)) e2)).trans
      (petersson_inner_lieAlgebra_skewAdjoint μ (e X) (hc φ) (hc ψ))

end UpperTheory.V.Af.Gk
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HeckeAdj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.heckeAdj :
    UpperTheory.V.Af.Gk.HeckeAdj := by
  intro F _ _ a w V _ _ ρ H hH x hx ϖ hϖ j
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w (n := a) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hf := fun (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V) => GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 := (H.flip x).toAddMonoidHom.map_finsum (hf ρ)
  have e2 := (H x).toAddMonoidHom.map_finsum (hf (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))))
  refine e1.trans ((finsum_congr fun c => ?_).trans e2.symm)
  generalize c.out = g
  change H (_ • ρ g x) x = H x (_ • ρ (GlobalTheory.CuspRep.invT a _ g) x)
  unfold Formalism.UG.Tj
  by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
      ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
  · rw [Set.indicator_of_mem hg, Pi.one_apply, one_smul, one_smul]
    obtain ⟨k, hk, b, hb, e⟩ := hg
    obtain ⟨d, rfl⟩ : ∃ d, g = k * d * b := ⟨k⁻¹ * g * b⁻¹, by group⟩
    have hd : d.val = Formalism.UG.diagJ a ϖ j := by
      rw [Units.val_mul, Units.val_mul] at e
      exact (Units.mul_right_inj k).1 ((Units.mul_left_inj b).1 e)
    have hd' : GlobalTheory.CuspRep.invT a _ d = d⁻¹ := by
      rw [← inv_eq_iff_eq_inv]
      apply Units.ext
      rw [InvT.invT_inv_val, hd, Formalism.UG.diagJ, Matrix.diagonal_transpose]
    simp only [map_mul, Module.End.mul_apply, hd']
    rw [hfix b hb, hfix _ (hK b hb)]
    have h1 : H (ρ k (ρ d x)) x = H (ρ d x) x := by
      rw [← hH k (ρ d x) x, hfix k hk]
    have h2 : H x (ρ (GlobalTheory.CuspRep.invT a _ k) (ρ d⁻¹ x)) = H x (ρ d⁻¹ x) := by
      rw [← hH (GlobalTheory.CuspRep.invT a _ k) x (ρ d⁻¹ x), hfix _ (hK k hk)]
    rw [h1, h2, ← hH d x (ρ d⁻¹ x), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rw [Set.indicator_of_notMem hg]
    simp
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.satConj :
    UpperTheory.V.Af.Gk.SatConj := by
  intro F _ _ a w V W _ _ _ _ ρ ρ' H C hdef hH hC B hB
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w (n := a) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hB' : GlobalTheory.LFun.HasSatGL w (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))) (B.map (·⁻¹)) :=
    InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun _ _ => rfl) hB
  have key : ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := a)), x ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ρ' (C x) (B.map (·⁻¹)) := by
    intro x hx h0
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
    have h1 := hB.2 x hx h0
    have h2 := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix _ (hK k hk)) h0
    refine ⟨(map_ne_zero_iff C C.injective).2 h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hC, hfix k hk],
      h2.2.2.1, fun ϖ hϖ j hj => ?_⟩
    have e := heckeAdj F a w V ρ H hH x hx ϖ hϖ j
    rw [h1.2.2.2 ϖ hϖ j hj, h2.2.2.2 ϖ hϖ j hj, H.map_smulₛₗ, (H x).map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul] at e
    have e' := mul_right_cancel₀ (fun h => h0 (hdef x h)) e
    rw [← e', ← C.map_smulₛₗ, ← h1.2.2.2 ϖ hϖ j hj]
    refine ((C.toLinearMap.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x)).trans (finsum_congr fun c => ?_)).symm
    generalize c.out = g
    change C (_ • ρ g x) = _ • ρ' g (C x)
    rw [C.map_smulₛₗ, hC]
    congr 1
    unfold Formalism.UG.Tj
    by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
        ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
    · rw [Set.indicator_of_mem hg, Pi.one_apply, map_one]
    · rw [Set.indicator_of_notMem hg, map_zero]
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx.2.1 hx.1).2.1, (key x hx.2.1 hx.1).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := C.surjective y
    refine key x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => C.injective ?_) ((map_ne_zero_iff C C.injective).1 h0)
    rw [hC, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
end
