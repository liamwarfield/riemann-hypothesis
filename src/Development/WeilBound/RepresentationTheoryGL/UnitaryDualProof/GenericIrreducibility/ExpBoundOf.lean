module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FactorIrr : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), IsSmooth A → IsSmooth B →
    (prod₂ A B).IsIrreducible → A.IsIrreducible ∧ B.IsIrreducible

def Comm2Irr : Prop :=
  ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N),
    (prodIrr ![x, y] hd).IsIrreducible → (prodIrr ![y, x] hd').IsIrreducible

def MoveLast : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (prodIrr x hd).IsIrreducible → ∀ j : Fin h,
    ∃ (y : IrrGL (k := k)) (hd2 : ∑ a, (![y, x j] a).1 = N), Nonempty ((prodIrr x hd).Equiv (prodIrr ![y, x j] hd2))

def MoveFirst : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (prodIrr x hd).IsIrreducible → ∀ j : Fin h,
    ∃ (y : IrrGL (k := k)) (hd2 : ∑ a, (![x j, y] a).1 = N), Nonempty ((prodIrr x hd).Equiv (prodIrr ![x j, y] hd2))

def ThetaProd : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), IsSmooth A → IsSmooth B →
    Nonempty (Representation.Equiv ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t)))
      (ind₂ (stdSum (add_comm t r)) (extTensor (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r)))))

def ThetaFacts : Prop :=
  (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsGeneric π → IsGeneric (π.comp (Zc.Cos.thetaW k N))) ∧
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (ω : kˣ →* ℂˣ),
    HasCentralChar π ω → HasCentralChar (π.comp (Zc.Cos.thetaW k N)) ω⁻¹

def CentralProd2 : Prop :=
  ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (ω ω' : kˣ →* ℂˣ), HasCentralChar x.rep ω →
    HasCentralChar y.rep ω' → HasCentralChar (prodIrr ![x, y] hd) (ω * ω')

end PositivityTheory.RgUd.Exp
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ThetaProducts.ThetaProd
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.ThetaPf

open GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.ThetaW

theorem thetaProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.ThetaProd k := by
  intro r t V W _ _ _ _ A B _ _
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum (rfl : r + t = r + t)) (stdSum (add_comm t r))
    (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap (k := k) A B
  exact ⟨(compInvTEquiv (prod₂ A B)).symm.trans (κ.symm.trans
    (ind₂Equiv _ (τ.trans (extTensorCongr (compInvTEquiv B) (compInvTEquiv A)))))⟩

end PositivityTheory.RgUd.Exp.ThetaPf

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ContragredientSwap.IsIrreducibleOfContraSwap
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped TensorProduct
open GlobalTheory.CompanionTheory.BZSegComm
open Zc.Cos (invT)

namespace PositivityTheory.RgUd.Exp.Comm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isIrreducible_comp_invT {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)) := by
  have e : (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)).comp (invT : GL (Fin N) k →* GL (Fin N) k) = π :=
    MonoidHom.ext fun g => congrArg (⇑π) (invT_invT g)
  exact GlobalTheory.SwapTwo.isIrreducible_of_comp (invT : GL (Fin N) k →* GL (Fin N) k) (by rw [e]; exact h)

theorem isIrreducible_of_contra_swap {r t N : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hAa : IsAdmissible A) (hAi : A.IsIrreducible) (hBa : IsAdmissible B) (hBi : B.IsIrreducible)
    (h : r + t = N) (h' : t + r = N)
    (ρX : Representation ℂ (GL (Fin N) k) X) (ρY : Representation ℂ (GL (Fin N) k) Y)
    (eX : ρX.Equiv (ind₂ (stdSum h) (extTensor A B)))
    (eY : (ind₂ (stdSum h') (extTensor (contra B) (contra A))).Equiv ρY)
    (hX : ρX.IsIrreducible) : ρY.IsIrreducible := by
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap A B
  obtain ⟨ga⟩ := nonempty_comp_invT_equiv_contra A hAa hAi
  obtain ⟨gb⟩ := nonempty_comp_invT_equiv_contra B hBa hBi
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv
    (((compEquiv eX _).trans κ.symm).trans ((ind₂Equiv _ (τ.trans (extTensorCongr gb ga))).trans eY))
    (isIrreducible_comp_invT _ hX)

theorem prodIrr_swap_isIrreducible (F G : Fin 2 → IrrGL (k := k)) (e₀ : G 0 = F 1) (e₁ : G 1 = F 0) {N : ℕ}
    (hd : ∑ a, (F a).1 = N) (hd' : ∑ a, (G a).1 = N) (hX : (prodIrr F hd).IsIrreducible) :
    (prodIrr G hd').IsIrreducible := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have h : (F 0).1 + (F 1).1 = N := (Fin.sum_univ_two _).symm.trans hd
  have h' : (G 0).1 + (G 1).1 = N := (Fin.sum_univ_two _).symm.trans hd'
  have h'' : (F 1).1 + (F 0).1 = N := by rw [← e₀, ← e₁]; exact h'
  have aX := hA k N _ _ (isSmooth_prodIrr _ hd) hX
  have a0 := hA k _ _ (F 0).rep (F 0).2.rep.smooth (F 0).2.rep.irr
  have a1 := hA k _ _ (F 1).rep (F 1).2.rep.smooth (F 1).2.rep.irr
  have R0 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 0).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a0 a0
  have R1 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 1).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a1 a1
  have RX := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin N) k) (GlobalTheory.LocalThetaGL.compact_open_basis _)
    _ _ _ _ aX aX
  have c0i := R0.1 (F 0).2.rep.irr
  have c1i := R1.1 (F 1).2.rep.irr
  have c0a := hA k _ _ (contra (F 0).rep) (isSmooth_contra _) c0i
  have c1a := hA k _ _ (contra (F 1).rep) (isSmooth_contra _) c1i
  obtain ⟨ε⟩ := nonempty_ind₂_contra_equiv hA F hd h
  have e0 := R0.2.1.some
  have e1 := R1.2.1.some
  obtain ⟨m⟩ := nonempty_ind₂_equiv_multiProd (k := k) (d := fun a => (G a).1) hd' h' fun a => (G a).rep
  have E₃ : ∀ (u v : IrrGL (k := k)), u = F 1 → v = F 0 → ∀ h₁ : u.1 + v.1 = N,
      Nonempty ((ind₂ (stdSum h'') (extTensor (F 1).rep (F 0).rep)).Equiv
        (ind₂ (stdSum h₁) (extTensor u.rep v.rep))) := by
    rintro _ _ rfl rfl _
    exact ⟨.refl _⟩
  have e₄ := (E₃ _ _ e₀ e₁ h').some
  exact isIrreducible_of_contra_swap (contra (F 0).rep) (contra (F 1).rep) c0a c0i c1a c1i h h''
    (contra (prodIrr F hd)) (prodIrr G hd') ε.symm
    (((ind₂Equiv _ (extTensorCongr e1.symm e0.symm)).trans e₄).trans m) (RX.1 hX)

end Lemmas

theorem comm2Irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.Comm2Irr k := by
  intro x y N hd hd' hX
  exact prodIrr_swap_isIrreducible ![x, y] ![y, x] rfl rfl hd hd' hX

end PositivityTheory.RgUd.Exp.Comm

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.IrreducibleFactors.FactorIrr
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.RgUd.Exp.Fact

theorem factorIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.FactorIrr k := by
  intro r t V W _ _ _ _ A B hAs hBs hI
  classical
  obtain ⟨hX, hIirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hI
  let ρ' := (extTensor A B).comp (GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hAs hBs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have key : ∀ R : Submodule ℂ (V ⊗[ℂ] W), (∀ l, ∀ y ∈ R, ρ' l y ∈ R) → R = ⊥ ∨ R = ⊤ := by
    intro R hR
    let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
      { carrier := {f | ∀ g, f.1.1 g ∈ R}
        add_mem' := fun ha hb g => add_mem (ha g) (hb g)
        zero_mem' := fun g => zero_mem R
        smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
    have hYs : ∀ g, ∀ f ∈ Y, prod₂ A B g f ∈ Y := fun g f hf x => hf (x * g)
    rcases hIirr Y hYs with hY | hY
    · left
      refine (Submodule.eq_bot_iff R).2 fun u hu => ?_
      obtain ⟨f, h1, h2⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := fun g => by
        rcases h2 g with h | ⟨l, c, h⟩
        · rw [h]; exact zero_mem R
        · rw [h]; exact R.smul_mem c (hR l u hu)
      rw [hY, Submodule.mem_bot] at hf
      rw [← h1, hf]; rfl
    · right
      refine eq_top_iff.2 fun u _ => ?_
      obtain ⟨f, h1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := by rw [hY]; exact Submodule.mem_top
      rw [← h1]; exact hf 1
  have h0 : ¬ ∀ z : V ⊗[ℂ] W, z = 0 := by
    intro h
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h _).trans (h _).symm)))
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact h0 fun z => TensorProduct.induction_on (motive := fun z => z = 0) z rfl
      (fun x w => by rw [Subsingleton.elim x 0, TensorProduct.zero_tmul])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    exact h0 fun z => TensorProduct.induction_on (motive := fun z => z = 0) z rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  refine ⟨(GlobalTheory.CuspRep.isIrreducible_iff A).2 ⟨hV, fun S hS => ?_⟩,
    (GlobalTheory.CuspRep.isIrreducible_iff B).2 ⟨hW, fun S hS => ?_⟩⟩
  · obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℂ W, ψ w₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V ψ
    have hL : ∀ x w, L (x ⊗ₜ w) = ψ w • x := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.rTensor W S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x, hS _ _ x.2⟩ ⊗ₜ
          B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.rTensor_tmul, hL]; exact S.smul_mem _ x.2
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : s ⊗ₜ[ℂ] w₀ ∈ R := ⟨⟨s, hs⟩ ⊗ₜ w₀, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (s ⊗ₜ w₀) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hψ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : v ⊗ₜ[ℂ] w₀ ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hψ).1 h2
  · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
    have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
          ⟨B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : x₀ ⊗ₜ[ℂ] s ∈ R := ⟨x₀ ⊗ₜ ⟨s, hs⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (x₀ ⊗ₜ s) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hφ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : x₀ ⊗ₜ[ℂ] v ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hφ).1 h2

end PositivityTheory.RgUd.Exp.Fact
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterTheta.HasCentralCharCompThetaW
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.Facts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isGeneric_comp_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (h : IsGeneric π) : IsGeneric (π.comp (Zc.Cos.thetaW k N)) := by
  obtain ⟨ψ, hc, h1, hg⟩ := h
  refine ⟨ψ⁻¹, ?_, inv_ne_one.mpr h1, ?_⟩
  · have e : (⇑(ψ⁻¹) : k → Circle) = fun x => ψ (-x) := by
      funext x
      exact AddChar.inv_apply ψ x
    rw [e]
    exact hc.comp continuous_neg
  · unfold IsGenericFor TwJacquet at hg ⊢
    rw [Submodule.Quotient.nontrivial_iff] at hg ⊢
    intro htop
    apply hg
    rw [eq_top_iff] at htop ⊢
    refine htop.trans ?_
    unfold twKer
    refine Submodule.span_le.mpr ?_
    rintro w ⟨n, v, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨Zc.Cos.thetaW k N n, GlobalTheory.CompanionTheory.StdQuot.thetaW_mem_unipB n.2⟩, v, ?_⟩
    rw [GlobalTheory.CompanionTheory.StdQuot.whitChar_thetaW, ← GlobalTheory.CompanionTheory.StdQuot.whitChar_inv]
    rfl

theorem thetaW_scalar (N : ℕ) (z : kˣ) :
    Zc.Cos.thetaW k N (GeneralLinearGroup.scalar (Fin N) z) = GeneralLinearGroup.scalar (Fin N) z⁻¹ := by
  ext i j
  rw [GlobalTheory.CompanionTheory.StdQuot.thetaW_apply, ← map_inv]
  simp [GeneralLinearGroup.scalar]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal_apply, hij, Ne.symm hij]

theorem hasCentralChar_comp_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ω : kˣ →* ℂˣ) (h : HasCentralChar π ω) :
    HasCentralChar (π.comp (Zc.Cos.thetaW k N)) ω⁻¹ := by
  intro z v
  rw [MonoidHom.comp_apply, thetaW_scalar, h z⁻¹ v, MonoidHom.inv_apply, map_inv]

theorem hasCentralChar_prodIrr_two (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (ω ω' : kˣ →* ℂˣ)
    (hx : HasCentralChar x.rep ω) (hy : HasCentralChar y.rep ω') :
    HasCentralChar (prodIrr ![x, y] hd) (ω * ω') := by
  have key := GlobalTheory.CentralSupport.hasCentralChar_multiProd_prod
    (stdBlocks (fun a : Fin 2 => (![x, y] a).fst) hd) (fun a : Fin 2 => (![x, y] a).rep) ![ω, ω']
    (by
      intro a
      fin_cases a
      · exact hx
      · exact hy)
  rw [Fin.prod_univ_two] at key
  exact key

end PositivityTheory.RgUd.Exp.Facts

namespace PositivityTheory.RgUd.Exp

theorem thetaFacts (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ThetaFacts k :=
  ⟨fun _ _ _ _ π h => Facts.isGeneric_comp_thetaW π h,
    fun _ _ _ _ π ω h => Facts.hasCentralChar_comp_thetaW π ω h⟩

theorem centralProd2 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralProd2 k :=
  fun x y N hd ω ω' hx hy => Facts.hasCentralChar_prodIrr_two x y N hd ω ω' hx hy

end PositivityTheory.RgUd.Exp

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.FirstPairExistence.ExistsPairFirst
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.Move2

open PositivityTheory.RgUd.Exp

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem factor_of_equiv (hF : FactorIrr k) {r t : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {A : Representation ℂ (GL (Fin r) k) V}
    {B : Representation ℂ (GL (Fin t) k) W} {π : Representation ℂ (GL (Fin (r + t)) k) U}
    (E : Nonempty ((prod₂ A B).Equiv π)) (hπ : π.IsIrreducible) (hA : IsSmooth A) (hB : IsSmooth B) :
    A.IsIrreducible ∧ B.IsIrreducible := by
  obtain ⟨e⟩ := E
  exact hF r t V W A B hA hB (GlobalTheory.Parabolic.isIrreducible_of_equiv e.symm hπ)

private theorem sum_fst_fin_append {k : Type} [Field k] [TopologicalSpace k] {m n : ℕ}
    (f : Fin m → IrrGL (k := k)) (g : Fin n → IrrGL (k := k)) :
    ∑ a, (Fin.append f g a).1 = (∑ a, (f a).1) + ∑ a, (g a).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem nonempty_prodIrr_equiv_of_eq_comp_cast {m n N : ℕ} (e : m = n) (f : Fin m → IrrGL (k := k)) (g : Fin n → IrrGL (k := k))
    (hfg : f = g ∘ Fin.cast e) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N) :
    Nonempty ((prodIrr f hf).Equiv (prodIrr g hg)) := by
  subst e
  have hfg' : f = g := by
    rw [hfg]
    funext a
    simp
  subst hfg'
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem pair_irr (hF : FactorIrr k) {h N : ℕ} (y : Fin h → IrrGL (k := k)) (i j : Fin h) (hij : (j : ℕ) = i + 1)
    (hd : ∑ a, (y a).1 = N) (hirr : (prodIrr y hd).IsIrreducible) (q : ℕ) (hq : ∑ t, (![y i, y j] t).1 = q) :
    (prodIrr ![y i, y j] hq).IsIrreducible := by
  subst hq
  obtain ⟨s, hs⟩ : ∃ s, (i : ℕ) + (2 + s) = h := ⟨h - i - 2, by have := j.2; omega⟩
  obtain ⟨P, hP⟩ : ∃ P : Fin i → IrrGL (k := k), ∀ a, P a = y ⟨a, by have := a.2; have := i.2; omega⟩ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin s → IrrGL (k := k), ∀ b, S b = y ⟨i + 2 + b, by have := b.2; omega⟩ :=
    ⟨_, fun _ => rfl⟩
  have hcomp : Fin.append P (Fin.append ![y i, y j] S) = y ∘ Fin.cast hs := by
    funext a
    refine Fin.addCases (fun a => ?_) (fun b => ?_) a
    · rw [Fin.append_left, hP]
      simp only [Function.comp_apply]
      congr 1
    · rw [Fin.append_right]
      refine Fin.addCases (fun c => ?_) (fun d => ?_) b
      · rw [Fin.append_left]
        fin_cases c
        · simp only [Function.comp_apply]
          show y i = _
          congr 1 <;> ext <;> simp
        · simp only [Function.comp_apply]
          show y j = _
          congr 1 <;> ext <;> simp [hij]
      · rw [Fin.append_right, hS]
        simp only [Function.comp_apply]
        congr 1 <;> ext <;> simp <;> omega
  have hQS : ∑ a, (Fin.append ![y i, y j] S a).1 = (∑ a, (![y i, y j] a).1) + ∑ a, (S a).1 :=
    sum_fst_fin_append _ _
  have hAll : ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 =
      (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1) := by
    rw [sum_fst_fin_append, hQS]
  have hsumY : ∑ a, (y a).1 = ∑ a, (Fin.append P (Fin.append ![y i, y j] S) a).1 := by
    rw [hcomp]
    exact (Fintype.sum_equiv (finCongr hs) _ _ (fun _ => rfl)).symm
  have hN : N = (∑ a, (P a).1) + ((∑ a, (![y i, y j] a).1) + ∑ a, (S a).1) := by
    rw [← hd, hsumY, hAll]
  subst hN
  obtain ⟨eC⟩ := nonempty_prodIrr_equiv_of_eq_comp_cast hs _ y hcomp hAll hd
  have irrA := GlobalTheory.Parabolic.isIrreducible_of_equiv eC.symm hirr
  obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k i (2 + s) _ _ P (Fin.append ![y i, y j] S) rfl hQS hAll
  have irrQS := (factor_of_equiv hF ⟨e2⟩ irrA (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 2 s _ _ ![y i, y j] S rfl rfl hQS
  exact (factor_of_equiv hF ⟨e3⟩ irrQS (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1

def PR {h : ℕ} (f g : Fin h → IrrGL (k := k)) : Prop :=
  ∑ a, (f a).1 = ∑ a, (g a).1 ∧
    ∀ (N : ℕ) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N),
      (prodIrr f hf).IsIrreducible → Nonempty ((prodIrr f hf).Equiv (prodIrr g hg))


set_option maxHeartbeats 1600000 in
theorem pr_swap (hF : FactorIrr k) (hC : Comm2Irr k) {h : ℕ} (f : Fin h → IrrGL (k := k)) (i j : Fin h)
    (hij : (j : ℕ) = i + 1) : PR f (f ∘ Equiv.swap i j) := by
  refine ⟨(Equiv.sum_comp (Equiv.swap i j) (fun a => (f a).1)).symm, ?_⟩
  intro N hf hg hirr
  refine GlobalTheory.CompanionTheory.ReorderRev.prodIrr_swap_adj f i j hij ?_ hf hg
  intro q hq hq'
  have hp := pair_irr hF f i j hij hf hirr q hq
  have hp' := hC (f i) (f j) q hq hq' hp
  exact GlobalTheory.CompanionTheory.BZSegComm.prodIrr_swap_of_isIrreducible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    ![f i, f j] ![f j, f i] rfl rfl hq hq' hp hp'

private theorem PR_refl {h : ℕ} (f : Fin h → IrrGL (k := k)) : PR f f :=
  ⟨rfl, fun _ _ _ _ => ⟨Representation.Equiv.refl _⟩⟩

private theorem PR_trans {h : ℕ} {f g g' : Fin h → IrrGL (k := k)} (h1 : PR f g) (h2 : PR g g') : PR f g' := by
  set_option maxHeartbeats 1600000 in
  refine ⟨h1.1.trans h2.1, fun N hf hg' hirr => ?_⟩
  have hg : ∑ a, (g a).1 = N := h1.1.symm.trans hf
  obtain ⟨e1⟩ := h1.2 N hf hg hirr
  have hirr2 : (prodIrr g hg).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hirr
  obtain ⟨e2⟩ := h2.2 N hg hg' hirr2
  exact ⟨e1.trans e2⟩


set_option maxHeartbeats 1600000 in
theorem pr_perm (hF : FactorIrr k) (hC : Comm2Irr k) {h : ℕ} (f : Fin h → IrrGL (k := k)) (σ : Equiv.Perm (Fin h)) :
    PR f (f ∘ σ) := by
  cases h with
  | zero =>
    have hc : f ∘ σ = f := funext (fun a => a.elim0)
    rw [hc]
    exact PR_refl f
  | succ n =>
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction generalizing f with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact pr_swap hF hC f _ _ (by simp)
    | one =>
      rw [Equiv.Perm.coe_one, Function.comp_id]
      exact PR_refl f
    | mul x y _ _ ihx ihy =>
      rw [Equiv.Perm.coe_mul]
      exact PR_trans (ihx f) (ihy (f ∘ x))

theorem prodIrr_cast {m n N : ℕ} (e : m = n) (f : Fin m → IrrGL (k := k)) (g : Fin n → IrrGL (k := k))
    (hfg : f = g ∘ Fin.cast e) (hf : ∑ a, (f a).1 = N) (hg : ∑ a, (g a).1 = N) :
    Nonempty ((prodIrr f hf).Equiv (prodIrr g hg)) := by
  subst e
  have hfg' : f = g := by
    rw [hfg]
    funext a
    simp
  subst hfg'
  exact ⟨Representation.Equiv.refl _⟩

def lastPerm {r : ℕ} (j : Fin (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' j).symm

def firstPerm {r : ℕ} (j : Fin (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  (finSuccEquiv r).trans (finSuccEquiv' j).symm

theorem comp_lastPerm {r : ℕ} {α : Type*} (x : Fin (r + 1) → α) (j : Fin (r + 1)) :
    x ∘ lastPerm j = Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    have e : (Fin.castAdd 1 i : Fin (r + 1)) = Fin.castSucc i := rfl
    simp [lastPerm, e]
  · rw [Fin.append_right]
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have e : (Fin.natAdd r (0 : Fin 1) : Fin (r + 1)) = Fin.last r := rfl
    simp [lastPerm, e]

theorem comp_firstPerm {r : ℕ} {α : Type*} (x : Fin (r + 1) → α) (j : Fin (r + 1)) :
    x ∘ firstPerm j = Fin.cons (x j) (x ∘ j.succAbove) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [firstPerm]
  · simp [firstPerm]


set_option maxHeartbeats 1600000 in
theorem exists_pair_last (x₀ : IrrGL (k := k)) {M : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] (A : Representation ℂ (GL (Fin M) k) V)
    (B : Representation ℂ (GL (Fin x₀.1) k) W) (π : Representation ℂ (GL (Fin (M + x₀.1)) k) U)
    (hAs : IsSmooth A) (hAi : A.IsIrreducible) (E : Nonempty ((prod₂ A B).Equiv π))
    (EB : Nonempty (x₀.rep.Equiv B)) :
    ∃ (y : IrrGL (k := k)) (hd2 : ∑ a, (![y, x₀] a).1 = M + x₀.1), Nonempty (π.Equiv (prodIrr ![y, x₀] hd2)) := by
  obtain ⟨e⟩ := E
  obtain ⟨eB⟩ := EB
  have hp : ∑ a, (![IrrGL.of A hAs hAi, x₀] a).1 = (IrrGL.of A hAs hAi).1 + x₀.1 := by
    simp [Fin.sum_univ_two]
  obtain ⟨e3⟩ := nonempty_prod₂_equiv_prodIrr_pair (IrrGL.of A hAs hAi) x₀ hp
  exact ⟨IrrGL.of A hAs hAi, hp, ⟨e.symm.trans ((prod₂Equiv (IrrGL.equivOf A hAs hAi) eB.symm).trans e3)⟩⟩


set_option maxHeartbeats 1600000 in
theorem exists_pair_first (x₀ : IrrGL (k := k)) {M : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] (A : Representation ℂ (GL (Fin x₀.1) k) V)
    (B : Representation ℂ (GL (Fin M) k) W) (π : Representation ℂ (GL (Fin (x₀.1 + M)) k) U)
    (hBs : IsSmooth B) (hBi : B.IsIrreducible) (E : Nonempty ((prod₂ A B).Equiv π))
    (EA : Nonempty (x₀.rep.Equiv A)) :
    ∃ (y : IrrGL (k := k)) (hd2 : ∑ a, (![x₀, y] a).1 = x₀.1 + M), Nonempty (π.Equiv (prodIrr ![x₀, y] hd2)) := by
  obtain ⟨e⟩ := E
  obtain ⟨eA⟩ := EA
  have hp : ∑ a, (![x₀, IrrGL.of B hBs hBi] a).1 = x₀.1 + (IrrGL.of B hBs hBi).1 := by
    simp [Fin.sum_univ_two]
  obtain ⟨e3⟩ := nonempty_prod₂_equiv_prodIrr_pair x₀ (IrrGL.of B hBs hBi) hp
  exact ⟨IrrGL.of B hBs hBi, hp, ⟨e.symm.trans ((prod₂Equiv eA.symm (IrrGL.equivOf B hBs hBi)).trans e3)⟩⟩

end Lemmas

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1600000 in
theorem moveLast : FactorIrr k → Comm2Irr k → MoveLast k := by
  intro hF hC h N x hd hirr j
  cases h with
  | zero => exact j.elim0
  | succ r =>
    have hcomp := comp_lastPerm x j
    have hy : ∑ _a : Fin 1, (x j).1 = (x j).1 := by simp
    have hApp : ∑ a, (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j) a).1 =
        (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hy]
    have hsumPerm : ∑ a, ((x ∘ lastPerm j) a).1 = ∑ a, (x a).1 :=
      Equiv.sum_comp (lastPerm j) (fun a => (x a).1)
    have hN : N = (∑ a, ((x ∘ j.succAbove) a).1) + (x j).1 := by
      rw [← hd, ← hsumPerm, hcomp, hApp]
    subst hN
    obtain ⟨e1⟩ := (pr_perm hF hC x (lastPerm j)).2 _ hd (hsumPerm.trans hd) hirr
    obtain ⟨eC⟩ := prodIrr_cast rfl (x ∘ lastPerm j) (Fin.append (x ∘ j.succAbove) (fun _ : Fin 1 => x j))
      (by rw [hcomp]; rfl) (hsumPerm.trans hd) hApp
    obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k r 1 _ _ (x ∘ j.succAbove) (fun _ : Fin 1 => x j) rfl hy hApp
    obtain ⟨eB⟩ := nonempty_equiv_prodIrr_one (x j) hy
    have E := e2.trans (eC.symm.trans e1.symm)
    have hAi := (factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).1
    exact exists_pair_last (x j) _ _ _ (isSmooth_prodIrr _ _) hAi ⟨E⟩ ⟨eB⟩

set_option maxHeartbeats 1600000 in
theorem moveFirst : FactorIrr k → Comm2Irr k → MoveFirst k := by
  intro hF hC h N x hd hirr j
  cases h with
  | zero => exact j.elim0
  | succ r =>
    have hfg : Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) =
        (x ∘ firstPerm j) ∘ Fin.cast (Nat.add_comm 1 r) := by
      rw [comp_firstPerm]
      funext a
      refine Fin.addCases (fun a => ?_) (fun b => ?_) a
      · rw [Fin.append_left]
        have e0 : Fin.cast (Nat.add_comm 1 r) (Fin.castAdd r a) = 0 := by
          ext
          have := a.2
          simp <;> omega
        simp only [Function.comp_apply, e0, Fin.cons_zero]
      · rw [Fin.append_right]
        have e1 : Fin.cast (Nat.add_comm 1 r) (Fin.natAdd 1 b) = b.succ := by
          ext
          simp [Nat.add_comm]
        simp only [Function.comp_apply, e1, Fin.cons_succ]
    have hy : ∑ _a : Fin 1, (x j).1 = (x j).1 := by simp
    have hApp : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 =
        (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hy]
    have hsumPerm : ∑ a, ((x ∘ firstPerm j) a).1 = ∑ a, (x a).1 :=
      Equiv.sum_comp (firstPerm j) (fun a => (x a).1)
    have hsumC : ∑ a, (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove) a).1 =
        ∑ a, ((x ∘ firstPerm j) a).1 := by
      rw [hfg]
      exact Fintype.sum_equiv (finCongr (Nat.add_comm 1 r)) _ _ (fun _ => rfl)
    have hN : N = (x j).1 + ∑ a, ((x ∘ j.succAbove) a).1 := by
      rw [← hd, ← hsumPerm, ← hsumC, hApp]
    subst hN
    obtain ⟨e1⟩ := (pr_perm hF hC x (firstPerm j)).2 _ hd (hsumPerm.trans hd) hirr
    obtain ⟨eC⟩ := prodIrr_cast (Nat.add_comm 1 r) (Fin.append (fun _ : Fin 1 => x j) (x ∘ j.succAbove))
      (x ∘ firstPerm j) hfg hApp (hsumPerm.trans hd)
    obtain ⟨e2⟩ := GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k 1 r _ _ (fun _ : Fin 1 => x j) (x ∘ j.succAbove) hy rfl hApp
    obtain ⟨eA⟩ := nonempty_equiv_prodIrr_one (x j) hy
    have E := e2.trans (eC.trans e1.symm)
    have hBi := (factor_of_equiv hF ⟨E⟩ hirr (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)).2
    exact exists_pair_first (x j) _ _ _ (isSmooth_prodIrr _ _) hBi ⟨E⟩ ⟨eA⟩

end PositivityTheory.RgUd.Exp.Move2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterZero.AsmCentralZero
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Exp.Asm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem asmGeneric {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (h : IsGeneric π) (φ : π.Equiv σ) : IsGeneric σ := by
  obtain ⟨ψ, hc, hne, hg⟩ := h
  exact ⟨ψ, hc, hne, hg.of_equiv φ⟩

theorem asmUnitComp {G H X : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (f : H →* G) (h : IsUnitarisable ρ) : IsUnitarisable (ρ.comp f) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  exact ⟨B, h1, h2, fun g v w => h3 (f g) v w⟩

theorem asmInd {r t N : ℕ} (e : r + t = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {A : Representation ℂ (GL (Fin r) k) V} {B : Representation ℂ (GL (Fin t) k) W}
    (hG : IsGeneric (ind₂ (stdSum e) (extTensor A B))) (hU : IsUnitarisable (ind₂ (stdSum e) (extTensor A B))) :
    IsGeneric (prod₂ A B) ∧ IsUnitarisable (prod₂ A B) := by
  subst e
  exact ⟨hG, hU⟩

theorem asmScalar {n : ℕ} (hn : n = 0) (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = 1 :=
  Units.ext (Matrix.ext fun i _ => absurd i.2 (by omega))

theorem asmCentralZero {n : ℕ} (hn : n = 0) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k) V) : HasCentralChar ρ 1 := fun z v => by
  rw [asmScalar hn z, map_one]
  simp

theorem asmNormInv (ω : kˣ →* ℂˣ) (m s : ℝ) (hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ (m * s)) :
    ∀ z, ‖((ω⁻¹ : kˣ →* ℂˣ) z : ℂ)‖ = nabs k z ^ (m * -s) := by
  intro z
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hn, ← Real.rpow_neg (nabs_pos' k z).le, mul_neg]

theorem asmZero (ω : kˣ →* ℂˣ) (m : ℕ) (hm : 0 < m) (s : ℝ)
    (hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ ((m : ℝ) * s)) (h1 : ∀ z, ‖(ω z : ℂ)‖ = 1) : s = 0 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hpos := nabs_pos' k ϖ
  have h2 : nabs k ϖ ^ ((m : ℝ) * s) = 1 := (hn ϖ).symm.trans (h1 ϖ)
  have h3 : (m : ℝ) * s * Real.log (nabs k ϖ) = 0 := by
    have := congrArg Real.log h2
    rwa [Real.log_rpow hpos, Real.log_one] at this
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  rcases mul_eq_zero.1 h3 with h | h
  · exact (mul_eq_zero.1 h).resolve_left hm'
  · exact absurd h hL0

theorem asmLower (hL : ExpLow k) (y z : IrrGL (k := k)) {N : ℕ} (hd2 : ∑ a, (![y, z] a).1 = N)
    (hG : IsGeneric (prodIrr ![y, z] hd2)) (hU : IsUnitarisable (prodIrr ![y, z] hd2)) (hy : 1 ≤ y.1)
    (ω : kˣ →* ℂˣ) (s : ℝ) (hm : 0 < z.1) (hω : HasCentralChar z.rep ω)
    (hn : ∀ w, ‖(ω w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * s)) : -1 / 2 < s := by
  have h : y.1 + z.1 = N := (Fin.sum_univ_two _).symm.trans hd2
  have E : Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd2)) :=
    GlobalTheory.CompanionTheory.BZSegComm.nonempty_ind₂_equiv_multiProd (d := fun a => (![y, z] a).1) hd2 h
      (fun a => (![y, z] a).rep)
  obtain ⟨E⟩ := E
  have hgu := asmInd h (asmGeneric hG E.symm) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E.symm hU)
  exact hL y.1 z.1 _ _ y.rep z.rep ω s hy hm y.2.rep.smooth z.2.rep.smooth hgu.1 hgu.2 hω hn

theorem asmThetaGU (hT : ThetaProd k) (hF : ThetaFacts k) {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hA : IsSmooth A) (hB : IsSmooth B) (hG : IsGeneric (prod₂ A B)) (hU : IsUnitarisable (prod₂ A B)) :
    IsGeneric (prod₂ (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r))) ∧
      IsUnitarisable (prod₂ (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r))) := by
  obtain ⟨Θ⟩ := hT r t V W A B hA hB
  have hG2 : IsGeneric ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t))) := hF.1 _ _ _ hG
  have hU2 : IsUnitarisable ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t))) := asmUnitComp _ _ hU
  exact asmInd (add_comm t r) (asmGeneric hG2 Θ) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv Θ hU2)

theorem asmSmoothTheta {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (h : IsSmooth ρ) : IsSmooth (ρ.comp (Zc.Cos.thetaW k n)) :=
  GlobalTheory.SmGL.isSmooth_comp h _ (GlobalTheory.CompanionTheory.ThetaProd.continuous_thetaW n)

theorem asmPair (z y : IrrGL (k := k)) {N : ℕ} (hd3 : ∑ a, (![z, y] a).1 = N) (hG : IsGeneric (prodIrr ![z, y] hd3))
    (hU : IsUnitarisable (prodIrr ![z, y] hd3)) :
    IsGeneric (prod₂ z.rep y.rep) ∧ IsUnitarisable (prod₂ z.rep y.rep) := by
  have h : z.1 + y.1 = N := (Fin.sum_univ_two _).symm.trans hd3
  have E : Nonempty ((ind₂ (stdSum h) (extTensor z.rep y.rep)).Equiv (prodIrr ![z, y] hd3)) :=
    GlobalTheory.CompanionTheory.BZSegComm.nonempty_ind₂_equiv_multiProd (d := fun a => (![z, y] a).1) hd3 h
      (fun a => (![z, y] a).rep)
  obtain ⟨E⟩ := E
  exact asmInd h (asmGeneric hG E.symm) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E.symm hU)

theorem asmUpper (hL : ExpLow k) (hT : ThetaProd k) (hF : ThetaFacts k) (z y : IrrGL (k := k)) {N : ℕ}
    (hd3 : ∑ a, (![z, y] a).1 = N) (hG : IsGeneric (prodIrr ![z, y] hd3))
    (hU : IsUnitarisable (prodIrr ![z, y] hd3)) (hy : 1 ≤ y.1) (ω : kˣ →* ℂˣ) (s : ℝ) (hm : 0 < z.1)
    (hω : HasCentralChar z.rep ω) (hn : ∀ w, ‖(ω w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * s)) : -1 / 2 < -s := by
  have hgu := asmPair z y hd3 hG hU
  have hgu2 := asmThetaGU hT hF z.rep y.rep z.2.rep.smooth y.2.rep.smooth hgu.1 hgu.2
  have hc : HasCentralChar (z.rep.comp (Zc.Cos.thetaW k z.1)) ω⁻¹ := hF.2 _ _ _ _ hω
  have hn2 : ∀ w, ‖((ω⁻¹ : kˣ →* ℂˣ) w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * -s) := asmNormInv ω _ _ hn
  exact hL y.1 z.1 _ _ (y.rep.comp (Zc.Cos.thetaW k y.1)) (z.rep.comp (Zc.Cos.thetaW k z.1)) ω⁻¹ (-s) hy hm
    (asmSmoothTheta _ y.2.rep.smooth) (asmSmoothTheta _ z.2.rep.smooth) hgu2.1 hgu2.2 hc hn2

end PositivityTheory.RgUd.Exp.Asm

namespace PositivityTheory.RgUd.Exp

open PositivityTheory.RgUd.Exp.Asm

theorem expBound_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    MoveLast k → MoveFirst k → ThetaProd k → ThetaFacts k → CentralProd2 k → ExpLow k → ExpBound k := by
  intro hML hMF hT hF hC hL
  unfold ExpBound
  intro h N x hd hirr hU hG j ω s hm hω hn
  obtain ⟨y, hd2, ⟨E⟩⟩ := hML h N x hd hirr j
  have hy2 : y.1 + (x j).1 = N := (Fin.sum_univ_two _).symm.trans hd2
  rcases Nat.eq_zero_or_pos y.1 with hy0 | hy0
  · have hcy : HasCentralChar y.rep 1 := asmCentralZero hy0 y.rep
    have hcπ : HasCentralChar (prodIrr ![y, x j] hd2) (1 * ω) := hC y (x j) N hd2 1 ω hcy hω
    have hcπ' : HasCentralChar (prodIrr x hd) (1 * ω) := hasCentralChar_of_equiv E.symm hcπ
    have := Model.nontrivial_of_isIrreducible hirr
    have h1 : ∀ z, ‖(((1 * ω) z : ℂˣ) : ℂ)‖ = 1 := fun z =>
      GlobalTheory.LocGL.UnitaryOrder.norm_eq_one_of_isUnitarisable hU (hcπ' z)
    have hs : s = 0 := asmZero ω (x j).1 hm s hn (fun z => by simpa using h1 z)
    rw [hs, abs_zero]
    norm_num
  · have hlow := asmLower hL y (x j) hd2 (asmGeneric hG E)
      (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E hU) hy0 ω s hm hω hn
    obtain ⟨y', hd3, ⟨E'⟩⟩ := hMF h N x hd hirr j
    have hy3 : (x j).1 + y'.1 = N := (Fin.sum_univ_two _).symm.trans hd3
    have hy' : 1 ≤ y'.1 := by omega
    have hup := asmUpper hL hT hF (x j) y' hd3 (asmGeneric hG E')
      (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E' hU) hy' ω s hm hω hn
    rw [abs_lt]
    constructor <;> linarith

end PositivityTheory.RgUd.Exp
end
end

namespace PositivityTheory.RgUd.Exp.Final

open PositivityTheory.RgUd.Exp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem expBound (hL : ExpLow k) : ExpBound k :=
  PositivityTheory.RgUd.Exp.expBound_of k
    (Move2.moveLast k (Fact.factorIrr k) (Comm.comm2Irr k)) (Move2.moveFirst k (Fact.factorIrr k) (Comm.comm2Irr k))
    (ThetaPf.thetaProd k) (thetaFacts k) (centralProd2 k) hL

theorem expBound_of : ExpLow k → ExpBound k := expBound k

end PositivityTheory.RgUd.Exp.Final
