module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsmPfB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMemStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_pull_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  first | exact @GlobalTheory.CuspEmb.pull_mem_SS | exact GlobalTheory.CuspEmb.pull_mem_SS | (intros; apply GlobalTheory.CuspEmb.pull_mem_SS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisors
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

theorem isOpen_isPreconnected_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) : IsOpen M.dom ∧ IsPreconnected M.dom := by
  have key : ∀ (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ),
      X.Ψ = Ψ → X.Gm = Gm → X.p0 = p0 → IsOpen (GG Ψ Gm p0) ∧ IsPreconnected (GG Ψ Gm p0) := by
    intro X Ψ Gm p0 h1 h2 h3
    subst h1 h2 h3
    exact ⟨FourierCoefficientDomain.isOpen_dom X, (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected⟩
  exact key (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c)

theorem C_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) →
    Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  intro E _ _ _ r U C _ _ M D hD
  have key : ∀ p : Polynomial (HA M), p * Polynomial.C D = 0 → p = 0 := by
    intro p hp
    apply Polynomial.ext
    intro i
    have hq : p.coeff i * D = 0 := by
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hp
      simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at this
      exact this
    have hq' : ((p.coeff i : HA M) : C → M.dom → ℂ) * (D : C → M.dom → ℂ) = 0 := by
      have := congrArg (fun f : HA M => (f : C → M.dom → ℂ)) hq
      exact this
    rw [Polynomial.coeff_zero]
    apply Subtype.ext
    funext c x
    obtain ⟨x0, hx0⟩ := hD c
    obtain ⟨GD, hGD, hGD'⟩ := D.2.1 c
    obtain ⟨Gq, hGq, hGq'⟩ := (p.coeff i).2.1 c
    obtain ⟨hO, hC⟩ := isOpen_isPreconnected_dom M c
    have h0 : GD x0.1 ≠ 0 := by rw [← hGD']; exact hx0
    have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hO hC hGD hGq
      (fun y hy => by
        have := congrFun (congrFun hq' c) ⟨y, hy⟩
        simp only [Pi.mul_apply, Pi.zero_apply] at this
        rw [← hGD' ⟨y, hy⟩, ← hGq' ⟨y, hy⟩, mul_comm]
        exact this) x0.2 h0 x.1 x.2
    show ((p.coeff i : HA M) : C → M.dom → ℂ) c x = ((0 : HA M) : C → M.dom → ℂ) c x
    rw [hGq' x, hz]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x ?_, key⟩
  rwa [mul_comm] at hx

end GlobalTheory.CuspEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisorsStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) → Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  first | exact @GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | exact GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | (intros; apply GlobalTheory.CuspEmb.C_mem_nonZeroDivisors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentation
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add (f := _), Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentationStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_pullbackRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  first | exact @GlobalTheory.PullCocycle.exists_cocycle | exact GlobalTheory.PullCocycle.exists_cocycle | (intros; apply GlobalTheory.PullCocycle.exists_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycle
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem pbA_comp (M : TwoLevels E r U C) (u v : U) (f : HA M) :
    pbA M v (pbA M u f) = pbA M (u * v) f := by
  apply Subtype.ext
  funext c x
  show f.1 (u • v • c) ⟨lact (M.tr u (v • c)) (lact (M.tr v c) x.1), _⟩ =
    f.1 ((u * v) • c) ⟨lact (M.tr (u * v) c) x.1, _⟩
  rw [show u • v • c = (u * v) • c from (mul_smul u v c).symm]
  have hγ := M.tr_mul u v c
  have hy : lact (M.tr u (v • c) * M.tr v c) x.1 ∈ M.dom := by
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]
    exact lact_tr_mem M u _ (lact_tr_mem M v c x.2)
  have e : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1) =
      lact (M.tr (u * v) c) x.1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel_right]
  have hz : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹)
      (⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ : M.dom).1 ∈ M.dom := by
    show lact _ (lact _ x.1) ∈ M.dom
    rw [e]; exact lact_tr_mem M (u * v) c x.2
  have key := f.2.2 ((u * v) • c) _ hγ ⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ hz
  rw [show (⟨lact (M.tr (u * v) c) x.1, lact_tr_mem M (u * v) c x.2⟩ : M.dom) =
      ⟨lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1), hz⟩
      from Subtype.ext e.symm, key]
  exact congrArg (f.1 _) (Subtype.ext (ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul _ _ _).symm)

theorem pbA_one (M : TwoLevels E r U C) (f : HA M) : pbA M 1 f = f := by
  apply Subtype.ext
  funext c x
  show f.1 ((1 : U) • c) ⟨lact (M.tr 1 c) x.1, _⟩ = f.1 c x
  have hγ := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at hγ
  rw [mul_inv_rev, mul_inv_cancel_left] at hγ
  have hz : lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) ∈ M.dom := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    exact x.2
  have key := f.2.2 c _ hγ ⟨lact (M.tr 1 c) x.1, lact_tr_mem M 1 c x.2⟩ hz
  simp only [one_smul]
  rw [← key]
  refine congrArg (f.1 c) (Subtype.ext ?_)
  show lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) = x.1
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]

theorem tw_law (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (a : U → C → ℂˣ) (ha : ∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) :
    tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧
      ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) =
        tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  refine ⟨?_, fun u v => ?_⟩
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ 1 (Polynomial.C f) = Polynomial.C f
      rw [tw_C, pbA_one]
    · show tw M _ 1 Polynomial.X = Polynomial.X
      rw [tw_X]
      have h1 : cst M (fun c => (a 1 c : ℂ)) = 1 := by
        apply Subtype.ext
        funext c x
        show (a 1 c : ℂ) = 1
        have h := ha 1 1 c
        rw [one_mul, one_smul] at h
        have h' : a 1 c = 1 := by
          have := congrArg (fun t => (a 1 c)⁻¹ * t) h
          simpa using this.symm
        rw [h', Units.val_one]
      rw [h1, map_one, one_mul]
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ v (tw M _ u (Polynomial.C f)) = tw M _ (u * v) (Polynomial.C f)
      rw [tw_C, tw_C, tw_C, pbA_comp]
    · show tw M _ v (tw M _ u Polynomial.X) = tw M _ (u * v) Polynomial.X
      rw [tw_X, map_mul, tw_C, tw_X, tw_X, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      apply Subtype.ext
      funext c x
      show (a u (v • c) : ℂ) * (a v c : ℂ) = (a (u * v) c : ℂ)
      rw [ha v u c, Units.val_mul, mul_comm]

end GlobalTheory.CuspEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycleStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (a : U → C → ℂˣ), (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) → tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧ ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) = tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  first | exact @GlobalTheory.CuspEmb.tw_law | exact GlobalTheory.CuspEmb.tw_law | (intros; apply GlobalTheory.CuspEmb.tw_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem twoLevels_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  intro E _ _ _ r U C _ _ M la mu F G hF hG c
  have hP := hF c
  have hQ := (hG c).1
  have h := ReciprocityTheory.ChartRestriction.G.AR.Up.ss_mul_pow (M.comp c).toData hP hQ 1
  have hw : castWt (M.comp_Ψ c) (la + mu) =
      castWt (M.comp_Ψ c) la + 1 • castWt (M.comp_Ψ c) mu := by
    rw [one_smul]; funext τ; rfl
  rw [hw]
  rw [pow_one] at h
  exact h

end GlobalTheory.CuspEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeightStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  first | exact @GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | exact GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | (intros; apply GlobalTheory.CuspEmb.twoLevels_mul_mem_SS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariantStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → M.res F ∈ HA M := by
  first | exact @GlobalTheory.CuspEmb.res_mem_HA | exact GlobalTheory.CuspEmb.res_mem_HA | (intros; apply GlobalTheory.CuspEmb.res_mem_HA <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def deg1 (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) : Submodule ℂ (Polynomial (HA M)) :=
  (W.comap (HA M).val.toLinearMap).map ((Polynomial.monomial 1).restrictScalars ℂ)

theorem mem_homogeneousExponentsOneBlock (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (p : Polynomial (HA M)) :
    p ∈ deg1 M W ↔ ∃ f : HA M, (f : C → M.dom → ℂ) ∈ W ∧ Polynomial.monomial 1 f = p := Iff.rfl

def deg1Equiv (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) :
    W ≃ₗ[ℂ] deg1 M W :=
  LinearEquiv.ofBijective
    ({ toFun := fun f => ⟨Polynomial.monomial 1 ⟨f, hW f f.2⟩, (mem_homogeneousExponentsOneBlock M W _).2 ⟨⟨f, hW f f.2⟩, f.2, rfl⟩⟩
       map_add' := fun f g => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((f + g : W) : C → M.dom → ℂ), hW _ (f + g).2⟩ : HA M) =
           Polynomial.monomial 1 ⟨f, hW _ f.2⟩ + Polynomial.monomial 1 ⟨g, hW _ g.2⟩
         rw [← map_add (f := _)]
         rfl)
       map_smul' := fun z f => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((z • f : W) : C → M.dom → ℂ), hW _ (z • f).2⟩ : HA M) =
           z • Polynomial.monomial 1 ⟨f, hW _ f.2⟩
         rw [Polynomial.smul_monomial]
         rfl) } :
      W →ₗ[ℂ] deg1 M W)
    ⟨fun f g hfg => by
      have := congrArg Subtype.val hfg
      have := Polynomial.monomial_injective 1 this
      exact Subtype.ext (congrArg (fun q : HA M => (q : C → M.dom → ℂ)) this),
     fun p => by
      obtain ⟨f, hf, hp⟩ := (mem_homogeneousExponentsOneBlock M W p.1).1 p.2
      exact ⟨⟨f, hf⟩, Subtype.ext hp⟩⟩

theorem deg1Equiv_coe (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) (f : W) :
    ((deg1Equiv M W hW f : deg1 M W) : Polynomial (HA M)) = Polynomial.monomial 1 ⟨f, hW f f.2⟩ := rfl

theorem mul_pb_mem_cusp (M : TwoLevels E r U C) (ka mu : Wt M.Ψ r) (u0 : C → Frame M.Ψ r → ℂ) (hu0 : u0 ∈ M.SS mu)
    (k h : U) {f : C → M.dom → ℂ} (hf : f ∈ M.cusp ka) :
    f * pb M k (M.res u0) * pb M h (M.res u0) ∈ M.cusp (ka + 2 • mu) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    have e : M.res F * pb M k (M.res u0) * pb M h (M.res u0) = M.res (F * M.pull k u0 * M.pull h u0) := rfl
    rw [e, two_smul, ← add_assoc]
    exact Submodule.subset_span ⟨_, GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ (GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ hF
      (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 k hu0)) (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 h hu0), rfl⟩
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul, add_mul]; exact add_mem hf hg
  | smul z f _ hf => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ z hf

end GlobalTheory.CuspEmb


open GlobalTheory.CuspEmb in
theorem GlobalTheory.CuspEmb.cusp_embReg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) →
    ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL
  classical
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  have hVHA : ∀ f ∈ M.cusp ka, f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M ka F hF
  have h2HA : ∀ f ∈ M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)), f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ F hF
  obtain ⟨a, hcoc, hform⟩ := GlobalTheory.T.exists_cocycle_pullbackRepresentation E r U C M ka ρ hρ (fun f hf => (hVHA f hf).2)
  obtain ⟨h1, hlaw⟩ := GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle E r U C M a hcoc
  let act : U →* (Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M)) :=
    { toFun := fun k => tw M (fun c => (a k⁻¹ c : ℂ)) k⁻¹
      map_one' := by
        show tw M (fun c => (a 1⁻¹ c : ℂ)) 1⁻¹ = 1
        rw [inv_one]
        exact h1
      map_mul' := fun g h => by
        simp only [mul_inv_rev]
        rw [← hlaw]
        rfl }
  let ut : HA M := ⟨M.res u0, GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ u0 hu0'⟩
  have hact : ∀ k, act k (Polynomial.C ut) = Polynomial.C (pbA M k⁻¹ ut) := fun k => tw_C M _ _ _
  have hactm : ∀ k (f : HA M), act k (Polynomial.monomial 1 f) =
      Polynomial.monomial 1 (cst M (fun c => (a k⁻¹ c : ℂ)) * pbA M k⁻¹ f) := fun k f => tw_monomial_one M _ _ _

  have hnz : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)).det ∈ nonZeroDivisors (Polynomial (HA M)) := by
    have e : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)) =
        (Polynomial.C : HA M →+* Polynomial (HA M)).mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) := by
      refine Matrix.ext fun h g => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hact, mul_inv_rev]
    rw [e, ← RingHom.map_det]
    refine GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors E r U C M _ fun c => ?_
    obtain ⟨x, hx, hne⟩ := hdet c
    refine ⟨⟨x, hx⟩, ?_⟩
    let φ : HA M →+* ℂ := ((Pi.evalRingHom _ (⟨x, hx⟩ : M.dom)).comp (Pi.evalRingHom _ c)).comp (HA M).val.toRingHom
    have e2 : ((Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det : C → M.dom → ℂ) c ⟨x, hx⟩ =
        φ (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det := rfl
    rw [e2, RingHom.map_det]
    have e3 : φ.mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) =
        ((Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c x).submatrix (Equiv.inv H) (Equiv.inv H)).transpose := by
      ext h g
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Equiv.inv_apply, mul_inv_rev]
      rfl
    rw [e3, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hne

  let V := deg1 M (M.cusp ka)
  let V2 := deg1 M (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)))
  let V1 : Submodule ℂ (Polynomial (HA M)) :=
    Submodule.span ℂ {p | ∃ x ∈ V, ∃ h : H, p = x * act h (Polynomial.C ut)}
  let e := deg1Equiv M (M.cusp ka) hVHA
  let e2 := deg1Equiv M _ h2HA
  haveI : Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := hR.2.1
  haveI : FiniteDimensional ℂ V2 := LinearEquiv.finiteDimensional e2
  let ρ' : Representation ℂ U V :=
    { toFun := fun k => e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  have hρ' : ∀ g x, ((ρ' g x : V) : Polynomial (HA M)) = act g x := by
    intro g x
    obtain ⟨f, rfl⟩ := e.surjective x
    have e1 : ρ' g (e f) = e (ρ g f) := by simp [ρ']
    rw [e1, deg1Equiv_coe, deg1Equiv_coe, hactm]
    congr 1
    apply Subtype.ext
    funext c x
    have := hform g⁻¹ f c x
    rw [inv_inv] at this
    exact this
  have hV1 : ∀ h : H, ∀ x ∈ V, x * act h (Polynomial.C ut) ∈ V1 := fun h x hx => Submodule.subset_span ⟨x, hx, h, rfl⟩
  have hactV : ∀ (k : U), ∀ x ∈ V, act k x ∈ V := fun k x hx => by
    have := hρ' k ⟨x, hx⟩
    rw [← this]
    exact (ρ' k ⟨x, hx⟩).2
  have hV1s : ∀ h : H, ∀ x ∈ V1, act h x ∈ V1 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      refine Submodule.subset_span ⟨act h y, hactV h y hy, h * k, ?_⟩
      rw [map_mul, Subgroup.coe_mul, map_mul act]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_smul]; exact Submodule.smul_mem _ z hx
  have hV2 : ∀ h : H, ∀ x ∈ V1, x * act h (Polynomial.C ut) ∈ V2 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      obtain ⟨f, hf, rfl⟩ := (mem_homogeneousExponentsOneBlock M _ y).1 hy
      rw [hact, hact, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
      refine (mem_homogeneousExponentsOneBlock M _ _).2 ⟨_, ?_, rfl⟩
      exact mul_pb_mem_cusp M ka _ u0 hu0' _ _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx
  obtain ⟨n, ⟨j, hj, hjeq⟩, hn⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant ℂ U (Polynomial (HA M)) act H (Polynomial.C ut) hnz V V1 V2 ρ' hρ' hV1
    hV1s hV2
  refine ⟨n, ⟨j ∘ₗ e.toLinearMap, hj.comp e.injective, fun h v i => ?_⟩, ?_⟩
  · have := hjeq h (e v) i
    have e1 : ρ' h (e v) = e (ρ h v) := by simp [ρ']
    rw [e1] at this
    exact this
  · rw [← e2.finrank_eq] at hn
    exact hn

end
