module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContragredientEqInvTransposeClass
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.DualClassTranspose

def equivComp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H) (e : ρ.Equiv σ) :
    Representation.Equiv (ρ.comp φ : Representation ℂ G V) (σ.comp φ : Representation ℂ G W) :=
  Representation.Equiv.mk' ⟨e.toLinearMap, fun g => e.toIntertwiningMap.isIntertwining' (φ g)⟩ e.symm
    (fun v => e.symm_apply_apply v) (fun w => e.apply_symm_apply w)

theorem invTranspose_eq (k : Type) [Field k] (n : ℕ) :
    GlobalTheory.TypeTame.invTranspose (R := k) n = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n k :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem dualCl_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ x y : IrrGL (k := k), DualCl x y ↔ ∃ (h1 : IsSmooth (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))) (h2 : Representation.IsIrreducible (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))), y = IrrGL.of (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1)) h1 h2 := by
  intro k _ _ _ _ hA x y
  have hinv : ∀ n (g : GL (Fin n) k), GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g :=
    fun n g => GlobalTheory.TypeTame.invTranspose_invTranspose n g
  have hsm : ∀ (z : IrrGL (k := k)), IsSmooth (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z v =>
    (z.2.rep.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose z.1)
  have hirr : ∀ (z : IrrGL (k := k)), Representation.IsIrreducible (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z =>
    GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, hinv _ g⟩) z.2.rep.irr

  have gk : ∀ {n : ℕ} (π : IrrRep (GL (Fin n) k)),
      Nonempty (Representation.Equiv (π.ρ.comp (GlobalTheory.TypeTame.invTranspose n) : Representation ℂ (GL (Fin n) k) π.V) (contra π.ρ)) := by
    intro n π
    rw [invTranspose_eq]
    exact GlobalTheory.GelfandKazhdan.equiv_contra k n π.V π.ρ (hA k n π.V π.ρ π.smooth π.irr) π.irr
  constructor
  · rintro ⟨n, π, π', rfl, rfl, ⟨e⟩⟩
    refine ⟨hsm _, hirr _, ?_⟩
    obtain ⟨f⟩ := gk π
    obtain ⟨r⟩ := IrrRep.nonempty_equiv_rep π

    have e2 : Representation.Equiv ((cls π).rep.comp (GlobalTheory.TypeTame.invTranspose (cls π).1) : Representation ℂ (GL (Fin n) k) _) π'.ρ :=
      (equivComp _ r).trans (f.trans e.symm)
    show (⟨n, π'.cl⟩ : IrrGL (k := k)) = _
    have : (⟨n, π'.cl⟩ : IrrGL (k := k)) = IrrGL.of π'.ρ π'.smooth π'.irr := rfl
    rw [this]
    exact IrrGL.of_eq_of.2 ⟨e2.symm⟩
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨x.1, x.2.rep, ⟨_, x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1), h1, h2⟩, ?_, rfl, ?_⟩
    · exact (congrArg (Sigma.mk x.1) x.2.cl_rep).symm
    · exact gk x.2.rep

end GlobalTheory.DualClassTranspose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetChar
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeTwist

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.TypeTame.invTranspose n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [GlobalTheory.TypeTame.invTranspose, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem nabs_inv (x : kˣ) : GlobalTheory.SplitWeil.nabs k x⁻¹ = (GlobalTheory.SplitWeil.nabs k x)⁻¹ := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem absPow_det_invTranspose (n : ℕ) (s : ℂ) (g : GL (Fin n) k) :
    detChar (Fin n) (absPow k s) (GlobalTheory.TypeTame.invTranspose n g) =
      detChar (Fin n) (absPow k (-s)) g := by
  ext
  have hp := GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g)
  simp only [detChar, absPow, MonoidHom.comp_apply, det_invTranspose]
  simp [nabs_inv, Complex.cpow_neg]

theorem twist_comp_invTranspose (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ) :
    (GlobalTheory.SmGL.twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n) =
      GlobalTheory.SmGL.twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))) := by
  ext g v
  simp only [MonoidHom.comp_apply, GlobalTheory.SmGL.twist, MonoidHom.coe_mk, OneHom.coe_mk, absPow_det_invTranspose]

end GlobalTheory.InvTransposeTwist

theorem GlobalTheory.InvTransposeTwist.main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (GlobalTheory.SmGL.twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  intro k _ _ _ _ n V _ _ π s
  rw [GlobalTheory.InvTransposeTwist.twist_comp_invTranspose]
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => rfl)⟩
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExistsClassIsLSeg
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in
theorem PositivityTheory.Exh.exists_class_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) : ∃ x : IrrGL (k := k), IsLSeg Δ x.rep := by
  obtain ⟨π, hd, hc⟩ := PositivityTheory.Exh.lSegExists k Δ
  refine ⟨⟨Δ.deg, Quotient.mk (IrrRep.setoid _) π⟩, ?_⟩
  obtain ⟨e⟩ : Nonempty ((Quotient.mk (IrrRep.setoid _) π).out.ρ.Equiv π.ρ) :=
    Quotient.mk_out (s := IrrRep.setoid _) π
  exact ⟨hd, IsCosocle.of_equiv hc e.symm (Representation.Equiv.refl _)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleComp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.DualityMap

open GlobalTheory.TypeTame

section Comp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def compEquiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (s : H →* G) :
    Representation.Equiv (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (s g)

end Comp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isSmooth_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : IsSmooth π) :
    IsSmooth (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  fun v => (h v).preimage (continuous_invTranspose n)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isIrreducible_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  GlobalTheory.CosocleComp.isIrreducible_comp (fun g => ⟨_, invTranspose_invTranspose n g⟩) h

def dual (x : IrrGL (k := k)) : IrrGL (k := k) :=
  IrrGL.of (x.rep.comp (invTranspose x.1)) (isSmooth_comp x.2.rep.smooth) (isIrreducible_comp x.2.rep.irr)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem dual_of {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    dual (IrrGL.of π hs hi) = IrrGL.of (π.comp (invTranspose n)) (isSmooth_comp hs) (isIrreducible_comp hi) :=
  IrrGL.of_eq_of.2 ⟨compEquiv (IrrGL.equivOf π hs hi).symm (invTranspose n)⟩


omit [IsNonarchimedeanLocalField k] in
theorem dual_dual (x : IrrGL (k := k)) : dual (dual x) = x := by
  refine (dual_of _ _ _).trans (Eq.trans (IrrGL.of_eq_of.2 ⟨?_⟩) (IrrGL.of_rep x))
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_
  ext v
  show x.rep (invTranspose x.1 (invTranspose x.1 g)) v = x.rep g v
  rw [invTranspose_invTranspose]

end GlobalTheory.DualityMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecedesOfSegDualPrecedes
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocLanglands

theorem precedes_of_segDual_precedes :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) →
      (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) →
      (∀ x, (D x).1 = x.1) → ∀ Δ Γ Δ' Γ' : Segment k, SegDual Δ Δ' → SegDual Γ Γ' → Γ'.Precedes Δ' → Δ.Precedes Γ := by
  intro k _ _ _ _ D hD hDD hnu _ _ Δ Γ Δ' Γ' ⟨l1, d1⟩ ⟨l2, d2⟩ H
  obtain ⟨j, h0, h1, h2, e⟩ := Segment.precedes_iff.1 H
  rw [(hD _ _).1 d1, (hD _ _).1 d2] at e
  have e' := congrArg D e
  rw [hnu (D _), hDD, hDD, IrrGL.nu_nu] at e'
  rw [l1] at h2
  rw [l2] at h1 h2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j + Δ.len = Γ.len + i := ⟨j + Δ.len - Γ.len, by omega⟩
  refine Segment.precedes_iff.2 ⟨i, by omega, by omega, by omega, ?_⟩
  have hc : (j : ℂ) + Δ.len = Γ.len + i := by exact_mod_cast hi
  have e2 := congrArg (fun x => IrrGL.nu x (-((Γ.len : ℂ) - 1 + -(j : ℂ)))) e'
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at e2
  rw [← e2]
  congr 1
  linear_combination hc

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SegDualExistsTerms
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.SegDualProof

theorem segDual_exists_terms : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) → (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) → (∀ x, (D x).1 = x.1) → ∀ Δ : Segment k, (∃ Δ', SegDual Δ Δ') ∧ ∀ Δ', SegDual Δ Δ' → Δ'.len = Δ.len ∧ ∀ a : ℕ, a < Δ.len → Δ'.first.nu (a : ℂ) = D (Δ.first.nu ((Δ.len : ℂ) - 1 - a)) := by
  intro k _ _ _ _ D hD _ hnu hcusp _ Δ
  have hρ : (D (Δ.first.nu ((Δ.len : ℂ) - 1))).IsCusp := hcusp _ (Δ.isCusp_first.nu _)
  refine ⟨⟨Segment.ofFirst _ hρ Δ.len Δ.len_pos, rfl, (hD _ _).2 rfl⟩, ?_⟩
  rintro Δ' ⟨hl, hd⟩
  refine ⟨hl, fun a _ => ?_⟩
  rw [(hD _ _).1 hd]
  have h1 := hnu (Δ.first.nu ((Δ.len : ℂ) - 1)) (-(a : ℂ))
  rw [neg_neg, IrrGL.nu_nu, ← sub_eq_add_neg] at h1
  exact h1.symm

end GlobalTheory.SegDualProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocGL.LExist

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ Δ : Segment k, ∃ x : IrrGL (k := k), IsLSeg Δ x.rep) →
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep := by
  intro k _ _ _ _ _ hS hL 𝔪
  obtain ⟨Δ, hΔ⟩ := ((precedes_and_orderedForms k).1.2.2) 𝔪
  choose y hy using hL
  let x : Fin 𝔪.card → IrrGL (k := k) := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := hS k 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

end GlobalTheory.LocGL.LExist
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.MultiProdCompInvTranspose
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult GlobalTheory.TypeTame

noncomputable section

namespace PositivityTheory.Pf1.LDual2

theorem multiProd_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty (Representation.Equiv ((multiProd e π).comp (invTranspose n))
      (multiProd e' fun a => ((π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) :
        Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  open GlobalTheory.InvTransposeProd in
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (GlobalTheory.InvTransposeProd.revPlace e)),
      ((twist (GlobalTheory.InvTransposeProd.revRep π') (deltaHalf k _)).comp
        (leviProj k (GlobalTheory.InvTransposeProd.revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twist_apply, twist_apply,
      GlobalTheory.InvTransposeProd.deltaHalf_revPlace e q hq, hπ', GlobalTheory.InvTransposeProd.revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (GlobalTheory.InvTransposeProd.revPlace e) (GlobalTheory.InvTransposeProd.revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (GlobalTheory.InvTransposeProd.revPlace e)) (Q := parab k e)
      (σ := (twist (GlobalTheory.InvTransposeProd.revRep π') (deltaHalf k _)).comp
        (leviProj k (GlobalTheory.InvTransposeProd.revPlace e)))
      (τ := (twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, GlobalTheory.InvTransposeProd.mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (GlobalTheory.InvTransposeProd.revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, GlobalTheory.InvTransposeProd.mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, GlobalTheory.InvTransposeProd.mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.PlacingProd.multiProd_placing_equiv k h n (fun a => d (Fin.rev a))
    (GlobalTheory.InvTransposeProd.revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (GlobalTheory.InvTransposeProd.revPlace e) (GlobalTheory.InvTransposeProd.revRepEquiv π')).trans B)⟩

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dual_nu (x : IrrGL (k := k)) (s : ℂ) : GlobalTheory.DualityMap.dual (x.nu s) = (GlobalTheory.DualityMap.dual x).nu (-s) := by
  obtain ⟨e⟩ := GlobalTheory.InvTransposeTwist.main k x.1 _ x.rep s
  refine Eq.trans ?_ (IrrGL.tw_of _ _ _ _ _).symm
  exact IrrGL.of_eq_of.2
    ⟨(GlobalTheory.DualityMap.compEquiv (IrrGL.twEquiv x _ (isSmoothChar_absPow s)).symm (invTranspose x.1)).trans e⟩

theorem isCusp_dual (x : IrrGL (k := k)) (h : x.IsCusp) : (GlobalTheory.DualityMap.dual x).IsCusp :=
  ⟨h.1, isCuspidal_of_equiv (IrrGL.equivOf _ _ _)
    (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose k x.1 _ x.rep h.2)⟩

end Dual

theorem dualMap (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : ∃ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) ∧
      (∀ x, D (D x) = x) ∧ (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) ∧
      (∀ x, x.IsCusp → (D x).IsCusp) ∧ (∀ x, (D x).1 = x.1) :=
  ⟨GlobalTheory.DualityMap.dual, fun x y => (GlobalTheory.DualClassTranspose.dualCl_iff k hA x y).trans
    ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, _, h⟩⟩, GlobalTheory.DualityMap.dual_dual, dual_nu, isCusp_dual, fun _ => rfl⟩

section Seg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem prodIrr_cast {h h' N : ℕ} (e : h = h') (x : Fin h' → IrrGL (k := k)) (hx : ∑ a, (x (Fin.cast e a)).1 = N)
    (hy : ∑ a, (x a).1 = N) : Nonempty ((prodIrr (fun a => x (Fin.cast e a)) hx).Equiv (prodIrr x hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem isLSeg_dual (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (D : IrrGL (k := k) → IrrGL (k := k))
    (hD : ∀ x y, DualCl x y ↔ y = D x) (hDD : ∀ x, D (D x) = x)
    (hnu : ∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) (hcusp : ∀ x, x.IsCusp → (D x).IsCusp)
    (hdeg : ∀ x, (D x).1 = x.1) (Δ Δ' : Segment k) (x : IrrGL (k := k)) (hx : IsLSeg Δ x.rep) (hΔ : SegDual Δ Δ') :
    IsLSeg Δ' (D x).rep := by
  obtain ⟨hlen, hterm⟩ := (GlobalTheory.SegDualProof.segDual_exists_terms k D hD hDD hnu hcusp hdeg Δ).2 Δ' hΔ
  have key : ∀ w : IrrGL (k := k), ∃ (h1 : IsSmooth (w.rep.comp (invTranspose w.1)))
      (h2 : Representation.IsIrreducible (w.rep.comp (invTranspose w.1))),
      D w = IrrGL.of (w.rep.comp (invTranspose w.1)) h1 h2 :=
    fun w => (GlobalTheory.DualClassTranspose.dualCl_iff k hA w (D w)).1 ((hD w _).2 rfl)
  choose s1 s2 hs using key
  obtain ⟨hd, hcos⟩ := hx
  have hd' : ∑ a, (Δ.term (Fin.rev a)).1 = x.1 := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (Δ.term a).1
  have hsurj : Function.Surjective (invTranspose (R := k) x.1) :=
    fun g => ⟨_, invTranspose_invTranspose _ g⟩
  have c1 := GlobalTheory.CosocleComp.isCosocle_comp _ _ _ _ _ _ (invTranspose (R := k) x.1) hsurj hcos
  obtain ⟨e1⟩ := multiProd_comp_invTranspose k Δ.len x.1 (fun a => (Δ.term a).1)
    (stdBlocks (fun a => (Δ.term a).1) hd) (stdBlocks (fun a => (Δ.term (Fin.rev a)).1) hd') _
    (fun a => (Δ.term a).rep)
  have e2 := prodIrrEquiv hd' (fun a => (Δ.term (Fin.rev a)).rep.comp (invTranspose (Δ.term (Fin.rev a)).1))
    (fun a => s1 _) (fun a => s2 _)
  have hfam : (fun a : Fin Δ.len => IrrGL.of ((Δ.term (Fin.rev a)).rep.comp (invTranspose (Δ.term (Fin.rev a)).1))
      (s1 _) (s2 _)) = fun a => Δ'.term (Fin.cast hlen.symm a) := by
    funext a
    rw [← hs]
    show D (Δ.first.nu (((Fin.rev a : Fin Δ.len) : ℕ) : ℂ)) = Δ'.first.nu (((a : ℕ)) : ℂ)
    rw [hterm a a.2, Fin.val_rev, Nat.cast_sub (by omega : (a : ℕ) + 1 ≤ Δ.len)]
    push_cast
    ring_nf
  have hd2 : ∑ a, (Δ'.term (Fin.cast hlen.symm a)).1 = x.1 := by
    rw [← hd']
    exact Finset.sum_congr rfl fun a _ => (congrArg Sigma.fst (congrFun hfam a)).symm
  have hd0 : ∑ a, (Δ'.term a).1 = x.1 := by
    rw [← hd2]
    exact (Equiv.sum_comp (finCongr hlen.symm) fun a => (Δ'.term a).1).symm
  obtain ⟨E3⟩ := prodIrr_congr hfam hd' hd2
  obtain ⟨E4⟩ := prodIrr_cast hlen.symm Δ'.term hd2 hd0
  rw [hs x]
  exact ⟨hd0, c1.of_equiv (IrrGL.equivOf _ (s1 x) (s2 x)) (e1.trans (e2.trans (E3.trans E4)))⟩

end Seg

theorem isL_dual_of_admissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (l : List (Segment k)) (x y : IrrGL (k := k)),
    IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
    ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep := by
  intro k _ _ _ _ hA l x y hL hxy
  obtain ⟨D, hD, hDD, hnu, hcusp, hdeg⟩ := dualMap k hA
  choose f hf using fun Δ : Segment k => (GlobalTheory.SegDualProof.segDual_exists_terms k D hD hDD hnu hcusp hdeg Δ).1
  refine ⟨l.map f, ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun Δ _ => hf Δ
  obtain ⟨h, z, hd, ⟨Δ, ⟨hΔ, hord⟩, hz⟩, hcos⟩ := hL
  obtain ⟨h1, h2, rfl⟩ := (GlobalTheory.DualClassTranspose.dualCl_iff k hA x y).1 hxy
  have key : ∀ w : IrrGL (k := k), ∃ (h1 : IsSmooth (w.rep.comp (invTranspose w.1)))
      (h2 : Representation.IsIrreducible (w.rep.comp (invTranspose w.1))),
      D w = IrrGL.of (w.rep.comp (invTranspose w.1)) h1 h2 :=
    fun w => (GlobalTheory.DualClassTranspose.dualCl_iff k hA w (D w)).1 ((hD w _).2 rfl)
  choose s1 s2 hs using key
  have hd' : ∑ a, (z (Fin.rev a)).1 = x.1 := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (z a).1
  have hsurj : Function.Surjective (invTranspose (R := k) x.1) :=
    fun g => ⟨_, invTranspose_invTranspose _ g⟩
  have c1 := GlobalTheory.CosocleComp.isCosocle_comp _ _ _ _ _ _ (invTranspose (R := k) x.1) hsurj hcos
  obtain ⟨e1⟩ := multiProd_comp_invTranspose k h x.1 (fun a => (z a).1) (stdBlocks (fun a => (z a).1) hd)
    (stdBlocks (fun a => (z (Fin.rev a)).1) hd') _ (fun a => (z a).rep)
  have e2 := prodIrrEquiv hd' (fun a => (z (Fin.rev a)).rep.comp (invTranspose (z (Fin.rev a)).1))
    (fun a => s1 _) (fun a => s2 _)
  refine ⟨h, fun a => IrrGL.of ((z (Fin.rev a)).rep.comp (invTranspose (z (Fin.rev a)).1)) (s1 _) (s2 _),
    hd', ⟨fun a => f (Δ (Fin.rev a)), ⟨?_, fun i j hij hp => ?_⟩, fun a => ?_⟩,
    c1.of_equiv (IrrGL.equivOf _ h1 h2) (e1.trans e2)⟩
  · rw [← Multiset.map_coe, ← hΔ, Multiset.map_map]
    conv_rhs => rw [← Finset.map_univ_equiv (Fin.revPerm (n := h)), Finset.map_val, Multiset.map_map]
    rfl
  · exact hord _ _ (Fin.rev_lt_rev.2 hij)
      (GlobalTheory.LocLanglands.precedes_of_segDual_precedes k D hD hDD hnu hcusp hdeg _ _ _ _ (hf _) (hf _) hp)
  · have := isLSeg_dual hA D hD hDD hnu hcusp hdeg _ _ _ (hz (Fin.rev a)) (hf _)
    rw [hs] at this
    exact this

theorem langlandsDataDualGL_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k], ∀ (l : List (Segment k)) (x y : IrrGL (k := k)),
    IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
    ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep :=
  fun k _ _ _ _ _ => isL_dual_of_admissible k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top

end PositivityTheory.Pf1.LDual2

end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace PositivityTheory.Pf1.LocalLanglands.LDual

theorem lExists_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep :=
  fun k _ _ _ _ _ => GlobalTheory.LocGL.LExist.main k hS (PositivityTheory.Exh.exists_class_isLSeg k)

theorem langlandsDataDualGL_of_clauses (hS : GlobalTheory.Published.StandardCosocleGL)
    (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (l : List (Segment k)) (x y : IrrGL (k := k)), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
        ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep) :
    GlobalTheory.Published.LanglandsDataDualGL :=
  fun k _ _ _ _ _ => ⟨lExists_of_cosocle hS k, hD k⟩

theorem langlandsDataDualGL_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) : GlobalTheory.Published.LanglandsDataDualGL :=
  langlandsDataDualGL_of_clauses hS PositivityTheory.Pf1.LDual2.langlandsDataDualGL_dual

end PositivityTheory.Pf1.LocalLanglands.LDual
