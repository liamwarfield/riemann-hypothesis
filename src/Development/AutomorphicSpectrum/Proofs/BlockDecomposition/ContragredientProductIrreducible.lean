module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

section Family

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
  [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)]
  [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_pi_subset
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    (U : Set (∀ a, Γ a)) (hU : U ∈ nhds (1 : ∀ a, Γ a)) :
    ∃ H : ∀ a, Subgroup (Γ a), (∀ a, IsOpen (H a : Set (Γ a))) ∧ (∀ a, IsCompact (H a : Set (Γ a))) ∧
      ((Subgroup.pi Set.univ H : Subgroup (∀ a, Γ a)) : Set (∀ a, Γ a)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose H hHo hHc hHs using fun a => hG a (t a) (ht a)
  refine ⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩
  exact (Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)

theorem pi_compactOpen_basis
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U) :
    ∀ U ∈ nhds (1 : ∀ a, Γ a), ∃ K : Subgroup (∀ a, Γ a), IsOpen (K : Set (∀ a, Γ a)) ∧
      IsCompact (K : Set (∀ a, Γ a)) ∧ (K : Set (∀ a, Γ a)) ⊆ U := by
  intro U hU
  obtain ⟨H, hHo, hHc, hsub⟩ := exists_pi_subset hG U hU
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩
  · show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isOpen_set_pi Set.finite_univ fun a _ => hHo a
  · show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isCompact_univ_pi fun a => hHc a

theorem isAdmissible_piTensor [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩
  obtain ⟨H, h1, h2, h3⟩ := exists_pi_subset hG _ (ho.mem_nhds (one_mem K))
  haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)
  let M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype
  have hle : fixed (piTensor ρ) K ≤ LinearMap.range M := by
    intro w hw
    have hs := GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh =>
      GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)
    refine Submodule.span_le.2 ?_ hs
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩
  exact Submodule.finiteDimensional_of_le hle

def pairForm (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] ℂ :=
  ((PiTensorProduct.dualDistrib (R := ℂ) (M := X)) ∘ₗ
    PiTensorProduct.map fun a => (smoothPart (ρ a).dual).subtype).flip

theorem pairForm_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (v : ∀ a, X a)
    (l : ∀ a, smoothPart (ρ a).dual) :
    pairForm ρ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ l) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]

theorem pairForm_invariant (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a)
    (s : ⨂[ℂ] a, X a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairForm ρ (piTensor ρ g s) (piTensor (fun a => contra (ρ a)) g t) = pairForm ρ s t := by
  have hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a)) := by
    intro v
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  have hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) =
      PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a)) := by
    intro l
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ l) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  refine PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)
  · refine PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, LinearMap.smul_apply]
      rw [hpt, hpt', pairForm_tprod, pairForm_tprod]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · simp only [map_add (f := _), hx, hy]
  · simp only [map_add (f := _), LinearMap.add_apply, hx, hy]

theorem nonempty_equiv_piTensor_contra [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a))
    (hi : ∀ a, (ρ a).IsIrreducible) :
    Nonempty ((piTensor fun a => contra (ρ a)).Equiv (contra (piTensor ρ))) := by
  have hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a)) := fun a => by
    obtain ⟨K, h1, h2, -⟩ := hG a Set.univ Filter.univ_mem
    exact ⟨K, h1, h2⟩
  choose K0 hK1 hK2 using hK
  have hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)
  have hci : ∀ a, (contra (ρ a)).IsIrreducible := fun a =>
    GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)
  have hca : ∀ a, IsAdmissible (contra (ρ a)) := fun a =>
    GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)
  have hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual,
      (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)
  have hI : (piTensor ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur
  have hI' : (piTensor fun a => contra (ρ a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur
  have hCI : (contra (piTensor ρ)).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI
  have hB0 : pairForm ρ ≠ 0 := by
    have hne : ∀ a, ∃ v : X a, v ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
      apply Subrepresentation.ext
      ext x
      rw [h x]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    choose v hv using hne
    choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)
    intro h0
    have h1 := pairForm_tprod ρ v l
    rw [h0] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)
  exact ⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a))
    (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩

end Family

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem contra_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible :=
  GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1)
    (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr

theorem contra_piTensor_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    Nonempty ((piTensor fun a => contra (x a).rep).Equiv (contra (piTensor fun a => (x a).rep))) := by
  haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group
  exact nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k)
    (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1)
    (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)
    fun a => (x a).2.rep.irr

theorem parInd_equiv_contra {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) V} {ρ : Representation ℂ (Levi k m) W}
    (hρ : IsSmooth ρ) (φ : Nonempty (σ.Equiv (contra ρ))) :
    Nonempty ((parInd e σ).Equiv (contra (parInd e ρ))) := by
  obtain ⟨φ⟩ := φ
  obtain ⟨ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ
  exact ⟨(parIndEquiv e φ).trans ψ⟩

theorem contra_prodIrr_multiProd (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks (fun a => (x a).1) hd) fun a => contra (x a).rep).Equiv
      (contra (prodIrr x hd))) :=
  parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)

theorem contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N,
      Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  intro k _ _ _ _ hA h N x hd
  have hci := fun a => contra_rep_isIrreducible hA (x a)
  have hy : (fun a => dualCl (x a)) =
      fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a) :=
    funext fun a => dif_pos (hci a)
  have key : ∀ y : Fin h → IrrGL (k := k),
      y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) →
      ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := by
    rintro _ rfl
    exact ⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans
      (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩
  exact key _ hy

end GlobalTheory.CompanionTheory.ContraProd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_product_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (GlobalTheory.SmGL.jac e π) = jhMult σ (GlobalTheory.SmGL.jac e π₁) + jhMult σ (GlobalTheory.SmGL.jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e T.toRepresentation))
    (hjm : jhMult ρ (GlobalTheory.SmGL.jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (GlobalTheory.SmGL.jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOneStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        have h := isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))
        have hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k)) := by
          ext A
          show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)
          constructor
          · intro hA i _ j _
            exact hA i j
          · intro hA i j
            exact hA i (Set.mem_univ i) j (Set.mem_univ j)
        rw [hSe]
        exact h
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eval_map (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (g : GL n k) (v : V) :
    (f (τ g v)).1.1 1 = (f v).1.1 g := by
  have hf : f (τ g v) = parInd e ρ g (f v) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (f.isIntertwining' g) v
  rw [hf, parInd_apply, one_mul]

theorem eval_unipRad (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (φ : IndSp e ρ)
    (u : unipRad k e) : φ.1.1 (u : GL n k) = φ.1.1 1 := by
  have hp : (u : GL n k) ∈ parab k e := unipRad_le_parab k e u.2
  have hl : leviProj k e ⟨u, hp⟩ = 1 := (coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2
  have hφ := parInd_law e ρ φ ⟨u, hp⟩ 1
  rw [hl] at hφ
  simpa using hφ

def evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : V →ₗ[ℂ] W where
  toFun v := (f v).1.1 1
  map_add' v w := by simp
  map_smul' c v := by simp

theorem twKer_le_ker_evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V}
    {ρ : Representation ℂ (Levi k m) W} (f : τ.IntertwiningMap (parInd e ρ)) :
    twKer τ (unipRad k e) 1 ≤ LinearMap.ker (evalOne e f) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  have hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v := by
    show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1
    rw [eval_map, eval_unipRad e (f v) u]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply,
    Units.val_one, one_smul, sub_self]

def frobMap (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : (GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ where
  toLinearMap := (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hmem : leviEmb k e g ∈ parab k e := by
      refine mem_parab_iff.2 fun a b i j hab => ?_
      simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
    have hproj : leviProj k e ⟨leviEmb k e g, hmem⟩ = g := by
      funext a
      ext i j
      simp [leviEmb]
    have h := parInd_law e ρ (f v) ⟨leviEmb k e g, hmem⟩ 1
    rw [mul_one, hproj] at h
    have h2 : evalOne e f (τ (leviEmb k e g) v) =
        (deltaHalf k m g : ℂ) • ρ g (evalOne e f v) := (eval_map e f _ v).trans h
    show (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
        (GlobalTheory.SmGL.jac e τ g (Submodule.Quotient.mk v)) = ρ g (evalOne e f v)
    rw [jac_mk, map_smul]
    change (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • evalOne e f (τ (leviEmb k e g) v) = _
    rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem frobMap_mk (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (v : V) :
    frobMap e f (Submodule.Quotient.mk v) = (f v).1.1 1 := rfl

theorem frobMap_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (hf : ∃ v, f v ≠ 0) : ∃ y, frobMap e f y ≠ 0 := by
  obtain ⟨v, hv⟩ := hf
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h1 := frobMap_mk e f (τ g v)
  rw [hcon, eval_map] at h1
  simpa using h1.symm

theorem surjective_of_ne_zero {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : ∃ y, f y ≠ 0) : Function.Surjective f := by
  haveI := hσ
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · obtain ⟨y, hy⟩ := hf
    exact (hy (by simp [hz])).elim

theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  let f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := f
  obtain ⟨y, hy⟩ := frobMap_ne_zero _ f' hf
  have hs := surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩
  have hq := jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)
  exact Order.one_le_iff_ne_zero.2 hq

end GlobalTheory.CompanionTheory.FrobJm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  first | exact @GlobalTheory.CompanionTheory.FrobJm.one_le_jm | exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm | (intros; apply GlobalTheory.CompanionTheory.FrobJm.one_le_jm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Bk (n : Fin (m + 1) → ℕ) : Fin (m + 1) → Type := fun c => Fin (n c + 1)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev prB (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) : MP ℤ m n ⟶ PSpace ℤ (n k) := pr ℤ m n k

abbrev blockChart (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) (i : Bk n k) : (MP ℤ m n).Opens :=
  prB n k ⁻¹ᵁ chart ℤ (n k) i

def mchart (c : ∀ k, Bk n k) : (MP ℤ m n).Opens :=
  ⟨⋂ k, (blockChart n k (c k) : Set (MP ℤ m n)),
    isOpen_iInter_of_finite fun k => (blockChart n k (c k)).isOpen⟩

theorem mchart_le (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mchart c ≤ blockChart n k (c k) :=
  fun _ hx => Set.mem_iInter.1 hx k

def blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) : Γ(MP ℤ m n, W)ˣ :=
  res h (pullU (prB n k) _ (ratioUnit _ i j inf_le_left inf_le_right))

def ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : Bk n k :=
  (GlobalTheory.ProjSpace.exists_mem_chart ℤ (n k) (prB n k x)).choose

theorem mem_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : x ∈ blockChart n k (ptChart x k) :=
  (GlobalTheory.ProjSpace.exists_mem_chart ℤ (n k) (prB n k x)).choose_spec

def ptCoord (x : MP ℤ m n) (p : Σ k, Bk n k) : (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (blockChart n p.1 (ptChart x p.1)) x (mem_ptChart x p.1)).hom
    (pullRatio (prB n p.1) _ (ptChart x p.1) le_rfl p.2)

def ptIdeal (x : MP ℤ m n) : Ideal (Geo.MRing (Bk n)) := Geo.mCoordIdeal (ptCoord x)

def IsUnder (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) : Prop :=
  ∀ (k : Fin (m + 1)) (i : Bk n k), (y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0) ∧
    ∀ j : Bk n k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) →
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y = z ⟨k, j⟩ / z ⟨k, i⟩

def IsHermRep (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) : Prop :=
  ∃ u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
    ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
      A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
        ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
          Real.exp ((M.φ σ₀).φ i y / 2)

abbrev consN (n' : ℕ) (n : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ := Fin.cons n' n

def sv (n' : ℕ) (n : Fin (m + 1) → ℕ) : (Σ k, Bk n k) → Σ k', Bk (consN n' n) k' :=
  fun p => ⟨p.1.succ, p.2⟩

theorem isBlockMap_sv (n' : ℕ) (n : Fin (m + 1) → ℕ) :
    IsBlockMap (ι := Bk n) (ι' := Bk (consN n' n)) Fin.succ (sv n' n) := by
  refine ⟨Fin.succ_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', j⟩ h
    have hk : k.succ = k'.succ := congrArg Sigma.fst h
    obtain rfl : k = k' := Fin.succ_injective _ hk
    have h' : (⟨k.succ, i⟩ : Σ k', Bk (consN n' n) k') = ⟨k.succ, j⟩ := h
    have hij : i = j := sigma_mk_injective (β := Bk (consN n' n)) (i := k.succ) h'
    rw [hij]
  · rintro ⟨k', j⟩ ⟨k, rfl⟩
    exact ⟨⟨k, j⟩, rfl⟩

def pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) : Geo.HermLine (Bk (consN n' n)) where
  a := pullDeg Fin.succ A.a
  h z := A.h fun p => z (sv n' n p)
  pos z hz := A.pos _ fun k => hz k.succ
  smul c z hc := by
    have e := A.smul (fun k => c k.succ) (fun p => z (sv n' n p)) fun k => hc k.succ
    refine e.trans ?_
    have h0 : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a 0 = 0 := by
      unfold pullDeg
      rw [Function.extend_apply']
      · rfl
      · rintro ⟨k, hk⟩
        exact Fin.succ_ne_zero k hk
    have hs (k : Fin (m + 1)) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a k.succ = A.a k :=
      (Fin.succ_injective _).extend_apply _ _ _
    rw [Fin.prod_univ_succ (fun k' => ‖c k'‖ ^ pullDeg Fin.succ A.a k'), h0, zpow_zero, one_mul]
    simp only [hs]

theorem isPullHerm_pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) :
    IsPullHerm Fin.succ (sv n' n) A (pullLine n' A) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwEntries

variable {E : Type} [Field E] [NumberField E]

theorem rel_le_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem rel_lt_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem mem_KGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, h2 i j⟩,
      hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem mem_KO_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) ↔
      (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) →
      ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (rel_le_one_iff w _).1 (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    let O := ValuativeRel.valuation (w.adicCompletion E) |>.integer
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, (rel_le_one_iff w _).2 (h1 i j)⟩,
      Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, (rel_le_one_iff w _).2 (h2 i j)⟩, hi ?_, hi ?_⟩,
      Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem iwGL_KGL_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  intro E _ _ _ w n g
  refine ⟨?_, mem_KGL_iff w n g⟩
  show g ∈ GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n) ↔ _
  rw [GlobalTheory.SmGL.mem_iwahori, mem_KO_iff, and_assoc]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun i j _ => rel_lt_one_iff w _))

end GlobalTheory.CompanionTheory.IwEntries
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteriaStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_and_maximal_compact_criteria : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  first | exact @GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | exact GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | (intros; apply GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdInj

theorem prod₂_map_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (f : σ.IntertwiningMap σ'), Function.Injective f → ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ), Function.Injective F := by
  intro k _ _ _ _ r t U U' W _ _ _ _ _ _ σ σ' ρ f hf
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.ProdInj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLattice
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isLat_lam_of_matrix (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K) : IsLat (lam c) := by
  have hL : IsLat (intVec K m) := isLat_intVec m
  refine ⟨Submodule.FG.sup hL.1 (Submodule.FG.map _ hL.1), ?_⟩
  rw [eq_top_iff, ← hL.2]
  exact Submodule.span_mono (fun v hv => (le_sup_left : intVec K m ≤ lam c) hv)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_is_lattice : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), IsLat (lam c) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix <;> assumption)
end
end
