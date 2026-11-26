module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsJacQuot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

set_option synthInstance.maxHeartbeats 400000

section

open GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.CompanionTheory.Hypotheses₂.TD

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem cellone_offdiag (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (x : Fin 2 → IrrGL (k := k))
    (H : ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = (x 1).1), 0 < (q 0).1 → jm q hq (x 1).rep ≠ 0 →
      ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = (x 0).1), jhMult (x 0).rep (prodIrr ![p, q 0] hc) = 0)
    {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (x j).1)
    (h0 : jhMult (piTensor fun i => (x i).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    b 1 0 = 0 := by
  have hτ : (piTensor fun i => (x i).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun i => (x i).2.rep
  have hτs : IsSmooth (piTensor fun i => (x i).rep) := isSmooth_piTensor fun i => (x i).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  by_contra hb
  let c : Fin 2 → Fin 2 → IrrGL (k := k) := fun i j => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hq : ∑ j, b 1 j = (x 1).1 := by simpa using Fintype.card_congr (f 1)
  have hd : ∑ i, b i 0 = (x 0).1 := by simpa using Fintype.card_congr (g 0)
  have hjm : jm (c 1) hq (x 1).rep ≠ 0 := by
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (f 1) (stdBlocks (fun j => b 1 j) hq) _).2
      (x 1).rep
    let θ := (piTensorEquiv fun j => IrrGL.equivOf (s 1 j).ρ (s 1 j).smooth (s 1 j).irr).symm
    exact jhMult_ne_zero_iff.2 ((IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans
      ((hrow 1).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)))
  have hsub : IsSubquotient (x 0).rep (prodIrr (fun i => c i 0) hd) := by
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) 0 (x 0).2.rep.irr
      ((isSubquotient_comp_mulSingle (fun i => (x i).rep) (fun i => (x i).2.rep.irr) 0).trans
        (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g 0) (stdBlocks (fun i => b i 0) hd) _).1
      (piTensor fun i => (s i 0).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i 0).ρ) (fun i => (s i 0).smooth) fun i => (s i 0).irr)
    exact h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  have key : ∀ (z : Fin 2 → IrrGL (k := k)) (hz : ∑ a, (z a).1 = (x 0).1), z = ![c 0 0, c 1 0] →
      jhMult (x 0).rep (prodIrr z hz) = 0 := by
    rintro _ hz rfl
    exact H (c 1) hq (Nat.pos_of_ne_zero hb) hjm (c 0 0) hz
  refine jhMult_ne_zero_iff.2 hsub (key _ hd (funext fun i => ?_))
  fin_cases i <;> rfl

set_option maxHeartbeats 1000000 in
private theorem jacquet_multiplicity_single_cell (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (x : Fin 2 → IrrGL (k := k))
    (H : ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = (x 1).1), 0 < (q 0).1 → jm q hq (x 1).rep ≠ 0 →
      ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = (x 0).1), jhMult (x 0).rep (prodIrr ![p, q 0] hc) = 0)
    {N : ℕ} (e : (Σ i, Fin (x i).1) ≃ Fin N) :
    jhMult (piTensor fun i => (x i).rep) (jac e (multiProd e fun i => (x i).rep)) = 1 := by
  classical
  have hτ : (piTensor fun i => (x i).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun i => (x i).2.rep
  let M := fun i : Fin 2 => Fin (x i).1
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then (x i).1 else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hρ : IsSmooth (piTensor fun i => (x i).rep) := isSmooth_piTensor fun i => (x i).2.rep.smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have h1 := (hG k).1.jhMult_eq (m := M) (m' := M) e e hρ f g hτ
  refine (show jhMult _ (jac e (multiProd e fun i => (x i).rep)) = _ from h1).trans ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult (piTensor fun i => (x i).rep) (cellFunctor f' g' (piTensor fun i => (x i).rep)) = 1 := by
      rintro _ _ rfl rfl
      exact (jhMult_congr_right _ E₀).trans (jhMult_self hτ)
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    have z2 := cellone_offdiag hG hBZ x H (f b) (g b) hne
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    have r0 := b.2.1 0
    have r1 := b.2.1 1
    have c0 := b.2.2 0
    simp only [Fin.sum_univ_two, M, Fintype.card_fin] at r0 r1 c0
    have z1 : b.1 0 1 = 0 := by omega
    have z3 : b.1 0 0 = (x 0).1 := by omega
    have z4 : b.1 1 1 = (x 1).1 := by omega
    revert i j
    simp only [Fin.forall_fin_two]
    exact ⟨⟨z3, z1⟩, z2, z4⟩
  · simp

end

theorem UpperTheory.Lit.Mix.cellone :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), (∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = y.1), 0 < (q 0).1 → jm q hq y.rep ≠ 0 → ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = x.1), jhMult x.rep (prodIrr ![p, q 0] hc) = 0) → jm ![x, y] hd (prodIrr ![x, y] hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ x y N hd H
  exact (jacquet_multiplicity_single_cell hG hBZ ![x, y] H (stdBlocks (fun a => (![x, y] a).1) hd)).le
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem segTerm_smooth {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))

private theorem segTerm_irr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  isIrreducible_twist σ.irr _

private theorem piSeg_irr (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {d : ℕ} (σ : IrrRep (GL (Fin d) k))
    (l : ℕ) : (piTensor (segTerm σ.ρ l)).IsIrreducible :=
  GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin l) (fun _ => Fin d) fun a => ⟨_, segTerm σ.ρ l a, segTerm_smooth σ l a, segTerm_irr σ l a⟩

private theorem range_eq {l d N : ℕ} (e : (Σ _ : Fin l, Fin d) ≃ Fin N) {V X : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π)
    {T : Representation ℂ (Levi k fun _ : Fin l => Fin d) X} (hs : IsSmooth T) (hi : T.IsIrreducible)
    (θ : (jac e π).Equiv T) (f g : π.IntertwiningMap (parInd e T)) (hf : f ≠ 0) :
    ∃ c : ℂ, g = c • f := by
  haveI := hi
  have hs' : GroundTheory.Automorphic.IsSmooth T := hs
  have hb := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
  have key : ∀ f : π.IntertwiningMap (parInd e T), ∃ c : ℂ, ∀ x, Model.evalOne e f x = c • θ x := by
    intro f
    obtain ⟨c, hc⟩ := hb ((Model.evalOne e f).comp θ.symm.toIntertwiningMap)
    refine ⟨c, fun x => ?_⟩
    have h1 : c • θ x = Model.evalOne e f (θ.symm (θ x)) :=
      congrArg (fun F : T.IntertwiningMap T => F (θ x)) hc
    rw [h1, θ.symm_apply_apply]
  obtain ⟨a, ha⟩ := key f
  obtain ⟨b, hb⟩ := key g
  have hinj := (Model.evalOne_bijective e hπ T).1
  have ha0 : a ≠ 0 := by
    rintro rfl
    refine hf (hinj ?_)
    refine DFunLike.ext _ _ fun x => ?_
    rw [ha, zero_smul]
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine ⟨b / a, hinj (DFunLike.ext _ _ fun x => ?_)⟩
  have : Model.evalOne e ((b / a) • f) x = (b / a) • Model.evalOne e f x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [this, ha, hb, smul_smul, div_mul_cancel₀ _ ha0]

private theorem isSocle_of {l d N : ℕ} (e : (Σ _ : Fin l, Fin d) ≃ Fin N) {X : Type}
    [AddCommGroup X] [Module ℂ X] (π : IrrRep (GL (Fin N) k))
    {T : Representation ℂ (Levi k fun _ : Fin l => Fin d) X} (hs : IsSmooth T) (hi : T.IsIrreducible)
    (θ : (jac e π.ρ).Equiv T) (f : π.ρ.IntertwiningMap (parInd e T)) (hf : Function.Injective f)
    (H : ∀ (τ : IrrRep (GL (Fin N) k)) (g : τ.ρ.IntertwiningMap (parInd e T)), Function.Injective g →
      Nonempty (τ.ρ.Equiv π.ρ)) : IsSocle π.ρ (parInd e T) := by
  refine ⟨π.irr, f, hf, fun S hS => ?_⟩
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let ι : S.toRepresentation.IntertwiningMap (parInd e T) := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hsm : IsSmooth S.toRepresentation :=
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth (isSmooth_parInd _ _)
  obtain ⟨ψ⟩ : Nonempty (S.toRepresentation.Equiv π.ρ) :=
    H ⟨_, S.toRepresentation, hsm, hirr⟩ ι Subtype.val_injective
  have hf0 : f ≠ 0 := by
    rintro rfl
    haveI := Model.nontrivial_of_isIrreducible π.irr
    obtain ⟨v, w, h⟩ := exists_pair_ne π.V
    exact h (hf rfl)
  obtain ⟨c, hc⟩ := range_eq e π.smooth hs hi θ f (ι.comp ψ.symm.toIntertwiningMap) hf0
  refine (((isAtom_range π.irr f hf).le_iff_eq hS.1).1 fun v hv => ?_)
  have h1 : ι (ψ.symm (ψ ⟨v, hv⟩)) = c • f (ψ ⟨v, hv⟩) :=
    congrArg (fun F : π.ρ.IntertwiningMap (parInd e T) => F (ψ ⟨v, hv⟩)) hc
  rw [ψ.symm_apply_apply, ← map_smul] at h1
  exact ⟨_, h1.symm⟩

private theorem exists_unit_one_add_generator (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k) :
    ∃ z : IrrGL (k := k), IsZSeg Δ z.rep := by
  have hd : ∑ a, (Δ.term a).1 = Δ.len * Δ.d := Δ.sum_term_fst
  have H := hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd)
  obtain ⟨f, hf⟩ := (H (Z Δ).rep).1.1 (Z Δ).cl_rep
  obtain ⟨θ⟩ := (H (Z Δ).rep).2.1 (Z Δ).cl_rep
  have hS : IsSocle (Z Δ).rep.ρ
      (multiProd (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (segTerm Δ.start.rep.ρ Δ.len)) :=
    isSocle_of _ (Z Δ).rep (isSmooth_piTensor (segTerm_smooth _ _)) (piSeg_irr hBZ _ _) θ f hf
      fun τ g hg => IrrRep.cl_eq_iff.1 (((H τ).1.2 ⟨g, hg⟩).trans (Z Δ).cl_rep.symm)
  exact ⟨⟨_, Z Δ⟩, hd, hS.of_equiv (.refl _) (segProdEquiv Δ hd)⟩


set_option maxHeartbeats 1000000 in
private theorem glue {n s : ℕ} (π : IrrRep (GL (Fin n) k)) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, IrrRep (GL (Fin (d a)) k)) (φ : π.ρ.IntertwiningMap (multiProd e fun a => (σ a).ρ))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k))
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a))
    (ψ : ∀ a, (σ a).ρ.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) :
    ∃ (w : Fin (∑ a, t a) → IrrGL (k := k)) (E : (Σ c, Fin (w c).1) ≃ Fin n)
      (Φ : π.ρ.IntertwiningMap (multiProd E fun c => (w c).rep)), Function.Injective Φ ∧
        ∀ c, w c = u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (GlobalTheory.CompanionTheory.CuspEmbed.piTensorMap ψ)
  have hΨ : Function.Injective Ψ :=
    GlobalTheory.CompanionTheory.CuspEmbed.parIndMap_injective e _ (GlobalTheory.CompanionTheory.CuspEmbed.piTensorMap_injective ψ hψ)
  exact ⟨fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ), fun _ => rfl⟩

private theorem embeds' (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (x : IrrGL (k := k)) : ∃ (s : ℕ) (u : Fin s → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin x.1),
      (∀ a, (u a).IsCusp) ∧ ∃ φ : x.rep.IntertwiningMap (multiProd e fun a => (u a).rep), Function.Injective φ :=
  GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep)

private theorem word (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k) {N : ℕ}
    (π : IrrRep (GL (Fin N) k)) (h : IsZSeg Δ π.ρ) {s : ℕ} (u : Fin s → IrrGL (k := k)) (hu : ∀ a, (u a).IsCusp)
    (e : (Σ a, Fin (u a).1) ≃ Fin N) (φ : π.ρ.IntertwiningMap (multiProd e fun a => (u a).rep))
    (hφ : Function.Injective φ) (a : Fin s) : u a = Δ.first.nu (a : ℕ) := by
  obtain rfl : Δ.len * Δ.d = N := h.deg_eq
  have h1 : HasSupport π.ρ (Finset.univ.val.map u) :=
    ⟨s, u, rfl, π.irr, fun a => ⟨(hu a).1, IrrRep.irr _, (hu a).2⟩, e, .of_injective φ hφ⟩
  have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ h1 h.hasSupport
  obtain rfl : Δ.len = s := by simpa using (congrArg Multiset.card h2).symm
  have h3 : ∀ a, ∃ c : IrrCl (GL (Fin Δ.d) k), u a = ⟨Δ.d, c⟩ := by
    intro a
    have : u a ∈ Δ.ms := h2 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, hb⟩ := Segment.mem_ms.1 this
    exact ⟨(Δ.term b).2, hb.symm⟩
  choose c hc using h3
  obtain rfl : u = fun a => ⟨Δ.d, c a⟩ := funext hc
  obtain ⟨θ⟩ := (hZ Δ Δ.start.rep Δ.start.cl_rep e π).2.1 (h.cl_eq hZ)
  have hT : (piTensor fun a => (c a).rep.ρ).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin Δ.len) (fun _ => Fin Δ.d) fun a => (c a).rep
  haveI := Model.nontrivial_of_isIrreducible π.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  have h4 := GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e hT φ ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩
  have h5 : IsSubquotient (piTensor fun a => (c a).rep.ρ) (piTensor (segTerm Δ.start.rep.ρ Δ.len)) :=
    (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h4)).trans
      (.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective)
  have h6 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (segTerm Δ.start.rep.ρ Δ.len) a (c a).rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun a => (c a).rep.ρ) (fun a => (c a).rep.irr) a).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp h5 _))
  obtain ⟨ω⟩ := h6.nonempty_equiv (c a).rep.irr (segTerm_irr _ _ a)
  have ω' := ω.symm.trans (Δ.first.twEquiv _ (isSmoothChar_absPow ((a : ℕ) : ℂ)))
  exact (IrrGL.of_rep (⟨Δ.d, c a⟩ : IrrGL (k := k))).symm.trans
    ((IrrGL.of_eq_of.2 ⟨ω'⟩).trans (IrrGL.of_rep (Δ.first.nu (a : ℕ))))

end

theorem UpperTheory.Lit.Full.zfirst :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k), (∃ z : IrrGL (k := k), IsZSeg Δ z.rep) ∧ ∀ z : IrrGL (k := k), IsZSeg Δ z.rep → FirstIn z {Δ.first} := by
  intro hG hBZ hP k _ _ _ _ Δ
  obtain ⟨Z, -, hZ, -⟩ := hP k
  refine ⟨exists_unit_one_add_generator hBZ hZ Δ, fun z hz q hq hc hj => ?_⟩
  obtain ⟨y, hd, φ, hφ⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
  choose t u e' hu ψ hψ using fun a : Fin 2 => embeds' hG hBZ (![q 0, y] a)
  obtain ⟨w, E, Φ, hΦ, hwu⟩ := glue z.2.rep (fun a => (![q 0, y] a).1) (stdBlocks (fun a => (![q 0, y] a).1) hd)
    (fun a => (![q 0, y] a).2.rep) φ hφ t u e' ψ hψ
  have hw := word hG hBZ hZ Δ z.2.rep hz w (fun c => hwu c ▸ hu _ _) E Φ hΦ
  have h1 : HasSupport (q 0).rep (Finset.univ.val.map (u 0)) :=
    ⟨t 0, u 0, rfl, (q 0).2.rep.irr, fun a => ⟨(hu 0 a).1, IrrRep.irr _, (hu 0 a).2⟩, e' 0,
      .of_injective (ψ 0) (hψ 0)⟩
  have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ h1 (hasSupport_self hc)
  have h3 : t 0 = 1 := by simpa using congrArg Multiset.card h2
  let b : Fin (t 0) := ⟨0, by omega⟩
  have h4 : u 0 b = q 0 :=
    Multiset.mem_singleton.1 (h2 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ b))
  have h5 := hw (finSigmaFinEquiv ⟨0, b⟩)
  have h6 : ((finSigmaFinEquiv ⟨0, b⟩ : Fin (∑ a, t a)) : ℕ) = 0 := by
    rw [finSigmaFinEquiv_apply]; simp [b]
  rw [hwu, h6, Nat.cast_zero, IrrGL.nu_zero, Equiv.symm_apply_apply] at h5
  exact h4.symm.trans h5
end
