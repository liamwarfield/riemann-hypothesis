module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_hasSupport (hBZ : BernsteinZelevinskyFiniteness) (hG : GeometricLemma) (x : IrrGL (k := k)) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨s, d, σ, h⟩ := GlobalTheory.CuspSupportExist.main hBZ hG k x.1 (Irr.ofIrrRep x.2.rep)
  exact ⟨_, hasSupport_of_isCuspSupport h⟩

theorem map_univ_eq_sum {α : Type} {β : Type*} [Fintype α] (f : α → β) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset β) := by
  rw [Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem hasSupport_of_isSubquotient_prodIrr {c N : ℕ} {y : Fin c → IrrGL (k := k)}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL (k := k))} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  choose T u hu hc using ht
  have h3 := fun a => (hc a).2.2
  choose e' he' using h3
  let e := stdBlocks (fun a => (y a).1) hd
  have step1 : IsSubquotient (multiProd e fun a => (y a).rep)
      (multiProd e fun a => multiProd (e' a) fun b => (u a b).rep) :=
    GlobalTheory.CuspSupportExist.L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (GlobalTheory.CuspSupportExist.L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := GlobalTheory.CuspSupportExist.L_stage k c N (fun a => (y a).1) e T (fun a b => (u a b).1) e' _
    (fun a b => (u a b).rep) fun a b => (u a b).2.rep.smooth
  refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, ?_, hi,
    fun c => (hc _).2.1 _, E, h.trans (step1.trans hE)⟩
  rw [map_univ_eq_sum, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (T a)) => ({u p.1 p.2} : Multiset _)),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hu a, map_univ_eq_sum]

theorem exists_sum_of_jac (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (GlobalTheory.SmGL.jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL (k := k)), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL (k := k)) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := exists_hasSupport hBZ hG (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem eq_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (N : ℕ) :
    ∀ (x : IrrGL (k := k)), x.1 = N → ∀ s t : Multiset (IrrGL (k := k)), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (GlobalTheory.SmGL.jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hBZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s t : Multiset (IrrGL (k := k))} (hs : HasSupport π s)
    (ht : HasSupport π t) : s = t := by
  have φ := IrrGL.equivOf π hs.isSmooth hs.isIrreducible
  exact eq_of_hasSupport hG hBZ N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv φ) (ht.of_equiv φ)

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapInjectiveOfInjective
namespace GlobalTheory.CompanionTheory.PiTensor

theorem map_injective_of_injective
    (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (f : ∀ i, M i →ₗ[K] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  have hg : ∀ i, ∃ g : N i →ₗ[K] M i, g ∘ₗ f i = LinearMap.id := fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.2 (hf i))
  choose g hg using hg
  have hcomp : PiTensorProduct.map g ∘ₗ PiTensorProduct.map f = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  exact LinearMap.congr_fun hcomp x

end GlobalTheory.CompanionTheory.PiTensor
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.CuspEmbed

def piTensorMap {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) : (piTensor ρ).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact (f a).isIntertwining _ _ _ _

theorem piTensorMap_injective {α : Type} [Fintype α] [DecidableEq α] {Γ Y Z : α → Type}
    [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) (hf : ∀ a, Function.Injective (f a)) :
    Function.Injective (piTensorMap f) :=
  GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective ℂ α Y Z (fun a => (f a).toLinearMap) hf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_injective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {σ : Representation ℂ (Levi k m) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective (parIndMap e f) := fun x y h =>
  Subtype.ext (Subtype.ext (funext fun g => hf
    (congrArg (fun z : IndSp e σ => z.1.1 g) h)))

def Embeds (N : ℕ) (Q : Irr k N) : Prop :=
  ∃ (s : ℕ) (u : Fin s → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
    (∀ a, (u a).IsCusp) ∧ ∃ φ : Q.π.IntertwiningMap (multiProd e fun a => (u a).rep),
      Function.Injective φ

theorem intertw_of_subsingleton {G V W : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (g : G) : f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

theorem embeds_zero (Q : Irr k 0) : Embeds 0 Q := by
  have hQ := Q.irr
  have := nontrivial_of_irreducible hQ
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Q.V)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ Q.V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hker : Function.Injective f := by
    let S : Subrepresentation Q.π := ⟨LinearMap.ker f, fun g x hx => by
      rw [Subsingleton.elim g 1, map_one]
      exact hx⟩
    rcases eq_bot_or_eq_top S with h | h
    · have h' : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 h'
    · have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd (LinearMap.ker_eq_top.1 h' ▸ rfl : f v = 0) hf
  let u : Fin 0 → IrrGL (k := k) := fun a => a.elim0
  haveI : IsEmpty (Σ a, Fin (u a).1) := ⟨fun x => x.1.elim0⟩
  let e : (Σ a, Fin (u a).1) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let L := GlobalTheory.EmptyProd.lineEquiv (k := k) e fun a => (u a).rep
  exact ⟨0, u, e, fun a => a.elim0,
    ⟨L.symm.toLinearMap ∘ₗ f, intertw_of_subsingleton _ _ _⟩, L.symm.injective.comp hker⟩

theorem embeds_cusp (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) : Embeds n π := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  let x : IrrGL (k := k) := IrrGL.of π.π π.smooth π.irr
  let ψ := multiProdEquiv e fun _ : Fin 1 => IrrGL.equivOf π.π π.smooth π.irr
  refine ⟨1, fun _ => x, e, fun _ => (IrrGL.isCusp_of.2 ⟨hn, hc⟩), (φ.trans ψ).toIntertwiningMap,
    (φ.trans ψ).toLinearEquiv.injective⟩

theorem reduce_embed (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hGL : GlobalTheory.Published.GeometricLemma) (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ ∃ φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π),
        Function.Injective φ := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := GlobalTheory.CuspSupportExist.L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hGL k n π s d e Y τ hτi hτq
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (d a)) fun a => (σ a).toIrrRep
  obtain ⟨ε⟩ := hσ.nonempty_equiv hτi hirr
  let ψ := parIndEquiv e ε.symm
  exact ⟨s, d, e, σ, GlobalTheory.CuspSupportExist.L_lt k n s d e hne,
    ψ.toIntertwiningMap.comp φ, ψ.toLinearEquiv.injective.comp hφ⟩

theorem glue_embed (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k))
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a)) (hu : ∀ a b, (u a b).IsCusp)
    (ψ : ∀ a, (σ a).π.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) : Embeds n π := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (piTensorMap ψ)
  have hΨ : Function.Injective Ψ := parIndMap_injective e _ (piTensorMap_injective ψ hψ)
  exact ⟨∑ a, t a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    fun c => hu _ _, (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ)⟩

theorem embeds (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma)
    (N : ℕ) (Q : Irr k N) : Embeds N Q := by
  induction N using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact embeds_zero Q
  by_cases hc : IsCuspidal Q.π
  · exact embeds_cusp n hn Q hc
  · have hr := reduce_embed hBZ hGL n Q hc
    obtain ⟨s, d, e, σ, hlt, hr⟩ := hr
    obtain ⟨φ, hφ⟩ := hr
    have h : ∀ a, Embeds (d a) (σ a) := fun a => ih (d a) (hlt a) (σ a)
    unfold Embeds at h
    choose t u e' hu ψ hψ using h
    exact glue_embed n Q s d e σ φ hφ t u e' hu ψ hψ

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (Q : GlobalTheory.SplitRead.Irr k N),
      ∃ (s : ℕ) (u : Fin s → GlobalTheory.LocGL.IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
        (∀ a, (u a).IsCusp) ∧
          ∃ φ : Q.π.IntertwiningMap (GlobalTheory.SmGL.multiProd e fun a => (u a).rep),
            Function.Injective φ :=
  fun hBZ hGL _ _ _ _ _ N Q => embeds hBZ hGL N Q

end GlobalTheory.CompanionTheory.CuspEmbed
end
end
