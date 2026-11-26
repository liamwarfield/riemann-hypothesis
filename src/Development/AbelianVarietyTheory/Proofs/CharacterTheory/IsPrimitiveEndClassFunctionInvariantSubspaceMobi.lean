module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspaces
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspaces
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

private lemma card_nilRad_eq_card_linearMap_quot (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module F V] (A : Submodule F V) :
    Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) = Nat.card ((V ⧸ A) →ₗ[F] A) := by
  refine Nat.card_congr
    { toFun := fun n => A.liftQ (LinearMap.codRestrict A n.1 n.2.1) (fun a ha => by
          simp [LinearMap.mem_ker, n.2.2 a ha])
      invFun := fun h => ⟨A.subtype ∘ₗ h ∘ₗ A.mkQ, fun x => by simp, fun x hx => by
          simp [(Submodule.Quotient.mk_eq_zero A).2 hx]⟩
      left_inv := fun n => by ext x; simp
      right_inv := fun h => by ext x; simp }

private lemma card_invariant_complements_over_eq_card_nilRad (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) (U : Submodule F (V ⧸ A)) (hU : ∀ y ∈ U, A.mapQ A g hg y ∈ U) :
    Nat.card {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} =
      Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) := by
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype A)
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective A.mkQ (Submodule.range_mkQ A)
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  let gU : U →ₗ[F] U := (A.mapQ A g hg).restrict hU
  let D : (U →ₗ[F] A) → (U →ₗ[F] V) := fun τ => σ ∘ₗ U.subtype ∘ₗ gU + A.subtype ∘ₗ τ ∘ₗ gU -
    g ∘ₗ σ ∘ₗ U.subtype - g ∘ₗ A.subtype ∘ₗ τ
  have hDA : ∀ τ u, D τ u ∈ A := by
    intro τ u
    rw [← Submodule.Quotient.mk_eq_zero]
    have h1 : ∀ q, A.mkQ (σ q) = q := fun q => LinearMap.congr_fun hσ q
    have h2 : ∀ a : A, A.mkQ (g a) = 0 := fun a => (Submodule.Quotient.mk_eq_zero A).2 (hg a a.2)
    have h3 : A.mkQ (g (σ u)) = A.mapQ A g hg u := by
      conv_rhs => rw [← h1 u]
      rfl
    simp only [D, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add]
    have := h1 (gU u)
    have h4 := h2 (τ u)
    have h5 := h2 (τ (gU u))
    simp only [Submodule.mkQ_apply] at this h4 h5 h3 ⊢
    rw [this, h3, h4]
    simp [gU]
  have hp' : ∀ u : U, p u = u := fun u => LinearMap.congr_fun hp u
  let E : (V ⧸ A) →ₗ[F] (V ⧸ A) := U.subtype ∘ₗ p
  have hS : Nat.card {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1} =
      Nat.card ((V ⧸ A) →ₗ[F] A) := by
    refine Nat.card_congr
      { toFun := fun q => q.1.1 ∘ₗ p + q.1.2 ∘ₗ (LinearMap.id - E)
        invFun := fun h => ⟨(h ∘ₗ U.subtype, ρ ∘ₗ D (h ∘ₗ U.subtype) ∘ₗ p + h ∘ₗ (LinearMap.id - E)),
          by ext u; simp [E, hp']⟩
        left_inv := fun q => ?_
        right_inv := fun h => ?_ }
    · have h1 : (q.1.1 ∘ₗ p + q.1.2 ∘ₗ (LinearMap.id - E)) ∘ₗ U.subtype = q.1.1 := by
        ext u; simp [E, hp']
      refine Subtype.ext (Prod.ext h1 ?_)
      simp only [h1]
      ext x
      have h2 := LinearMap.congr_fun q.2 (p (Submodule.Quotient.mk x))
      simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h2
      simp [E, hp', ← h2]
    · ext x
      simp [E, hp']
  have hρ' : ∀ v ∈ A, (ρ v : V) = v := fun v hv => congrArg Subtype.val (LinearMap.congr_fun hρ ⟨v, hv⟩)
  have hσ' : ∀ q : V ⧸ A, A.mkQ (σ q) = q := fun q => LinearMap.congr_fun hσ q
  have hmapQ : ∀ v : V, A.mkQ (g v) = A.mapQ A g hg (A.mkQ v) := fun v => rfl
  let Γ : (U →ₗ[F] A) → (U →ₗ[F] V) := fun τ => σ ∘ₗ U.subtype + A.subtype ∘ₗ τ
  have hΓ : ∀ τ (u : U), A.mkQ (Γ τ u) = u := by
    intro τ u
    simp only [Γ, LinearMap.add_apply, LinearMap.comp_apply, map_add (f := _), hσ']
    simp [(Submodule.Quotient.mk_eq_zero A).2 (τ u).2]
  have memN : ∀ k : (V ⧸ A) →ₗ[F] A, A.subtype ∘ₗ k ∘ₗ A.mkQ ∈ _root_.GlobalTheory.CuspGL.nilRad A :=
    fun k => ⟨fun x => by simp, fun x hx => by simp [(Submodule.Quotient.mk_eq_zero A).2 hx]⟩
  have botΓ : ∀ τ, LinearMap.range (Γ τ) ⊓ A = ⊥ := by
    intro τ
    rw [eq_bot_iff]
    rintro x ⟨⟨u, rfl⟩, hx⟩
    have h0 : (u : V ⧸ A) = 0 := by rw [← hΓ τ u]; exact (Submodule.Quotient.mk_eq_zero A).2 hx
    have hu : u = 0 := Subtype.ext h0
    rw [hu, map_zero]
    exact Submodule.zero_mem _
  have mapΓ : ∀ τ, (LinearMap.range (Γ τ)).map A.mkQ = U := by
    intro τ
    rw [← LinearMap.range_comp]
    have : A.mkQ ∘ₗ Γ τ = U.subtype := by ext u; exact hΓ τ u
    rw [this, Submodule.range_subtype]
  have invΓ : ∀ q : {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1},
      ∀ v ∈ LinearMap.range (Γ q.1.1),
        (g + A.subtype ∘ₗ q.1.2 ∘ₗ A.mkQ) v ∈ LinearMap.range (Γ q.1.1) := by
    rintro q _ ⟨u, rfl⟩
    refine ⟨gU u, ?_⟩
    have h2 : (q.1.2 (A.mkQ (Γ q.1.1 u)) : V) = D q.1.1 u := by
      rw [hΓ]
      have := LinearMap.congr_fun q.2 u
      simp only [LinearMap.comp_apply, Submodule.coe_subtype] at this
      rw [this, hρ' _ (hDA _ _)]
    change _ = g (Γ q.1.1 u) + (q.1.2 (A.mkQ (Γ q.1.1 u)) : V)
    rw [h2]
    simp only [D, Γ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, map_add]
    abel
  let Φ : {q : (U →ₗ[F] A) × ((V ⧸ A) →ₗ[F] A) // q.2 ∘ₗ U.subtype = ρ ∘ₗ D q.1} →
      {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
        x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} :=
    fun q => ⟨(A.subtype ∘ₗ q.1.2 ∘ₗ A.mkQ, LinearMap.range (Γ q.1.1)), memN _, botΓ _, invΓ q,
      mapΓ _⟩
  have hinjΦ : Function.Injective Φ := by
    intro q q' h
    have h1 := congrArg (fun x => x.1.1) h
    have h2 := congrArg (fun x => x.1.2) h
    simp only [Φ] at h1 h2
    have e2 : q.1.2 = q'.1.2 := by
      ext x
      simpa using LinearMap.congr_fun h1 x
    have e1 : q.1.1 = q'.1.1 := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      have hu : Γ q.1.1 u ∈ LinearMap.range (Γ q'.1.1) := h2 ▸ ⟨u, rfl⟩
      obtain ⟨u', hu'⟩ := hu
      have hu'' : u' = u := Subtype.ext (by rw [← hΓ q'.1.1 u', hu', hΓ])
      subst hu''
      simp only [Γ, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        add_right_inj] at hu'
      exact hu'.symm
    exact Subtype.ext (Prod.ext e1 e2)
  have hsurjΦ : Function.Surjective Φ := by
    rintro ⟨⟨n, W⟩, hn, hbot, hinv, hmap⟩
    have hinj : Function.Injective (A.mkQ.comp W.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, eq_bot_iff]
      rintro ⟨x, hxW⟩ hxA
      have hx : x ∈ W ⊓ A := ⟨hxW, hxA⟩
      rw [hbot] at hx
      simpa using hx
    have hrange : LinearMap.range (A.mkQ.comp W.subtype) = U := by
      rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
    let e : W ≃ₗ[F] U := (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
    have he : ∀ u : U, A.mkQ (e.symm u : V) = u :=
      fun u => congrArg Subtype.val (e.apply_symm_apply u)
    let τ : U →ₗ[F] A := LinearMap.codRestrict A (W.subtype ∘ₗ e.symm.toLinearMap - σ ∘ₗ U.subtype)
      (fun u => (Submodule.Quotient.mk_eq_zero A).1 (by
        have h1 := he u
        have h2 := hσ' u
        simp only [Submodule.mkQ_apply] at h1 h2
        simp [Submodule.Quotient.mk_sub, h1, h2]))
    have hΓτ : ∀ u, Γ τ u = e.symm u := by
      intro u; simp [Γ, τ]
    have hW : LinearMap.range (Γ τ) = W := by
      ext v
      constructor
      · rintro ⟨u, rfl⟩
        rw [hΓτ]
        exact (e.symm u).2
      · intro hv
        exact ⟨e ⟨v, hv⟩, by rw [hΓτ, e.symm_apply_apply]⟩
    let k : (V ⧸ A) →ₗ[F] A := A.liftQ (LinearMap.codRestrict A n hn.1) (fun a ha => by
      simp [LinearMap.mem_ker, hn.2 a ha])
    have hk : A.subtype ∘ₗ k ∘ₗ A.mkQ = n := by ext x; simp [k]
    have hcond : k ∘ₗ U.subtype = ρ ∘ₗ D τ := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [hρ' _ (hDA τ u)]
      have hk' : (k (u : V ⧸ A) : V) = n (Γ τ u) := by
        conv_lhs => rw [← hΓ τ u]
        exact LinearMap.congr_fun hk (Γ τ u)
      have hmemu : Γ τ u ∈ W := by rw [hΓτ]; exact (e.symm u).2
      have hmemg : Γ τ (gU u) ∈ W := by rw [hΓτ]; exact (e.symm (gU u)).2
      have hgn : (g + n) (Γ τ u) = Γ τ (gU u) := by
        have := @hinj ⟨_, hinv _ hmemu⟩ ⟨_, hmemg⟩ (by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply]
          rw [hΓ, LinearMap.add_apply, map_add (f := _), hmapQ, hΓ,
            show A.mkQ (n (Γ τ u)) = 0 from (Submodule.Quotient.mk_eq_zero A).2 (hn.1 _), add_zero]
          rfl)
        exact congrArg Subtype.val this
      rw [hk']
      rw [LinearMap.add_apply] at hgn
      rw [eq_sub_of_add_eq' hgn]
      simp only [D, Γ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, map_add]
      abel
    exact ⟨⟨(τ, k), hcond⟩, Subtype.ext (Prod.ext hk hW)⟩
  rw [card_nilRad_eq_card_linearMap_quot, ← hS]
  exact (Nat.card_eq_of_bijective Φ ⟨hinjΦ, hsurjΦ⟩).symm

private lemma psi_restrict_complement_eq_psi_quotient (F : Type) [Field F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) (n : Module.End F V) (hn : n ∈ _root_.GlobalTheory.CuspGL.nilRad A)
    (W : Submodule F V) (hWA : W ⊓ A = ⊥) (hW : ∀ v ∈ W, (g + n) v ∈ W)
    (hU : ∀ y ∈ W.map A.mkQ, A.mapQ A g hg y ∈ W.map A.mkQ) :
    _root_.GlobalTheory.CuspGL.psi s W ((g + n).restrict hW) =
      _root_.GlobalTheory.CuspGL.psi s (W.map A.mkQ) ((A.mapQ A g hg).restrict hU) := by
  have hinj : Function.Injective (A.mkQ.comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxA
    have hx : x ∈ W ⊓ A := ⟨hxW, hxA⟩
    rw [hWA] at hx
    simpa using hx
  have hrange : LinearMap.range (A.mkQ.comp W.subtype) = W.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let e : W ≃ₗ[F] W.map A.mkQ := (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  rw [← _root_.GlobalTheory.CuspGL.psi_conj F s _ _ e]
  congr 1
  ext y
  obtain ⟨w, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.restrict_apply]
  simp [e, hn.1 w.1]

theorem _root_.GlobalTheory.CuspGL.finsum_psi_transversal : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, _root_.GlobalTheory.CuspGL.psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
  intro F _ _ V _ _ _ s A g hg
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ⧸ A) := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun U : Submodule F V => (U : Set V)) SetLike.coe_injective
  haveI : Finite (Submodule F (V ⧸ A)) :=
    Finite.of_injective (fun U : Submodule F (V ⧸ A) => (U : Set (V ⧸ A))) SetLike.coe_injective
  set gb := A.mapQ A g (fun x hx => hg x hx) with hgb
  have hcount : ∀ (U : Submodule F (V ⧸ A)), (∀ y ∈ U, gb y ∈ U) →
      Nat.card {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
        x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧ x.2.map A.mkQ = U} =
        Nat.card (_root_.GlobalTheory.CuspGL.nilRad A) :=
    fun U hU => card_invariant_complements_over_eq_card_nilRad F V A g hg U hU
  have hstep : ∀ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2},
      ∀ y ∈ x.1.2.map A.mkQ, gb y ∈ x.1.2.map A.mkQ := by
    intro x y hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨(g + x.1.1) w, x.2.2.2 w hw, ?_⟩
    have h1 : A.mkQ (x.1.1 w) = 0 := (Submodule.Quotient.mk_eq_zero A).2 (x.2.1.1 w)
    simp only [LinearMap.add_apply, map_add (f := _), h1, add_zero]
    rfl
  have hpsi : ∀ x : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2},
      _root_.GlobalTheory.CuspGL.psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) =
        _root_.GlobalTheory.CuspGL.psi s (x.1.2.map A.mkQ) (gb.restrict (hstep x)) :=
    fun x => psi_restrict_complement_eq_psi_quotient F V s A g hg x.1.1 x.2.1 x.1.2 x.2.2.1 x.2.2.2
      (hstep x)
  let fib : {x : Module.End F V × Submodule F V // x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧
      x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2} → {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U} :=
    fun x => ⟨_, hstep x⟩
  let G : {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U} → ℂ :=
    fun U => _root_.GlobalTheory.CuspGL.psi s U.1 (gb.restrict U.2)
  haveI := Fintype.ofFinite {U : Submodule F (V ⧸ A) // ∀ y ∈ U, gb y ∈ U}
  haveI := Fintype.ofFinite {x : Module.End F V × Submodule F V //
    x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}
  rw [_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F (V ⧸ A) s gb, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.mul_sum]
  simp_rw [hpsi]
  change ∑ x, G (fib x) = ∑ U, _ * G U
  rw [← Finset.sum_fiberwise Finset.univ fib (fun x => G (fib x))]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => G U) (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hequiv : {x // fib x = U} ≃ {x : Module.End F V × Submodule F V //
      x.1 ∈ _root_.GlobalTheory.CuspGL.nilRad A ∧ x.2 ⊓ A = ⊥ ∧ (∀ v ∈ x.2, (g + x.1) v ∈ x.2) ∧
        x.2.map A.mkQ = U.1} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, congrArg Subtype.val x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1⟩, Subtype.ext y.2.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← hcount U.1 U.2, ← Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype]

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspacesStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_transversal | exact GlobalTheory.CuspGL.finsum_psi_transversal | (intros; apply GlobalTheory.CuspGL.finsum_psi_transversal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspac
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspac
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem exists_comp_eq_of_ker_le {F : Type} [Field F] {U X Y : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] (p : U →ₗ[F] X) (f : U →ₗ[F] Y)
    (h : LinearMap.ker p ≤ LinearMap.ker f) : ∃ k : X →ₗ[F] Y, ∀ u, k (p u) = f u := by
  obtain ⟨k, hk⟩ := LinearMap.exists_extend
    (((LinearMap.ker p).liftQ f h) ∘ₗ p.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun u => ?_⟩
  have := LinearMap.congr_fun hk ⟨p u, LinearMap.mem_range_self p u⟩
  simpa using this

theorem exists_nilRad_extend {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (A W : Submodule F V) (h' : Module.End F W) (hh : h' ∈ nilRad (A.comap W.subtype)) :
    ∃ L : Module.End F V, L ∈ nilRad A ∧ ∀ x : W, L x = h' x := by
  obtain ⟨k, hk⟩ := exists_comp_eq_of_ker_le (A.mkQ ∘ₗ W.subtype)
    (LinearMap.codRestrict A (W.subtype ∘ₗ h') (fun x => hh.1 x)) (by
      intro x hx
      have hx' : (x : V) ∈ A := by simpa using hx
      have := hh.2 x hx'
      rw [LinearMap.mem_ker]
      ext
      simp [this])
  refine ⟨A.subtype ∘ₗ k ∘ₗ A.mkQ, ⟨fun x => by simp, fun x hx => ?_⟩, fun x => ?_⟩
  · have : A.mkQ x = 0 := by simpa using hx
    simp only [LinearMap.comp_apply, this, map_zero]
  · have := congrArg Subtype.val (hk x)
    simpa using this

theorem sum_restrict_eq_zero_of_mixed (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (h1 : W ⊓ A ≠ ⊥) (h2 : ¬ W ≤ A) (φ : Module.End F W → ℂ) (hφ : IsPrimitive φ) :
    ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W},
      φ ((g + h.1).restrict h.2.2) = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Module.End F W) := Finite.of_injective _ DFunLike.coe_injective
  set A' : Submodule F W := A.comap W.subtype with hA'
  have hb : A' ≠ ⊥ := by
    intro h
    apply h1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : W) ∈ A' := hx.2
    rw [h, Submodule.mem_bot] at this
    simpa using congrArg Subtype.val this
  have ht : A' ≠ ⊤ := by
    intro h
    apply h2
    intro x hx
    have : (⟨x, hx⟩ : W) ∈ A' := h ▸ Submodule.mem_top
    exact this
  let S := {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype (nilRad A') := Fintype.ofFinite _
  have inner : ∀ h : S, ∑ h' : nilRad A', φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    intro h
    have := hφ A' hb ht ((g + h.1).restrict h.2.2) (by
      intro x hx
      have hx' : (x : V) ∈ A := hx
      change (g + h.1) x ∈ A
      rw [LinearMap.add_apply]
      exact A.add_mem (hg _ hx') (h.2.1.1 _))
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype] at this
    exact this
  have shift : ∀ h' : nilRad A', ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) =
      ∑ h : S, φ ((g + h.1).restrict h.2.2) := by
    intro h'
    obtain ⟨L, hL, hLW⟩ := exists_nilRad_extend A W h'.1 h'.2
    let T : S → S := fun h => ⟨h.1 + L, ⟨fun x => A.add_mem (h.2.1.1 x) (hL.1 x), fun x hx => by
      rw [LinearMap.add_apply, h.2.1.2 x hx, hL.2 x hx, add_zero]⟩, fun x hx => by
        rw [← add_assoc, LinearMap.add_apply, hLW ⟨x, hx⟩]
        exact W.add_mem (h.2.2 x hx) (h'.1 ⟨x, hx⟩).2⟩
    have hT : Function.Bijective T := by
      apply Finite.injective_iff_bijective.mp
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (add_right_cancel this)
    refine Fintype.sum_bijective T hT _ _ fun h => ?_
    congr 1
    ext x
    change (g + h.1) x + (h'.1 x : V) = (g + (h.1 + L)) x
    rw [← add_assoc, LinearMap.add_apply (g + h.1), hLW x]
  have tot : ∑ h' : nilRad A', ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun h _ => inner h
  simp only [shift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_eq_zero] at tot
  haveI : Nonempty (nilRad A') := ⟨⟨0, fun x => A'.zero_mem, fun x _ => rfl⟩⟩
  rw [finsum_eq_sum_of_fintype]
  rcases tot with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · exact h

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V), (∀ x ∈ A, g x ∈ A) → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∀ φ : Module.End F W → ℂ, IsPrimitive φ → ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}, φ ((g + h.1).restrict h.2.2) = 0 := by
  first | exact @GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | exact GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | (intros; apply GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.PsiPrimitive

open scoped Classical

open Classical in
theorem finsum_sub {α : Type} [Fintype α] (p : α → Prop) (f : {a // p a} → ℂ) :
    ∑ᶠ x, f x = ∑ a, if h : p a then f ⟨a, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∀ i : {a // p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = f i := fun i => by
    rw [dite_eq_left i.2]
  have h2 : ∀ i : {a // ¬ p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 := fun i => by
    rw [dite_eq_right i.2]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

open Classical in
def res {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (k : Module.End F V) : ℂ :=
  if hk : ∀ x ∈ W, k x ∈ W then psi s W (k.restrict hk) else 0

theorem psi_trivial {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Subsingleton V] (g : Module.End F V) :
    psi s V g = 0 := by
  rw [psi_eq s V g]
  have hpoly : LinearMap.charpoly g = 1 := by
    have hdeg : (LinearMap.charpoly g).natDegree = 0 := by
      rw [LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g) hdeg
  have hs1 : s 1 = 0 := by
    have h11 := hs 1 1 monic_one monic_one
    rw [one_mul] at h11
    linear_combination -h11
  have hempty : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} := by
    refine ⟨fun W => W.2.1 ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    rw [Subsingleton.elim x 0]
    exact W.1.zero_mem
  rw [hpoly, hs1, finsum_of_isEmpty, sub_zero]

theorem res_top {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (k : Module.End F V) : res s ⊤ k = psi s V k := by
  have htop : ∀ x ∈ (⊤ : Submodule F V), k x ∈ (⊤ : Submodule F V) := fun _ _ => Submodule.mem_top
  unfold res
  rw [dite_eq_left htop]
  have hconj := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s (⊤ : Submodule F V) V Submodule.topEquiv (k.restrict htop)
  rw [← hconj]
  congr 1

theorem step {F : Type} [Field F] [Finite F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ih : ∀ W : Submodule F V, W ≠ ⊤ → IsPrimitive (psi s W)) : IsPrimitive (psi s V) := by
  classical
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun f : Module.End F V => (f : V → V)) fun a b h => LinearMap.ext (congrFun h)
  have : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  let _ : Fintype (Module.End F V) := Fintype.ofFinite _
  let _ : Fintype (Submodule F V) := Fintype.ofFinite _
  intro A hA0 hAT g hg
  set H : Finset (Module.End F V) := Finset.univ.filter fun h => h ∈ nilRad A with hH
  have memH : ∀ h, h ∈ H ↔ h ∈ nilRad A := fun h => by simp [hH]
  have sum_H : ∀ f : Module.End F V → ℂ,
      ∑ h ∈ H, f h = ∑ h, if h ∈ nilRad A then f h else 0 := fun f => by
    rw [hH, Finset.sum_filter]
  have card_H : ((Nat.card (nilRad A) : ℕ) : ℂ) = (H.card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have res_bot : ∀ k : Module.End F V, res s (⊥ : Submodule F V) k = 0 := by
    intro k
    unfold res
    split_ifs
    · exact psi_trivial s hs _ _
    · rfl
  have s_cp : ∀ k : Module.End F V, s (LinearMap.charpoly k) = ∑ W : Submodule F V, res s W k := by
    intro k
    exact (GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F V s k).trans
      (finsum_sub (fun W : Submodule F V => ∀ x ∈ W, k x ∈ W) fun W => psi s W.1 (k.restrict W.2))
  have res_le : ∀ h ∈ nilRad A, ∀ W : Submodule F V, W ≤ A → res s W (g + h) = res s W g := by
    intro h hh W hWA
    have hh' : (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0 := hh
    have h0 : ∀ x ∈ W, h x = 0 := fun x hx => hh'.2 x (hWA hx)
    unfold res
    by_cases hk : ∀ x ∈ W, g x ∈ W
    · have hk' : ∀ x ∈ W, (g + h) x ∈ W := fun x hx => by
        simpa [h0 x hx] using hk x hx
      rw [dite_eq_left hk', dite_eq_left hk]
      congr 1
      ext x
      simp [h0 x.1 x.2]
    · have hk' : ¬ ∀ x ∈ W, (g + h) x ∈ W := fun hk' => hk fun x hx => by
        simpa [h0 x hx] using hk' x hx
      rw [dite_eq_right hk', dite_eq_right hk]
  have res_mixed : ∀ W : Submodule F V, W ≠ ⊤ → W ⊓ A ≠ ⊥ → ¬ W ≤ A →
      ∑ h ∈ H, res s W (g + h) = 0 := by
    intro W hWT hWA hWle
    have key := (finsum_sub (fun h : Module.End F V => h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W)
      fun h => psi s W ((g + h.1).restrict h.2.2)).symm.trans
        (GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace F V A W g hg hWA hWle (psi s W) (ih W hWT))
    rw [← key, sum_H]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h ∈ nilRad A <;> simp [hh, res]
  have sum_le : ∑ W : Submodule F V, (if W ≤ A then res s W g else 0) =
      s (LinearMap.charpoly (g.restrict hg)) := by
    have key := (finsum_sub (fun W : Submodule F V => W ≤ A ∧ ∀ x ∈ W, g x ∈ W)
      fun W => psi s W.1 (g.restrict W.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le F V s A g hg)
    rw [← key]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ≤ A <;> by_cases hk : ∀ x ∈ W, g x ∈ W <;> simp [hW, hk, res]
  have sum_disj : ∑ W : Submodule F V,
      (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    have key := (finsum_sub
      (fun x : Module.End F V × Submodule F V =>
        x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2)
      fun x => psi s x.1.2 ((g + x.1.1).restrict x.2.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces F V s A g hg)
    rw [← card_H, ← key, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ⊓ A = ⊥
    · rw [if_pos hW, sum_H]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hh : h ∈ nilRad A <;> simp [hh, hW, res]
    · rw [if_neg hW]
      symm
      refine Finset.sum_eq_zero fun h _ => ?_
      simp [hW]
  have split : ∀ W : Submodule F V, W ≠ ⊤ →
      ∑ h ∈ H, res s W (g + h) =
        (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) +
          (if W ≤ A then (H.card : ℂ) * res s W g else 0) := by
    intro W hWT
    by_cases hb : W = ⊥
    · subst hb
      simp [res_bot]
    by_cases hle : W ≤ A
    · have hmeet : W ⊓ A ≠ ⊥ := by rw [inf_eq_left.2 hle]; exact hb
      rw [if_neg hmeet, if_pos hle, zero_add,
        Finset.sum_congr rfl fun h hh => res_le h ((memH h).1 hh) W hle, Finset.sum_const, nsmul_eq_mul]
    by_cases hd : W ⊓ A = ⊥
    · rw [if_pos hd, if_neg hle, add_zero]
    · rw [if_neg hd, if_neg hle, add_zero]
      exact res_mixed W hWT hd hle
  have s_split : s (LinearMap.charpoly g) = s (LinearMap.charpoly (g.restrict hg)) +
      s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).1]
    exact hs _ _ (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)
  have s_const : ∑ h ∈ H, s (LinearMap.charpoly (g + h)) = (H.card : ℂ) * s (LinearMap.charpoly g) := by
    rw [Finset.sum_congr rfl fun h hh => by rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).2 h ((memH h).1 hh)],
      Finset.sum_const, nsmul_eq_mul]
  have psi_expand : ∀ k : Module.End F V, psi s V k =
      s (LinearMap.charpoly k) - ∑ W ∈ Finset.univ.erase ⊤, res s W k := by
    intro k
    rw [s_cp, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⊤), res_top]
    ring
  have proper : ∑ W ∈ Finset.univ.erase ⊤, ∑ h ∈ H, res s W (g + h) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) +
        (H.card : ℂ) * s (LinearMap.charpoly (g.restrict hg)) := by
    rw [Finset.sum_congr rfl fun W hW => split W (Finset.ne_of_mem_erase hW), Finset.sum_add_distrib]
    have htop1 : ¬ (⊤ : Submodule F V) ⊓ A = ⊥ := by rw [top_inf_eq]; exact hA0
    have htop2 : ¬ (⊤ : Submodule F V) ≤ A := fun h => hAT (top_le_iff.1 h)
    rw [Finset.sum_erase _ (by rw [if_neg htop1]), Finset.sum_erase _ (by rw [if_neg htop2]),
      sum_disj, ← sum_le, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    split_ifs <;> simp
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [Set.indicator_apply]
  rw [← sum_H, Finset.sum_congr rfl fun h _ => psi_expand (g + h), Finset.sum_sub_distrib,
    Finset.sum_comm, proper, s_const, s_split]
  ring

end GlobalTheory.CuspGL.PsiPrimitive

namespace GlobalTheory.CuspGL

theorem isPrimitive_psi : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  intro F _ _ V _ _ _ s hs
  suffices key : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.finrank F V < n → IsPrimitive (psi s V) from key _ V (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro V _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro V _ _ _ h
    exact PsiPrimitive.step s hs V fun W hW =>
      ih W (lt_of_lt_of_le (Submodule.finrank_lt hW) (Nat.lt_succ_iff.1 h))

end GlobalTheory.CuspGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_psi | exact GlobalTheory.CuspGL.isPrimitive_psi | (intros; apply GlobalTheory.CuspGL.isPrimitive_psi <;> assumption)
end
