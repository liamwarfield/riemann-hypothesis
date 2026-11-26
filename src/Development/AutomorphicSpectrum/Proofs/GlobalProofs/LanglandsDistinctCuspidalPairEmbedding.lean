module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqOfSubsingletonStep
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL.SupportUnique

variable {G H V Y Y' W₀ W₁ : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Y'] [Module ℂ Y'] [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁]

theorem exists_quot_map {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    (A T : Subrepresentation μ) (hT : T = ⊤) (E : (subQuot T A).Equiv τ) :
    ∃ q : μ.IntertwiningMap τ, Function.Surjective q ∧ ∀ v, q v = 0 ↔ v ∈ A.toSubmodule := by
  have hv : ∀ v : V, v ∈ T.toSubmodule := by
    subst hT
    intro v
    exact Submodule.mem_top
  let j : V →ₗ[ℂ] T.toSubmodule := LinearMap.codRestrict T.toSubmodule LinearMap.id hv
  let L : V →ₗ[ℂ] Y := E.toIntertwiningMap.toLinearMap ∘ₗ (Submodule.mkQ _) ∘ₗ j
  have hL : ∀ v, L v = E.toIntertwiningMap (Submodule.Quotient.mk (j v)) := fun v => rfl
  have hint : ∀ (g : G) (v : V), L (μ g v) = τ g (L v) := by
    intro g v
    rw [hL, hL]
    refine Eq.trans ?_ (Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g _)
    rfl
  refine ⟨L.intertwiningMap_of_isIntertwiningMap μ τ hint, ?_, ?_⟩
  · intro y
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (E.symm y)
    refine ⟨(w : V), ?_⟩
    show L w = y
    rw [hL]
    have hj : j w = w := Subtype.ext rfl
    rw [hj, hw]
    exact E.apply_symm_apply y
  · intro v
    show L v = 0 ↔ v ∈ A.toSubmodule
    rw [hL]
    constructor
    · intro h0
      have h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0 := by
        rw [← E.symm_apply_apply (Submodule.Quotient.mk (j v))]
        change E.symm (E.toIntertwiningMap (Submodule.Quotient.mk (j v))) = 0
        rw [h0]
        exact map_zero E.symm.toIntertwiningMap
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
      exact h1
    · intro h0
      have h1 : (Submodule.Quotient.mk (j v) : T.toSubmodule ⧸ A.toSubmodule.comap T.toSubmodule.subtype) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact h0
      rw [h1]
      exact map_zero E.toIntertwiningMap

theorem exists_sub_equiv {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    (X B : Subrepresentation μ) (hB : B = ⊥) (E : (subQuot X B).Equiv τ) :
    Nonempty (X.toRepresentation.Equiv τ) := by
  subst hB
  let m : X.toRepresentation.IntertwiningMap (subQuot X ⊥) :=
    ⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩
  have hm : Function.Injective m := by
    intro x y hxy
    have h1 : x - y ∈ (⊥ : Subrepresentation μ).toSubmodule.comap X.toSubmodule.subtype :=
      (Submodule.Quotient.eq _).1 hxy
    rw [Submodule.mem_comap] at h1
    have h0 : ((x - y : X.toSubmodule) : V) = 0 := (Submodule.mem_bot ℂ).1 h1
    exact sub_eq_zero.1 (Submodule.coe_eq_zero.1 h0)
  have hms : Function.Surjective m := Submodule.Quotient.mk_surjective _
  have hE : Function.Injective E.toIntertwiningMap := by
    intro x y hxy
    rw [← E.symm_apply_apply x, ← E.symm_apply_apply y]
    exact congrArg E.symm hxy
  have hEs : Function.Surjective E.toIntertwiningMap := fun y => ⟨E.symm y, E.apply_symm_apply y⟩
  let f := E.toIntertwiningMap.comp m
  have bij : Function.Bijective f := ⟨hE.comp hm, hEs.comp hms⟩
  exact ⟨Representation.Equiv.mk' f (Function.surjInv bij.2) (Function.leftInverse_surjInv bij)
    (Function.rightInverse_surjInv bij.2)⟩

theorem central_dichotomy {μ : Representation ℂ G V} {τ : Representation ℂ G Y} {ρ : Representation ℂ G Y'}
    (X : Subrepresentation μ) (a : X.toRepresentation.Equiv τ) (q : μ.IntertwiningMap ρ)
    (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule) (z : G) (hz : ∀ g, g * z = z * g) (c : ℂ)
    (hc : ∀ y, ρ z y = c • y) :
    (∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0) ∨ ∀ v, μ z v = c • v := by
  have hcomm : ∀ (g : G) (v : V), μ z (μ g v) = μ g (μ z v) := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, ← hz g, map_mul, Module.End.mul_apply]
  have hD : ∀ v : V, μ z v - c • v ∈ X.toSubmodule := by
    intro v
    rw [← hq, map_sub, map_smul, Representation.IntertwiningMap.isIntertwining _ _ q, hc, sub_self]
  let P : V →ₗ[ℂ] X.toSubmodule :=
    LinearMap.codRestrict X.toSubmodule (μ z - c • LinearMap.id) (fun v => hD v)
  have hP : ∀ v, (P v : V) = μ z v - c • v := fun v => rfl
  have hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v) := by
    intro g v
    apply Subtype.ext
    rw [hP]
    show μ z (μ g v) - c • μ g v = μ g (P v : V)
    rw [hP, map_sub, map_smul, hcomm]
  let φL : V →ₗ[ℂ] Y := a.toIntertwiningMap.toLinearMap ∘ₗ P
  have hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v) := by
    intro g v
    show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))
    rw [hPg]
    exact Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)
  by_cases hex : ∃ v, φL v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    exact Or.inl ⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, v, hv⟩
  · push_neg at hex
    right
    intro v
    have h1 : P v = 0 := by
      rw [← a.symm_apply_apply (P v)]
      change a.symm (φL v) = 0
      rw [hex v]
      exact map_zero a.symm.toIntertwiningMap
    have h2 : (P v : V) = 0 := by rw [h1]; rfl
    rw [hP] at h2
    exact sub_eq_zero.1 h2

def imageSub (ψ : H →* G) (A : Representation ℂ H W₀) (μ : Representation ℂ G V)
    (hdec : ∀ g, ∃ (h : H) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x) : Subrepresentation μ where
  toSubmodule := Submodule.span ℂ {u | ∃ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w = u}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h, g', rfl, hg'⟩ := hdec g
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ι, w, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨μ g' ∘ₗ ι.toLinearMap, fun x => LinearMap.ext fun w => ?_⟩, A h w, ?_⟩
      · show μ g' (ι (A x w)) = μ (ψ x) (μ g' (ι w))
        have h1 : ι (A x w) = μ (ψ x) (ι w) := ι.isIntertwining _ _ x w
        rw [h1, ← Module.End.mul_apply, ← map_mul, ← hg', map_mul, Module.End.mul_apply]
      · show μ g' (ι (A h w)) = μ (ψ h * g') (ι w)
        have h1 : ι (A h w) = μ (ψ h) (ι w) := ι.isIntertwining _ _ h w
        rw [h1, ← Module.End.mul_apply, ← map_mul, ← hg']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (μ (ψ h * g'))]
      exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem exists_map_of_image (ψ : H →* G) {A : Representation ℂ H W₀} {B : Representation ℂ H W₁}
    (hB : B.IsIrreducible) (hAB : ¬ IsSubquotient B A) {μ : Representation ℂ G V} {τ : Representation ℂ G Y}
    {ρ : Representation ℂ G Y'} (hτ : τ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (X : Subrepresentation μ) (a : X.toRepresentation.Equiv τ) (q : μ.IntertwiningMap ρ)
    (hqs : Function.Surjective q) (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule)
    (hBτ : IsSubquotient B (τ.comp ψ : Representation ℂ H Y))
    (ι₀ : A.IntertwiningMap (μ.comp ψ)) (hι₀ : ι₀ ≠ 0)
    (hdec : ∀ g, ∃ (h : H) (g' : G), g = ψ h * g' ∧ ∀ x, ψ x * g' = g' * ψ x) :
    ∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  classical
  haveI := hτ
  haveI := hρ
  let W' := imageSub ψ A μ hdec
  have hWspan : W'.toSubmodule =
      Submodule.span ℂ {u | ∃ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w = u} := rfl
  have hmemW : ∀ (ι : A.IntertwiningMap (μ.comp ψ)) (w : W₀), ι w ∈ W'.toSubmodule :=
    fun ι w => Submodule.subset_span ⟨ι, w, rfl⟩
  let P' : Subrepresentation τ :=
    { toSubmodule := W'.toSubmodule.comap (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap)
      apply_mem_toSubmodule := by
        intro g y hy
        rw [Submodule.mem_comap] at hy ⊢
        show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) ∈ W'.toSubmodule
        rw [Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]
        exact W'.apply_mem_toSubmodule g hy }
  rcases eq_bot_or_eq_top P' with hP | hP
  · have hXW0 : ∀ x : V, x ∈ X.toSubmodule → x ∈ W'.toSubmodule → x = 0 := by
      intro x hx hxW
      have h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule := by
        rw [Submodule.mem_comap]
        show ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule
        rw [a.symm_apply_apply]
        exact hxW
      rw [hP] at h1
      have h2 : a ⟨x, hx⟩ = 0 := (Submodule.mem_bot ℂ).1 h1
      have h3 : (⟨x, hx⟩ : X.toSubmodule) = 0 := by
        rw [← a.symm_apply_apply ⟨x, hx⟩, h2]
        exact map_zero a.symm.toIntertwiningMap
      exact congrArg Subtype.val h3
    have hqW : ∀ w1 w2 : V, w1 ∈ W'.toSubmodule → w2 ∈ W'.toSubmodule → q w1 = q w2 → w1 = w2 := by
      intro w1 w2 h1 h2 h12
      have h3 : w1 - w2 ∈ X.toSubmodule := by rw [← hq, map_sub, h12, sub_self]
      exact sub_eq_zero.1 (hXW0 _ h3 (W'.toSubmodule.sub_mem h1 h2))
    let incl : W'.toRepresentation.IntertwiningMap μ :=
      ⟨W'.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
    let r := q.comp incl
    have hι : ∃ w, ι₀ w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hι₀ (Representation.IntertwiningMap.ext (LinearMap.ext hcon))
    obtain ⟨w0, hw0⟩ := hι
    have hrange : r.range = ⊤ := by
      rcases eq_bot_or_eq_top r.range with h | h
      · exfalso
        have hm : r ⟨ι₀ w0, hmemW ι₀ w0⟩ ∈ r.range.toSubmodule := LinearMap.mem_range_self r.toLinearMap _
        rw [h] at hm
        have h0 : q (ι₀ w0) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact hw0 (hXW0 _ ((hq _).1 h0) (hmemW ι₀ w0))
      · exact h
    have hrs : Function.Surjective r := by
      intro y
      have hy : y ∈ r.range.toSubmodule := by rw [hrange]; exact Submodule.mem_top
      obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hy
      exact ⟨x, hx⟩
    have hri : Function.Injective r := by
      intro x1 x2 h12
      exact Subtype.ext (hqW _ _ x1.2 x2.2 h12)
    let e : W'.toSubmodule ≃ₗ[ℂ] Y' := LinearEquiv.ofBijective r.toLinearMap ⟨hri, hrs⟩
    let s : V →ₗ[ℂ] V := W'.toSubmodule.subtype ∘ₗ e.symm.toLinearMap ∘ₗ q.toLinearMap
    have hsW : ∀ v, s v ∈ W'.toSubmodule := fun v => (e.symm (q v)).2
    have hqs' : ∀ v, q (s v) = q v := by
      intro v
      show r (e.symm (q v)) = q v
      exact e.apply_symm_apply (q v)
    have hsg : ∀ (g : G) (v : V), s (μ g v) = μ g (s v) := by
      intro g v
      apply hqW _ _ (hsW _) (W'.apply_mem_toSubmodule g (hsW v))
      rw [hqs', Representation.IntertwiningMap.isIntertwining _ _ q,
        Representation.IntertwiningMap.isIntertwining _ _ q, hqs']
    have hPX : ∀ v, v - s v ∈ X.toSubmodule := by
      intro v
      rw [← hq, map_sub, hqs', sub_self]
    let P : V →ₗ[ℂ] X.toSubmodule :=
      LinearMap.codRestrict X.toSubmodule (LinearMap.id - s) (fun v => hPX v)
    let φL : V →ₗ[ℂ] Y := a.toIntertwiningMap.toLinearMap ∘ₗ P
    have hPg : ∀ (g : G) (v : V), P (μ g v) = X.toRepresentation g (P v) := by
      intro g v
      apply Subtype.ext
      show μ g v - s (μ g v) = μ g (v - s v)
      rw [hsg, map_sub]
    have hφ : ∀ (g : G) (v : V), φL (μ g v) = τ g (φL v) := by
      intro g v
      show a.toIntertwiningMap (P (μ g v)) = τ g (a.toIntertwiningMap (P v))
      rw [hPg]
      exact Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g (P v)
    have hY : ∃ y : Y, y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      ext y
      rw [hcon y]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    obtain ⟨y, hy⟩ := hY
    refine ⟨φL.intertwiningMap_of_isIntertwiningMap μ τ hφ, ((a.symm y : X.toSubmodule) : V), ?_⟩
    show a.toIntertwiningMap (P _) ≠ 0
    have hq0 : q ((a.symm y : X.toSubmodule) : V) = 0 := (hq _).2 (a.symm y).2
    have hs0 : s ((a.symm y : X.toSubmodule) : V) = 0 := by
      show ((e.symm (q _) : W'.toSubmodule) : V) = 0
      rw [hq0, map_zero]
      rfl
    have hP0 : P ((a.symm y : X.toSubmodule) : V) = a.symm y := by
      apply Subtype.ext
      show ((a.symm y : X.toSubmodule) : V) - s ((a.symm y : X.toSubmodule) : V) = ((a.symm y : X.toSubmodule) : V)
      rw [hs0, sub_zero]
    rw [hP0]
    change a (a.symm y) ≠ 0
    rw [a.apply_symm_apply]
    exact hy
  · exfalso
    apply hAB
    have hXW : ∀ x ∈ X.toSubmodule, x ∈ W'.toSubmodule := by
      intro x hx
      have h1 : a ⟨x, hx⟩ ∈ P'.toSubmodule := by rw [hP]; exact Submodule.mem_top
      rw [Submodule.mem_comap] at h1
      have h2 : ((a.symm (a ⟨x, hx⟩) : X.toSubmodule) : V) ∈ W'.toSubmodule := h1
      rw [a.symm_apply_apply] at h2
      exact h2
    let f : τ.IntertwiningMap W'.toRepresentation :=
      ⟨LinearMap.codRestrict W'.toSubmodule (X.toSubmodule.subtype ∘ₗ a.symm.toIntertwiningMap.toLinearMap)
        (fun y => hXW _ (a.symm y).2), fun g => by
          refine LinearMap.ext fun y => ?_
          apply Subtype.ext
          show ((a.symm.toIntertwiningMap (τ g y) : X.toSubmodule) : V) =
            μ g ((a.symm.toIntertwiningMap y : X.toSubmodule) : V)
          rw [Representation.IntertwiningMap.isIntertwining _ _ a.symm.toIntertwiningMap g y]
          rfl⟩
    have hfi : Function.Injective f := by
      intro y1 y2 h12
      have h4 : ((f y1 : W'.toSubmodule) : V) = ((f y2 : W'.toSubmodule) : V) := congrArg Subtype.val h12
      have h3 : a.symm y1 = a.symm y2 := Subtype.ext h4
      rw [← a.apply_symm_apply y1, ← a.apply_symm_apply y2, h3]
    have hsub1 : IsSubquotient τ W'.toRepresentation := GlobalTheory.SmGL.IsSubquotient.of_injective f hfi
    have hsub2 := GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hsub1 ψ
    have hsub3 := GlobalTheory.SmGL.IsSubquotient.trans hBτ hsub2
    have hspan : Submodule.span ℂ {u : W'.toSubmodule |
        ∃ (ι : A.IntertwiningMap (W'.toRepresentation.comp ψ)) (w : W₀), ι w = u} = ⊤ := by
      apply Submodule.map_injective_of_injective W'.toSubmodule.injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top]
      refine Eq.trans ?_ hWspan.symm
      congr 1
      ext u
      constructor
      · rintro ⟨u', ⟨ι, w, rfl⟩, rfl⟩
        refine ⟨⟨W'.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩
        exact congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ ι g w')
      · rintro ⟨ι, w, rfl⟩
        refine ⟨⟨ι w, hmemW ι w⟩, ⟨⟨LinearMap.codRestrict W'.toSubmodule ι.toLinearMap (fun w' => hmemW ι w'),
          fun g => LinearMap.ext fun w' => ?_⟩, w, rfl⟩, rfl⟩
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining _ _ ι g w'
    exact GlobalTheory.LocGL.SupportUnique.isSubquotient_of_span hB hsub3 hspan

theorem eq_of_subsingleton_step {μ : Representation ℂ G V} {A B : Subrepresentation μ} (hBA : B ≤ A)
    (h : Subsingleton (A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype)) : A = B := by
  refine le_antisymm (fun x hx => ?_) hBA
  have h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : A.toSubmodule ⧸ B.toSubmodule.comap A.toSubmodule.subtype) = 0 :=
    Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem eq_of_steps {μ : Representation ℂ G V} {N : ℕ} (S : Fin (N + 1) → Subrepresentation μ) (hS : Monotone S)
    (i j : Fin (N + 1)) (hij : i ≤ j)
    (h : ∀ t : Fin N, i ≤ t.castSucc → t.succ ≤ j → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)) : S i = S j := by
  have hij' : i.val ≤ j.val := hij
  have key : ∀ k : ℕ, ∀ hk : i.val + k < N + 1, i.val + k ≤ j.val → S i = S ⟨i.val + k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk _
      rfl
    | succ k ih =>
      intro hk hkj
      have hk' : i.val + k < N := by omega
      rw [ih (by omega) (by omega)]
      have hst := h ⟨i.val + k, hk'⟩ (by rw [Fin.le_def]; exact Nat.le_add_right _ _)
        (by rw [Fin.le_def]; show i.val + k + 1 ≤ j.val; omega)
      have e := eq_of_subsingleton_step (hS (Fin.castSucc_le_succ (⟨i.val + k, hk'⟩ : Fin N))) hst
      exact e.symm
  rw [key (j.val - i.val) (by omega) (by omega)]
  congr 1
  apply Fin.ext
  show i.val + (j.val - i.val) = j.val
  omega

theorem exists_map_of_top {μ : Representation ℂ G V} {τ : Representation ℂ G Y} [Nontrivial Y] {N : ℕ}
    (S : Fin (N + 1) → Subrepresentation μ) (hS : Monotone S) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N)
    (h : ∀ t : Fin N, t₀ < t → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype))
    (E : (subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) : ∃ (φ : μ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  have htop : S t₀.succ = ⊤ := by
    rw [← hN]
    apply eq_of_steps S hS t₀.succ (Fin.last N) (Fin.le_last _)
    intro t ht1 _
    apply h t
    have h2 : t₀.val + 1 ≤ t.val := ht1
    exact (show t₀.val < t.val by omega)
  obtain ⟨q, hqs, _⟩ := exists_quot_map (S t₀.castSucc) (S t₀.succ) htop E
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hqs y
  exact ⟨q, v, hy⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.OneBlockCell GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.LocGL GlobalTheory.LocGL.SupportUnique

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cell_antidiag (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i))
    (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))))
    (h00 : b.1 0 0 = 0) (h11 : b.1 1 1 = 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have hrz : ∀ i j, j ≠ Equiv.swap 0 1 i → b.1 i j = 0 := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hcz : ∀ j i, i ≠ Equiv.swap 0 1 j → b.1 i j = 0 := by
    intro j i hi
    fin_cases i <;> fin_cases j <;> simp_all
  have hrf : ∀ i, b.1 i (Equiv.swap 0 1 i) = d i := by
    intro i
    fin_cases i <;> simp <;> omega
  have hcf : ∀ j, b.1 (Equiv.swap 0 1 j) j = d (Equiv.swap 0 1 j) := by
    intro j
    fin_cases j <;> simp <;> omega
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    valEquiv (Equiv.swap 0 1 i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j)) := fun j =>
    valEquiv (Equiv.swap 0 1 j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (Equiv.swap 0 1 j) =
        (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a (by rwa [Equiv.swap_apply_self])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a' (by rwa [Equiv.swap_apply_self])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl

  have hsm : IsSmooth (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) :=
    isSmooth_piTensor fun j => (σ (Equiv.swap 0 1 j)).smooth
  let R := PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)
  let Ψ : (⨂[ℂ] j, (σ (Equiv.swap 0 1 j)).V) ≃ₗ[ℂ]
      Jacquet (piTensor fun i => (σ i).π) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (GlobalTheory.SmGL.twist ((relJac f (piTensor fun i => (σ i).π)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [reindex_piTensor σ _ (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)
      (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π).IntertwiningMap
      (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u), fun p x => by
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (y * x) u) =
            Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x
            ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) h u)) =
          Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem row_unique (hG : GeometricLemma) {d d' : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i))
    (hσ : ∀ i, IsCuspidal (σ i).π) {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d' j))
    {Z : Type} [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]
    {κ : Representation ℂ (Levi k fun j => Fin (d' j)) Z}
    (E : κ.Equiv (cellFunctor f g (piTensor fun i => (σ i).π))) (i j j' : Fin 2)
    (hj : 0 < b i j) (hj' : 0 < b i j') : j = j' := by
  obtain ⟨Y, _, _, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ κ inferInstance
  have hs' : IsSubquotient υ (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  have hsm : IsSmooth υ := hs'.isSmooth (isSmooth_relInd _ _)
  obtain ⟨s, hrow, -⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (σ i).smooth)
    (fun i => hasFiniteLength_of_isIrreducible (σ i).irr) hυ hsm (jhMult_ne_zero_iff.2 hs')
  exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k (d i) _ (σ i).π 2 (b i) (f i) _ (fun j => (s i j).ρ) (hσ i)
    (fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (s i j).irr) (hrow i) j j' hj hj'

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r y =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    calc
      _ = (PiTensorProduct.tprod ℂ) (fun a => c a • y a) := by congr 1; funext a; exact h a _
      _ = _ := MultilinearMap.map_smul_univ _ _ _

theorem exists_map_two_step (hBZ : BernsteinZelevinskyFiniteness) {D : ℕ} (hD : 0 < D) (σ : Fin 2 → Irr k D)
    (hc : ∀ i, IsCuspidal (σ i).π) (hne : ¬ Nonempty ((σ 0).π.Equiv (σ 1).π)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {μ : Representation ℂ (Levi k fun _ : Fin 2 => Fin D) V} (hμ : IsSmooth μ) (X : Subrepresentation μ)
    (a : X.toRepresentation.Equiv (piTensor fun j => (σ (Equiv.swap 0 1 j)).π))
    (q : μ.IntertwiningMap (piTensor fun i => (σ i).π)) (hqs : Function.Surjective q)
    (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule) :
    ∃ (φ : μ.IntertwiningMap (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) (v : V), φ v ≠ 0 := by
  let ψ : GL (Fin D) k →* Levi k (fun _ : Fin 2 => Fin D) := MonoidHom.mulSingle (fun _ : Fin 2 => GL (Fin D) k) 0
  have hirr : ∀ (s : Fin 2 → Irr k D), (piTensor fun j => (s j).π).IsIrreducible := fun s =>
    GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin 2) (fun _ => Fin D)
      (fun j => ⟨(s j).V, (s j).π, (s j).smooth, (s j).irr⟩)
  choose ω _ hω using fun i => exists_smooth_hasCentralChar (σ i).smooth (σ i).irr
  have hcent : ∀ (z : kˣ) (g : Levi k (fun _ : Fin 2 => Fin D)),
      g * ψ (GeneralLinearGroup.scalar _ z) = ψ (GeneralLinearGroup.scalar _ z) * g := by
    intro z g
    funext i
    by_cases hi : i = 0
    · subst hi
      have hcm : g 0 * GeneralLinearGroup.scalar (Fin D) z = GeneralLinearGroup.scalar (Fin D) z * g 0 := by
        ext i j
        simp [GeneralLinearGroup.scalar, mul_comm]
      simpa [ψ] using hcm
    · simp [ψ, Pi.mulSingle_eq_of_ne hi]
  have hρz : ∀ (z : kˣ) y, (piTensor fun i => (σ i).π) (ψ (GeneralLinearGroup.scalar _ z)) y = (ω 0 z : ℂ) • y := by
    intro z y
    have h1 := piTensor_scalar (fun i => (σ i).π) (ψ (GeneralLinearGroup.scalar _ z))
      (fun i => if i = 0 then (ω 0 z : ℂ) else 1) (fun i v => by
        by_cases hi : i = 0
        · subst hi
          simpa [ψ] using hω 0 z v
        · simp [ψ, Pi.mulSingle_eq_of_ne hi, hi]) y
    simpa [Fin.prod_univ_two] using h1
  by_cases hsc : ∀ (z : kˣ) v, μ (ψ (GeneralLinearGroup.scalar _ z)) v = (ω 0 z : ℂ) • v
  · have hsub : IsSubquotient (σ 0).π (μ.comp ψ : Representation ℂ (GL (Fin D) k) V) :=
      (GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun i => (σ i).π) (fun i => (σ i).irr) 0).trans
        (isSubquotient_comp (.of_surjective q hqs) ψ)
    have hsm : IsSmooth (μ.comp ψ : Representation ℂ (GL (Fin D) k) V) :=
      isSmooth_comp hμ _ (continuous_mulSingle (A := fun _ : Fin 2 => GL (Fin D) k) 0)
    obtain ⟨ι, hι⟩ := exists_map_of_isCuspidal hD (σ 0).irr (hc 0) hsm (fun z => ⟨_, hsc z⟩) hsub
    refine exists_map_of_image ψ (σ 1).irr (fun h => ?_) (hirr _) (hirr σ) X a q hqs hq ?_ ι hι ?_
    · obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient (σ 1).irr (σ 0).irr h
      exact hne ⟨φ⟩
    · exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (σ (Equiv.swap 0 1 j)).π)
        (fun j => (σ (Equiv.swap 0 1 j)).irr) 0
    · intro g
      refine ⟨g 0, Pi.mulSingle 1 (g 1), ?_, fun x => ?_⟩
      · funext i
        fin_cases i <;> simp [ψ]
      · funext i
        fin_cases i <;> simp [ψ]
  · push_neg at hsc
    obtain ⟨z, v, hv⟩ := hsc
    rcases central_dichotomy X a q hq _ (hcent z) _ (hρz z) with h | h
    · exact h
    · exact absurd (h v) hv


variable (k) in
theorem exists_jac_map_of_ne (hG : GeometricLemma) (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ)
    (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π) (hd : d 0 ≠ d 1)
    (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n) :
    ∃ (φ : (GlobalTheory.SmGL.jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
  obtain ⟨N, b, hb⟩ := (hG k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![d 1, 0]] := ⟨⟨![![0, d 0], ![d 1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  have hstep : ∀ t, t ≠ b.symm G0 → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype) := by
    intro t ht
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    have hrow := row_unique (d' := fun j => d (Equiv.swap 0 1 j)) hG σ (fun i => (hσ i).2) _ _ E
    have a1 : ¬ (0 < (b t).1 0 0 ∧ 0 < (b t).1 0 1) := fun h => absurd (hrow 0 0 1 h.1 h.2) (by decide)
    have a2 : ¬ (0 < (b t).1 1 0 ∧ 0 < (b t).1 1 1) := fun h => absurd (hrow 1 0 1 h.1 h.2) (by decide)
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_antidiag d σ (b (b.symm G0)) (by rw [Equiv.apply_symm_apply, hG0]; rfl)
    (by rw [Equiv.apply_symm_apply, hG0]; rfl)
  haveI : Nontrivial (⨂[ℂ] i, (σ (Equiv.swap 0 1 i)).V) := GlobalTheory.ProdSupport.nontrivial_piTensor _
    fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr
  exact exists_map_of_top S hmono hN (b.symm G0) (fun t ht => hstep t ht.ne')
    ((h4 (b.symm G0) f₀ g₀).some.trans E₀)


set_option maxHeartbeats 2000000 in
variable (k) in
theorem exists_jac_map_of_eq (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (n : Type) [Fintype n]
    [DecidableEq n] {D : ℕ} (hD : 0 < D) (σ : Fin 2 → Irr k D) (hc : ∀ i, IsCuspidal (σ i).π)
    (hne : ¬ Nonempty ((σ 0).π.Equiv (σ 1).π)) (e e' : (Σ _ : Fin 2, Fin D) ≃ n) :
    ∃ (φ : (GlobalTheory.SmGL.jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
  obtain ⟨N, b, hb⟩ := (hG k).1 (Fin 2) (Fin 2) n (fun _ => Fin D) (fun _ => Fin D) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D),
      G0.1 = ![![0, D], ![D, 0]] := ⟨⟨![![0, D], ![D, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D),
      G1.1 = ![![D, 0], ![0, D]] := ⟨⟨![![D, 0], ![0, D]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  have hstep : ∀ t, t ≠ b.symm G0 → t ≠ b.symm G1 → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype) := by
    intro t ht ht'
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    have hrow := row_unique (d := fun _ => D) (d' := fun _ => D) hG σ hc _ _ E
    have a1 : ¬ (0 < (b t).1 0 0 ∧ 0 < (b t).1 0 1) := fun h => absurd (hrow 0 0 1 h.1 h.2) (by decide)
    have a2 : ¬ (0 < (b t).1 1 0 ∧ 0 < (b t).1 1 1) := fun h => absurd (hrow 1 0 1 h.1 h.2) (by decide)
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin] at r1 c0 r0 c1
    by_cases h00 : (b t).1 0 0 = 0
    · apply ht
      rw [Equiv.eq_symm_apply]
      apply Subtype.ext
      funext i j
      rw [hG0]
      fin_cases i <;> fin_cases j <;> simp <;> omega
    · apply ht'
      rw [Equiv.eq_symm_apply]
      apply Subtype.ext
      funext i j
      rw [hG1]
      fin_cases i <;> fin_cases j <;> simp <;> omega
  have h01 : b.symm G0 ≠ b.symm G1 := fun h => by
    have h1 := congrArg (fun G : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D) => G.1 0 0)
      (b.symm.injective h)
    simp only [hG0, hG1] at h1
    simp at h1
    omega
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_antidiag (fun _ => D) σ (b (b.symm G0)) (by rw [Equiv.apply_symm_apply, hG0]; rfl)
    (by rw [Equiv.apply_symm_apply, hG0]; rfl)
  have hsm : IsSmooth (piTensor fun i => (σ i).π) := isSmooth_piTensor fun i => (σ i).smooth
  obtain ⟨f₁, g₁, ⟨E₁⟩⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.cell_diag (k := k) (b (b.symm G1)) (fun i j hj => by
    rw [Equiv.apply_symm_apply, hG1]
    fin_cases i <;> fin_cases j <;> simp_all) (piTensor fun i => (σ i).π) hsm
  have F₀ := (h4 (b.symm G0) f₀ g₀).some.trans E₀
  have F₁ := (h4 (b.symm G1) f₁ g₁).some.trans E₁
  haveI : Nontrivial (⨂[ℂ] i, (σ (Equiv.swap 0 1 i)).V) := GlobalTheory.ProdSupport.nontrivial_piTensor _
    fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr
  rcases lt_or_gt_of_ne h01 with hlt | hlt
  · have hlow : S (b.symm G0).castSucc = ⊥ := (eq_of_steps S hmono 0 _ (Fin.zero_le _) fun t h1 h2 =>
      hstep t (by
        rintro rfl
        exact absurd h2 (by simp [Fin.le_def]))
        (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h2
        have h3 : (b.symm G0).val < (b.symm G1).val := hlt
        omega)).symm.trans h0
    have hmid : S (b.symm G0).succ = S (b.symm G1).castSucc := eq_of_steps S hmono _ _
      (by simpa [Fin.le_def] using Nat.succ_le_of_lt hlt) fun t h1 h2 => hstep t (by
        rintro rfl
        have : (b.symm G0).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h1
        omega) (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G1).val := by simpa [Fin.le_def] using h2
        omega)
    have htop : S (b.symm G1).succ = ⊤ := (eq_of_steps S hmono _ _ (Fin.le_last _) fun t h1 _ => hstep t (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h1
        have h3 : (b.symm G0).val < (b.symm G1).val := hlt
        omega) (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G1).val := by simpa [Fin.le_def] using h1
        omega)).trans hN
    obtain ⟨a⟩ := exists_sub_equiv _ _ hlow F₀
    obtain ⟨q, hqs, hq⟩ := exists_quot_map _ _ htop F₁
    exact exists_map_two_step hBZ hD σ hc hne (isSmooth_jac e' (isSmooth_parInd _ _)) _ a q hqs
      (fun v => by rw [hmid]; exact hq v)
  · exact exists_map_of_top S hmono hN (b.symm G0) (fun t ht => hstep t ht.ne' (by
      rintro rfl
      exact absurd ht (not_lt.2 (le_of_lt hlt)))) F₀

theorem swap_equiv_of_irreducible : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, GlobalTheory.SplitRead.Irr k (d i)), (∀ i, 0 < d i ∧ GlobalTheory.SmGL.IsCuspidal (σ i).π) → GlobalTheory.LocGL.IrrGL.of (σ 0).π (σ 0).smooth (σ 0).irr ≠ GlobalTheory.LocGL.IrrGL.of (σ 1).π (σ 1).smooth (σ 1).irr → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), (GlobalTheory.SmGL.multiProd e fun i => (σ i).π).IsIrreducible → (GlobalTheory.SmGL.multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π).IsIrreducible → Nonempty ((GlobalTheory.SmGL.multiProd e fun i => (σ i).π).Equiv (GlobalTheory.SmGL.multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hG hBZ k _ _ _ _ n _ _ d σ hσ hne e e' h1 h2
  have key : ∃ (φ : (GlobalTheory.SmGL.jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
    by_cases hd : d 0 = d 1
    · obtain ⟨D, rfl⟩ : ∃ D, d = fun _ => D := ⟨d 0, funext fun i => by
        fin_cases i
        · rfl
        · exact hd.symm⟩
      exact exists_jac_map_of_eq k hG hBZ n (hσ 0).1 σ (fun i => (hσ i).2)
        (fun ⟨φ⟩ => hne (IrrGL.of_eq_of.2 ⟨φ⟩)) e e'
    · exact exists_jac_map_of_ne k hG n d σ hσ hd e e'
  obtain ⟨φ, x, hx⟩ := key
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact GlobalTheory.SwapTwo.nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

end
