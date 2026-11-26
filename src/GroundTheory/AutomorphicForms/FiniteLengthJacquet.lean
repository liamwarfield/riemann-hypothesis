module

public import GroundTheory.AutomorphicForms.GeometricLemma

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.FiniteLengthSubquotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function Parabolic

universe u

section Subquotient

variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]

def IsSubquotient (π : Representation ℂ G W) (ρ : Representation ℂ G V) : Prop :=
  ∃ C : Subrepresentation ρ, ∃ p : Representation.IntertwiningMap C.toRepresentation π,
    Surjective p

variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}

def subrepInclusion (C : Subrepresentation ρ) :
    Representation.IntertwiningMap C.toRepresentation ρ where
  toLinearMap := C.toSubmodule.subtype
  isIntertwining' _ := rfl

theorem IsSubquotient.of_injective_of_surjective {X : Type*} [AddCommGroup X] [Module ℂ X]
    {α : Representation ℂ G X} (i : Representation.IntertwiningMap α ρ) (hi : Injective i)
    (q : Representation.IntertwiningMap α π) (hq : Surjective q) : IsSubquotient π ρ := by
  let e : X ≃ₗ[ℂ] LinearMap.range i.toLinearMap := LinearEquiv.ofInjective i.toLinearMap hi
  let R : Subrepresentation ρ := ⟨LinearMap.range i.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨α g x, Representation.IntertwiningMap.isIntertwining _ _ i g x⟩⟩
  have he : ∀ x, ((e x : LinearMap.range i.toLinearMap) : V) = i x := fun x => rfl
  refine ⟨R, ⟨q.toLinearMap ∘ₗ e.symm.toLinearMap, fun g => ?_⟩, ?_⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : R.toRepresentation g (e x) = e (α g x) := by
      apply Subtype.ext
      show ρ g ((e x : LinearMap.range i.toLinearMap) : V) = _
      rw [he, he]
      exact (Representation.IntertwiningMap.isIntertwining _ _ i g x).symm
    simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe, h1,
      LinearEquiv.symm_apply_apply, Representation.IntertwiningMap.toLinearMap_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ q g x
  · intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨e x, by simp⟩

theorem IsSubquotient.of_surjective (q : Representation.IntertwiningMap ρ π) (hq : Surjective q) :
    IsSubquotient π ρ :=
  .of_injective_of_surjective (Representation.IntertwiningMap.id ρ) injective_id q hq

theorem IsSubquotient.of_injective (i : Representation.IntertwiningMap π ρ) (hi : Injective i) :
    IsSubquotient π ρ :=
  .of_injective_of_surjective i hi (Representation.IntertwiningMap.id π) surjective_id

theorem IsSubquotient.trans (h₁ : IsSubquotient π ρ) (h₂ : IsSubquotient ρ θ) :
    IsSubquotient π θ := by
  obtain ⟨C, p, hp⟩ := h₁
  obtain ⟨D, q, hq⟩ := h₂

  let E : Subrepresentation D.toRepresentation := subrepComap q C
  let qE : E.toSubmodule →ₗ[ℂ] C.toSubmodule :=
    { toFun := fun e => ⟨q e, e.2⟩
      map_add' := fun _ _ => Subtype.ext (map_add q _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul q _ _) }
  refine .of_injective_of_surjective ((subrepInclusion D).comp (subrepInclusion E))
    (fun x y h => Subtype.ext (Subtype.ext h))
    (p.comp ⟨qE, fun g => LinearMap.ext fun e =>
        Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ q g e)⟩) ?_
  intro y
  obtain ⟨c, rfl⟩ := hp y
  obtain ⟨d, hd⟩ := hq c
  exact ⟨⟨d, show q d ∈ C from hd ▸ c.2⟩, by
    show p ⟨q d, _⟩ = p c
    congr 1
    exact Subtype.ext hd⟩

theorem IsSubquotient.subsingleton [Subsingleton V] (h : IsSubquotient π ρ) : Subsingleton W := by
  obtain ⟨C, p, hp⟩ := h
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hp a
  obtain ⟨y, rfl⟩ := hp b
  rw [Subsingleton.elim x y]

theorem IsSubquotient.exists_piece [π.IsIrreducible] (h : IsSubquotient π ρ) {k : ℕ}
    (Vf : ℕ → Submodule ℂ V) (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥)
    (hk : Vf k = ⊤) {X : Fin k → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (σ : ∀ j, Representation ℂ G (X j))
    (Ψ : ∀ j : Fin k,
      Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) :
    ∃ j, IsSubquotient π (σ j) := by
  classical
  obtain ⟨C, p, hp⟩ := h

  have hex : ∃ j, j < k ∧ ∃ c : C.toSubmodule, (c : V) ∈ Vf (j + 1) ∧ p c ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
    obtain ⟨c, rfl⟩ := hp x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [h0] at hk
      have : (c : V) ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← hk, Submodule.mem_bot] at this
      exact hx (by rw [show c = 0 from Subtype.ext this, map_zero])
    refine ⟨k - 1, by omega, c, ?_, hx⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0), hk]
    trivial
  let j₀ := Nat.find hex
  obtain ⟨hj₀k, c₀, hc₀V, hc₀⟩ := Nat.find_spec hex
  have hbelow : ∀ c : C.toSubmodule, (c : V) ∈ Vf j₀ → p c = 0 := by
    intro c hc
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h, h0, Submodule.mem_bot] at hc
      rw [show c = 0 from Subtype.ext hc, map_zero]
    · by_contra hpc
      obtain ⟨m, hm⟩ : ∃ m, j₀ = m + 1 := ⟨j₀ - 1, by omega⟩
      exact Nat.find_min hex (m := m) (by omega) ⟨by omega, c, by rw [← hm]; exact hc, hpc⟩
  set j : Fin k := ⟨j₀, hj₀k⟩

  let D : Subrepresentation (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) :=
    ⟨C.toSubmodule.comap (Vf (j + 1)).subtype, fun g x hx => C.apply_mem_toSubmodule g hx⟩
  let toC : D.toSubmodule →ₗ[ℂ] C.toSubmodule :=
    { toFun := fun d => ⟨((d : Vf (j + 1)) : V), d.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let P : D.toSubmodule →ₗ[ℂ] W := p.toLinearMap ∘ₗ toC
  let Q : D.toSubmodule →ₗ[ℂ] X j := (Ψ j).toLinearMap ∘ₗ D.toSubmodule.subtype
  have hker : LinearMap.ker Q ≤ LinearMap.ker P := by
    intro d hd
    have : ((d : Vf (j + 1)) : V) ∈ Vf j₀ := (hΨ j d).1 hd
    exact hbelow _ this

  have hPsurj : Surjective P := by
    let R : Subrepresentation π := ⟨LinearMap.range P, by
      rintro g _ ⟨d, rfl⟩
      refine ⟨(D.toRepresentation g) d, ?_⟩
      show p (toC (D.toRepresentation g d)) = π g (p (toC d))
      rw [← Representation.IntertwiningMap.isIntertwining]
      rfl⟩
    have hR : R ≠ ⊥ := by
      intro hR
      have hmem : P ⟨⟨c₀, hc₀V⟩, c₀.2⟩ ∈ R.toSubmodule := ⟨_, rfl⟩
      rw [hR] at hmem
      exact hc₀ ((Submodule.mem_bot ℂ).1 hmem)
    have := (eq_bot_or_eq_top R).resolve_left hR
    intro y
    have hy : y ∈ R.toSubmodule := by rw [this]; trivial
    exact hy

  let E : Subrepresentation (σ j) := ⟨LinearMap.range Q, by
    rintro g _ ⟨d, rfl⟩
    refine ⟨(D.toRepresentation g) d, ?_⟩
    show Ψ j ((ρ.subrepresentation (Vf (j + 1)) (hV (j + 1)) g) d) = σ j g (Ψ j d)
    exact Representation.IntertwiningMap.isIntertwining _ _ (Ψ j) g d⟩
  let e := Q.quotKerEquivRange
  let lift : LinearMap.range Q →ₗ[ℂ] W :=
    (LinearMap.ker Q).liftQ P hker ∘ₗ e.symm.toLinearMap
  have hlift : ∀ d, lift (Q.rangeRestrict d) = P d := by
    intro d
    simp only [lift, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe]
    rw [show Q.rangeRestrict d = e (Submodule.Quotient.mk d) from rfl, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨j, E, ⟨lift, fun g => LinearMap.ext fun y => ?_⟩, fun y => ?_⟩
  · obtain ⟨d, rfl⟩ := Q.surjective_rangeRestrict y
    have h1 : (E.toRepresentation g (Q.rangeRestrict d) : LinearMap.range Q) =
        Q.rangeRestrict (D.toRepresentation g d) :=
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (Ψ j) g d).symm
    simp only [LinearMap.coe_comp, comp_apply]
    rw [h1, hlift, hlift]
    show p (toC (D.toRepresentation g d)) = π g (p (toC d))
    rw [← Representation.IntertwiningMap.isIntertwining]
    rfl
  · obtain ⟨d, rfl⟩ := hPsurj y
    exact ⟨Q.rangeRestrict d, hlift d⟩

end Subquotient

section Coinvariants

variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}


omit [TopologicalSpace G] in
theorem map_mem_coinvariantsKer {π : Representation ℂ G W} (p : Representation.IntertwiningMap ρ π)
    (N : Subgroup G) {x : V} (hx : x ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    p x ∈ Representation.Coinvariants.ker (π.comp N.subtype) := by
  have hle : Representation.Coinvariants.ker (ρ.comp N.subtype) ≤
      (Representation.Coinvariants.ker (π.comp N.subtype)).comap p.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, v⟩, rfl⟩
    simp only [MonoidHom.coe_comp, comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining]
    exact Representation.Coinvariants.sub_mem_ker (ρ := π.comp N.subtype) u (p v)
  exact hle hx

variable [IsTopologicalGroup G]

theorem isSmooth_subrep (hρ : IsSmooth ρ) (C : Subrepresentation ρ) :
    IsSmooth C.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : V))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg

theorem mem_ker_subrep_of_mem_ker (N : Subgroup G) [LocallyCompactSpace N] [T2Space N]
    [TotallyDisconnectedSpace N]
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hρ : IsSmooth ρ) (C : Subrepresentation ρ) {c : C.toSubmodule}
    (hc : (c : V) ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    c ∈ Representation.Coinvariants.ker (C.toRepresentation.comp N.subtype) := by
  let f : Representation.IntertwiningMap (C.toRepresentation.comp N.subtype)
      (C.toRepresentation.comp N.subtype) := 0
  let g : Representation.IntertwiningMap (C.toRepresentation.comp N.subtype) (ρ.comp N.subtype) :=
    ⟨C.toSubmodule.subtype, fun _ => rfl⟩
  have hfg : Exact f g := by
    intro y
    constructor
    · intro hy
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact (Subtype.ext hy).symm
    · rintro ⟨z, rfl⟩
      rfl
  have hex := exact_coinvariantsMap hN (isSmooth_comp_subtype (isSmooth_subrep hρ C) N)
    (isSmooth_comp_subtype hρ N) f g hfg
  have h1 : Representation.Coinvariants.map _ _ g (Representation.Coinvariants.mk _ c) = 0 := by
    rw [Representation.Coinvariants.map_mk]
    exact (Representation.Coinvariants.mk_eq_zero _).2 hc
  obtain ⟨z, hz⟩ := (hex _).1 h1
  have h0 : Representation.Coinvariants.map _ _ f z = 0 := by
    obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    rw [Representation.Coinvariants.map_mk]
    show Representation.Coinvariants.mk _ 0 = 0
    exact map_zero _
  rw [h0] at hz
  exact (Representation.Coinvariants.mk_eq_zero _).1 hz.symm

end Coinvariants

section Criterion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem hasFiniteLength_of_coinvariants {V : Type u} [AddCommGroup V] [Module ℂ V]
    {X : Representation ℂ G V} (hX : IsSmooth X) {ι : Type*} [Finite ι] (N : ι → Subgroup G)
    [∀ i, LocallyCompactSpace (N i)] [∀ i, T2Space (N i)] [∀ i, TotallyDisconnectedSpace (N i)]
    (hN : ∀ i (s : Finset (N i)), ∃ K : Subgroup (N i), IsCompact (K : Set (N i)) ∧
      IsOpen (K : Set (N i)) ∧ ∀ x ∈ s, x ∈ K)
    {M : ι → Type*} [∀ i, Group (M i)]
    (τ : ∀ i, Representation ℂ (M i) (Representation.Coinvariants (X.comp (N i).subtype)))
    (hτ : ∀ i m, ∃ g : G, ∃ c : ℂ, ∀ v, τ i m (Representation.Coinvariants.mk _ v) =
      c • Representation.Coinvariants.mk _ (X g v))
    (hfin : ∀ i, HasFiniteLength (τ i))
    (hfaith : ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
      [π.IsIrreducible], IsSmooth π → IsSubquotient π X →
        ∃ i, Nontrivial (Representation.Coinvariants (π.comp (N i).subtype))) :
    HasFiniteLength X := by
  classical
  have := fun i => (hfin i).wellFoundedLT
  have := fun i => (hfin i).wellFoundedGT
  let Λ : Subrepresentation X → ∀ i, Subrepresentation (τ i) := fun A i =>
    ⟨A.toSubmodule.map (Representation.Coinvariants.mk (X.comp (N i).subtype)), by
      rintro m _ ⟨v, hv, rfl⟩
      obtain ⟨g, c, hgc⟩ := hτ i m
      rw [hgc]
      exact Submodule.smul_mem _ c ⟨X g v, A.apply_mem_toSubmodule g hv, rfl⟩⟩
  have hmono : ∀ A B : Subrepresentation X, A ≤ B → ∀ i, Λ A i ≤ Λ B i :=
    fun A B h i _ ⟨v, hv, hvy⟩ => ⟨v, h hv, hvy⟩
  refine hasFiniteLength_of_strictMono Λ fun A B hAB => ?_
  rw [Pi.lt_def]
  refine ⟨hmono A B hAB.le, ?_⟩
  by_contra hne'
  have hne : ∀ i, ¬ Λ A i < Λ B i := fun i h => hne' ⟨i, h⟩
  have heq : ∀ i, Λ A i = Λ B i := fun i =>
    (lt_or_eq_of_le (hmono A B hAB.le i)).resolve_left (hne i)

  obtain ⟨x, hxB, hxA⟩ := SetLike.exists_of_lt hAB
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => X g x)
  have hS : ∀ g, S ≤ S.comap (X g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let Cs : Submodule ℂ V := A.toSubmodule ⊔ S
  have hCs : ∀ g, Cs ≤ Cs.comap (X g) := fun g => sup_le
    (fun v hv => Submodule.mem_sup_left (A.apply_mem_toSubmodule g hv))
    (fun v hv => Submodule.mem_sup_right (hS g hv))
  let C : Subrepresentation X := ⟨Cs, fun g v hv => hCs g hv⟩
  have hxC : x ∈ Cs := Submodule.mem_sup_right (Submodule.subset_span ⟨1, by simp⟩)
  have hCB : ∀ v ∈ Cs, v ∈ B := fun v hv => (sup_le (show A.toSubmodule ≤ B.toSubmodule from hAB.le)
    (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact B.apply_mem_toSubmodule g hxB))) hv
  let Y0 : Submodule ℂ Cs := A.toSubmodule.comap Cs.subtype
  have hY0 : ∀ g, Y0 ≤ Y0.comap (C.toRepresentation g) := fun g v hv =>
    A.apply_mem_toSubmodule g hv
  let Q := Representation.quotient C.toRepresentation Y0 hY0
  let q₀ : Cs ⧸ Y0 := Submodule.Quotient.mk ⟨x, hxC⟩
  have hq₀ : q₀ ≠ 0 := fun h => hxA ((Submodule.Quotient.mk_eq_zero Y0 (x := (⟨x, hxC⟩ : Cs))).1 h)
  have : Nontrivial (Cs ⧸ Y0) := ⟨⟨q₀, 0, hq₀⟩⟩
  have hgen : Submodule.span ℂ {y | ∃ g, ∃ s ∈ ({q₀} : Finset (Cs ⧸ Y0)), y = Q g s} = ⊤ := by
    set T := Submodule.span ℂ {y | ∃ g, ∃ s ∈ ({q₀} : Finset (Cs ⧸ Y0)), y = Q g s}
    have hle : Cs ≤ (T.comap Y0.mkQ).map Cs.subtype := by
      refine sup_le (fun a ha => ⟨⟨a, Submodule.mem_sup_left ha⟩, ?_, rfl⟩)
        (Submodule.span_le.2 ?_)
      · show Submodule.Quotient.mk _ ∈ T
        rw [(Submodule.Quotient.mk_eq_zero Y0 (x := (⟨a, Submodule.mem_sup_left ha⟩ : Cs))).2 ha]
        exact T.zero_mem
      · rintro _ ⟨g, rfl⟩
        refine ⟨⟨X g x, hCs g hxC⟩, Submodule.subset_span ⟨g, q₀, Finset.mem_singleton_self _, rfl⟩,
          rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective Y0 y
    obtain ⟨c', hc', hcc'⟩ := hle c.2
    rw [show c = c' from Subtype.ext hcc'.symm]
    exact hc'
  obtain ⟨Z, hZ, hirr⟩ := exists_irreducible_quotient (τ := Q) {q₀} hgen
  let π := Representation.quotient Q Z hZ
  let p : Representation.IntertwiningMap C.toRepresentation π :=
    (quotientMk Z hZ).comp (quotientMk Y0 hY0)
  have hp : Surjective p := (quotientMk_surjective Z hZ).comp (quotientMk_surjective Y0 hY0)
  have hπs : IsSmooth π := isSmooth_quotient (isSmooth_quotient (isSmooth_subrep hX C) Y0 hY0) Z hZ
  obtain ⟨i, hi⟩ := hfaith _ π hπs ⟨C, p, hp⟩

  have key : ∀ c : Cs, p c ∈ Representation.Coinvariants.ker (π.comp (N i).subtype) := by
    intro c
    have hmem : Representation.Coinvariants.mk (X.comp (N i).subtype) (c : V) ∈
        (Λ B i).toSubmodule := ⟨c, hCB c c.2, rfl⟩
    rw [← heq i] at hmem
    obtain ⟨a, ha, hac⟩ := hmem
    have haC : a ∈ Cs := Submodule.mem_sup_left ha
    have hk : ((c - ⟨a, haC⟩ : Cs) : V) ∈
        Representation.Coinvariants.ker (X.comp (N i).subtype) := by
      rw [← Representation.Coinvariants.mk_eq_zero]
      simp only [Submodule.coe_sub, map_sub]
      rw [← hac, sub_self]
    have hk' := mem_ker_subrep_of_mem_ker (N i) (hN i) hX C hk
    have hpa : p ⟨a, haC⟩ = 0 := by
      show quotientMk Z hZ (quotientMk Y0 hY0 ⟨a, haC⟩) = 0
      rw [quotientMk_apply Y0, (Submodule.Quotient.mk_eq_zero _).2 (show (⟨a, haC⟩ : Cs) ∈ Y0 from ha),
        map_zero]
    have := map_mem_coinvariantsKer p (N i) hk'
    rwa [map_sub, hpa, sub_zero] at this
  refine (not_subsingleton_iff_nontrivial.2 hi) ⟨fun y z => ?_⟩
  have hall : ∀ y : Representation.Coinvariants (π.comp (N i).subtype), y = 0 := by
    intro y
    obtain ⟨q, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    obtain ⟨c, rfl⟩ := hp q
    exact (Representation.Coinvariants.mk_eq_zero _).2 (key c)
  rw [hall y, hall z]

end Criterion

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

namespace Parabolic

open Function Matrix Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Congr

variable {α α' : Type*} [LinearOrder α] [LinearOrder α'] {β : Fin n → α} {γ : Fin n → α'}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eq_iff_eq_of_lt_iff (h : ∀ i j, β i < β j ↔ γ i < γ j) (i j : Fin n) :
    β i = β j ↔ γ i = γ j := by
  constructor
  · intro e
    rcases lt_trichotomy (γ i) (γ j) with hl | he | hg
    · exact absurd ((h i j).2 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).2 hg) (by rw [e]; exact lt_irrefl _)
  · intro e
    rcases lt_trichotomy (β i) (β j) with hl | he | hg
    · exact absurd ((h i j).1 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).1 hg) (by rw [e]; exact lt_irrefl _)


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockUpper_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    blockUpper F n β = blockUpper F n γ := by
  ext g
  simp only [mem_blockUpper, Matrix.BlockTriangular]
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_left (h j i)


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem unipotentRadical_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    unipotentRadical F n β = unipotentRadical F n γ := by
  ext g
  rw [mem_unipotentRadical, mem_unipotentRadical, blockUpper_congr h]
  exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j =>
    imp_congr_left (eq_iff_eq_of_lt_iff h i j)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_iff {i j : Fin n} : blockRank β i < blockRank β j ↔ β i < β j := by
  refine ⟨fun h => ?_, blockRank_lt⟩
  by_contra h'
  rcases (not_lt.1 h').lt_or_eq with h'' | h''
  · exact absurd (blockRank_lt h'') (by omega)
  · exact absurd (blockRank_eq h''.symm) (by omega)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_card (β : Fin n → α) (i : Fin n) : blockRank β i < n := by
  have : (Finset.univ.filter fun j => β j < β i) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => by
      have := h ▸ Finset.mem_univ i
      simp at this⟩
  simpa [blockRank] using Finset.card_lt_card this

def rankFun (β : Fin n → α) : Fin n → Fin n := fun i => ⟨blockRank β i, blockRank_lt_card β i⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rankFun_lt_iff (β : Fin n → α) (i j : Fin n) :
    ((rankFun β i : Fin n) : ℕ) < (rankFun β j : ℕ) ↔ β i < β j :=
  blockRank_lt_iff

end Congr

section Jacquet

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {X : Representation ℂ (GL (Fin n) F) V} {π : Representation ℂ (GL (Fin n) F) V'}

theorem jacquetMap_surjective (p : Representation.IntertwiningMap X π) (hp : Surjective p)
    (γ : Fin n → ℕ) : Surjective (jacquetMap F n γ p) := by
  intro y
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, jacquetMap_mk _ _⟩

theorem jacquetMap_injective (hX : IsSmooth X) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap X π) (hi : Injective i) (γ : Fin n → ℕ) :
    Injective (jacquetMap F n γ i) := by
  have hex := exact_jacquetMap (β := γ) hX hπ (0 : Representation.IntertwiningMap X X) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : V) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [jacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.jacquetRep (hX : IsSmooth X) (h : IsSubquotient π X) (γ : Fin n → ℕ) :
    IsSubquotient (jacquetRep F n γ π) (jacquetRep F n γ X) := by
  obtain ⟨C, p, hp⟩ := h
  exact .of_injective_of_surjective (jacquetMap F n γ (subrepInclusion C))
    (jacquetMap_injective (isSmooth_subrep hX C) hX _ (fun a b h => Subtype.ext h) γ)
    (jacquetMap F n γ p) (jacquetMap_surjective p hp γ)

theorem surjective_frobeniusParabolic [Nontrivial V'] {δ : Fin n → ℕ} {U : Type*}
    [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible]
    (hπ : IsSmooth π) (Φ : Representation.IntertwiningMap π (parabolicInd F n δ τ))
    (hΦ : Injective Φ) : Surjective (frobeniusParabolic F n δ τ hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero
    (frobeniusParabolic F n δ τ hπ Φ) with h | h
  · exact h
  · exfalso
    have h0 : Φ = 0 := (frobeniusParabolic F n δ τ hπ).injective (h.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : V')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Jacquet

end Parabolic

section Irreducible

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ρ : Representation ℂ G V} {π : Representation ℂ G W}

end Irreducible

end GroundTheory.Automorphic
