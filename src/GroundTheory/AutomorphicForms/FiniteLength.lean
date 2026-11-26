module

public import GroundTheory.AutomorphicForms.FiniteLengthCuspidal

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.FiniteLengthSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function Parabolic

universe u

section Series

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

def subquotientRep (A B : Subrepresentation ρ) :
    Representation ℂ G (B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) :=
  Representation.quotient B.toRepresentation (A.toSubmodule.comap B.toSubmodule.subtype)
    (fun g _ hx => A.apply_mem_toSubmodule g hx)

def subquotientMk (A B : Subrepresentation ρ) :
    Representation.IntertwiningMap B.toRepresentation (subquotientRep A B) :=
  quotientMk _ _

theorem subquotientMk_surjective (A B : Subrepresentation ρ) : Surjective (subquotientMk A B) :=
  quotientMk_surjective _ _

theorem subquotientMk_eq_zero_iff (A B : Subrepresentation ρ) (b : B.toSubmodule) :
    subquotientMk A B b = 0 ↔ (b : V) ∈ A :=
  Submodule.Quotient.mk_eq_zero _

def subrepInclusionOfLE {A B : Subrepresentation ρ} (h : A ≤ B) :
    Representation.IntertwiningMap A.toRepresentation B.toRepresentation :=
  ⟨Submodule.inclusion (p := A.toSubmodule) (p' := B.toSubmodule) fun _ hx => h hx,
    fun _ => LinearMap.ext fun _ => rfl⟩

theorem subrepInclusionOfLE_injective {A B : Subrepresentation ρ} (h : A ≤ B) :
    Injective (subrepInclusionOfLE h) :=
  fun a b hab => by
    have := congrArg (Subtype.val : B.toSubmodule → V) hab
    exact Subtype.ext this

theorem exact_subrepInclusionOfLE_subquotientMk {A B : Subrepresentation ρ} (h : A ≤ B) :
    Exact (subrepInclusionOfLE h) (subquotientMk A B) := by
  intro b
  rw [subquotientMk_eq_zero_iff]
  exact ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩

theorem isIrreducible_subquotientRep {A B : Subrepresentation ρ} (h : A ⋖ B) :
    (subquotientRep A B).IsIrreducible := by
  set T := A.toSubmodule.comap B.toSubmodule.subtype
  obtain ⟨b₀, hb₀B, hb₀A⟩ := SetLike.exists_of_lt h.lt
  have hmk : ∀ b : B.toSubmodule, Submodule.Quotient.mk (p := T) b = 0 ↔ (b : V) ∈ A :=
    fun b => Submodule.Quotient.mk_eq_zero _
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun Z => ?_ }
  · have : Submodule.Quotient.mk (p := T) ⟨b₀, hb₀B⟩ ∈ (⊥ : Subrepresentation (subquotientRep A B)) := by
      rw [hbt]; trivial
    exact hb₀A ((hmk _).1 ((Submodule.mem_bot ℂ).1 this))

  let Z' : Subrepresentation ρ :=
    ⟨(Z.toSubmodule.comap T.mkQ).map B.toSubmodule.subtype, by
      rintro g _ ⟨b, hb, rfl⟩
      exact ⟨B.toRepresentation g b, Z.apply_mem_toSubmodule g hb, rfl⟩⟩
  have hAZ : A ≤ Z' := fun a ha => ⟨⟨a, h.le ha⟩, by
    show Submodule.Quotient.mk (p := T) _ ∈ Z.toSubmodule
    rw [(hmk _).2 ha]
    exact Z.toSubmodule.zero_mem, rfl⟩
  have hZB : Z' ≤ B := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hmem : ∀ b : B.toSubmodule, (b : V) ∈ Z' → Submodule.Quotient.mk (p := T) b ∈ Z := by
    rintro b ⟨b', hb', hbb'⟩
    rw [show b = b' from Subtype.ext hbb'.symm]
    exact hb'
  rcases h.eq_or_eq hAZ hZB with hZ | hZ
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun q hq => ?_)
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective T q
    have : (b : V) ∈ Z' := ⟨b, hq, rfl⟩
    rw [hZ] at this
    exact (Submodule.mem_bot ℂ).2 ((hmk b).2 this)
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun q _ => ?_)
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective T q
    exact hmem b (by rw [hZ]; exact b.2)

theorem HasFiniteLength.exists_compositionSeries (h : HasFiniteLength ρ) :
    ∃ (k : ℕ) (S : ℕ → Subrepresentation ρ), S 0 = ⊥ ∧ S k = ⊤ ∧ ∀ j < k, S j ⋖ S (j + 1) := by
  have := h.wellFoundedLT
  have := h.wellFoundedGT
  obtain ⟨a, h0, k, hk, hcov⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (bot_le : (⊥ : Subrepresentation ρ) ≤ ⊤)
  exact ⟨k, a, h0, hk, hcov⟩

variable {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  {α : Representation ℂ G W} {γ : Representation ℂ G U}

theorem hasFiniteLength_of_exact (f : Representation.IntertwiningMap α ρ)
    (g : Representation.IntertwiningMap ρ γ) (hf : Injective f) (hfg : Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength ρ := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α ρ f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule ρ γ g
  have hf' : Injective f' := hf
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range g') :=
    IsFiniteLength.of_injective hC (LinearMap.range g').injective_subtype
  have hex : Exact f' g'.rangeRestrict := by
    intro y
    have : g'.rangeRestrict y = 0 ↔ g y = 0 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact f' g'.rangeRestrict hf' g'.surjective_rangeRestrict hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hA, Module.length_ne_top_iff.2 hr⟩

end Series

namespace Parabolic

open Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section IndMap

variable {β : Fin n → ℕ} {W W' W'' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
  [Module ℂ W'] [AddCommGroup W''] [Module ℂ W''] {σ : Representation ℂ (levi F n β) W}
  {σ' : Representation ℂ (levi F n β) W'} {σ'' : Representation ℂ (levi F n β) W''}

theorem comp_mem_parabolicIndSpace (f : Representation.IntertwiningMap σ σ')
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) :
    (f ∘ φ) ∈ parabolicIndSpace F n β σ' := by
  obtain ⟨h1, K, hK, hφK⟩ := hφ
  refine ⟨fun p g => ?_, K, hK, fun k hk g => ?_⟩
  · show f (φ ((p : GL (Fin n) F) * g)) = inflateTwist F n β σ' p (f (φ g))
    rw [h1 p g, inflateTwist_apply, inflateTwist_apply, map_smul,
      Representation.IntertwiningMap.isIntertwining]
  · show f (φ (g * k)) = f (φ g)
    rw [hφK k hk g]

def parabolicIndMap (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (parabolicInd F n β σ) (parabolicInd F n β σ') where
  toLinearMap :=
    { toFun := fun φ => ⟨f ∘ (φ : GL (Fin n) F → W), comp_mem_parabolicIndSpace f φ.2⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add f _ _)
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => map_smul f _ _) }
  isIntertwining' _ := LinearMap.ext fun _ => rfl

theorem parabolicIndMap_injective (f : Representation.IntertwiningMap σ σ') (hf : Injective f) :
    Injective (parabolicIndMap f) := fun _ _ h =>
  Subtype.ext (funext fun x => hf (congrFun (congrArg Subtype.val h) x))

theorem exists_parabolicIndMap_eq (f : Representation.IntertwiningMap σ σ') (hf : Injective f)
    (φ : parabolicIndSpace F n β σ') (hφ : ∀ x, ∃ y, f y = (φ : GL (Fin n) F → W') x) :
    ∃ ψ, parabolicIndMap f ψ = φ := by
  choose ψ hψ using hφ
  obtain ⟨h1, K, hK, hφK⟩ := φ.2
  refine ⟨⟨ψ, fun p x => hf ?_, K, hK, fun k hk x => hf ?_⟩, Subtype.ext (funext hψ)⟩
  · show f (ψ ((p : GL (Fin n) F) * x)) = f (inflateTwist F n β σ p (ψ x))
    rw [hψ, h1 p x, inflateTwist_apply, inflateTwist_apply, map_smul,
      Representation.IntertwiningMap.isIntertwining, hψ]
  · rw [hψ, hψ, hφK k hk x]

theorem exact_parabolicIndMap (f : Representation.IntertwiningMap σ σ')
    (g : Representation.IntertwiningMap σ' σ'') (hf : Injective f) (hfg : Exact f g) :
    Exact (parabolicIndMap f) (parabolicIndMap g) := by
  intro φ
  constructor
  · intro hφ
    exact exists_parabolicIndMap_eq f hf φ fun x =>
      (hfg _).1 (congrFun (congrArg Subtype.val hφ) x)
  · rintro ⟨ψ, rfl⟩
    refine Subtype.ext (funext fun x => ?_)
    exact (hfg _).2 ⟨_, rfl⟩

theorem parabolicIndMap_surjective (f : Representation.IntertwiningMap σ σ') (hf : Bijective f) :
    Surjective (parabolicIndMap f) := fun φ =>
  exists_parabolicIndMap_eq f hf.1 φ fun _ => hf.2 _

theorem hasFiniteLength_parabolicInd_of_factors {W₀ : Type u} [AddCommGroup W₀] [Module ℂ W₀]
    {σ₀ : Representation ℂ (levi F n β) W₀} (hσ : IsSmooth σ₀) (hfl : HasFiniteLength σ₀)
    (H : ∀ (W' : Type u) [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (levi F n β) W')
      [ρ.IsIrreducible], IsSmooth ρ → IsSubquotient ρ σ₀ → HasFiniteLength (parabolicInd F n β ρ)) :
    HasFiniteLength (parabolicInd F n β σ₀) := by
  obtain ⟨k, S, h0, hk, hcov⟩ := hfl.exists_compositionSeries
  have key : ∀ j ≤ k, HasFiniteLength (parabolicInd F n β (S j).toRepresentation) := by
    intro j hj
    induction j with
    | zero =>
      have hS0 : ∀ v, v ∈ (S 0).toSubmodule → v = 0 := fun v hv => by
        rw [h0] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      have : Subsingleton (S 0).toSubmodule :=
        ⟨fun a b => Subtype.ext ((hS0 _ a.2).trans (hS0 _ b.2).symm)⟩
      have := subsingleton_indSpace (blockUpper F n β) (inflateTwist F n β (S 0).toRepresentation)
      exact hasFiniteLength_of_subsingleton
    | succ j ih =>
      have hcj := hcov j (by omega)
      have := isIrreducible_subquotientRep hcj
      exact hasFiniteLength_of_exact (parabolicIndMap (subrepInclusionOfLE hcj.le))
        (parabolicIndMap (subquotientMk (S j) (S (j + 1))))
        (parabolicIndMap_injective _ (subrepInclusionOfLE_injective hcj.le))
        (exact_parabolicIndMap _ _ (subrepInclusionOfLE_injective hcj.le)
          (exact_subrepInclusionOfLE_subquotientMk hcj.le))
        (ih (by omega))
        (H _ (subquotientRep (S j) (S (j + 1)))
          (isSmooth_quotient (isSmooth_subrep hσ _) _ _)
          ⟨S (j + 1), subquotientMk _ _, subquotientMk_surjective _ _⟩)
  refine hasFiniteLength_of_surjective (parabolicIndMap (subrepInclusion (S k)))
    (parabolicIndMap_surjective _ ⟨fun a b hab => Subtype.ext hab, fun v => ⟨⟨v, ?_⟩, rfl⟩⟩)
    (key k le_rfl)
  rw [hk]
  trivial

end IndMap

section Jacquet

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem hasFiniteLength_jacquetRep_of_factors (hπ : IsSmooth π) (hfl : HasFiniteLength π)
    (β : Fin n → ℕ)
    (H : ∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin n) F) V')
      [π'.IsIrreducible], IsSmooth π' → IsSubquotient π' π → HasFiniteLength (jacquetRep F n β π')) :
    HasFiniteLength (jacquetRep F n β π) := by
  obtain ⟨k, S, h0, hk, hcov⟩ := hfl.exists_compositionSeries
  have key : ∀ j ≤ k, HasFiniteLength (jacquetRep F n β (S j).toRepresentation) := by
    intro j hj
    induction j with
    | zero =>
      have hS0 : ∀ v, v ∈ (S 0).toSubmodule → v = 0 := fun v hv => by
        rw [h0] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      have : Subsingleton (S 0).toSubmodule :=
        ⟨fun a b => Subtype.ext ((hS0 _ a.2).trans (hS0 _ b.2).symm)⟩
      have : Subsingleton (JacquetModule F n β (S 0).toRepresentation) :=
        ⟨fun a b => by
          obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
          obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
          rw [Subsingleton.elim a b]⟩
      exact hasFiniteLength_of_subsingleton
    | succ j ih =>
      have hcj := hcov j (by omega)
      have := isIrreducible_subquotientRep hcj
      have hs : ∀ i, IsSmooth (S i).toRepresentation := fun i => isSmooth_subrep hπ _
      have hq : IsSmooth (subquotientRep (S j) (S (j + 1))) :=
        isSmooth_quotient (hs _) _ _
      exact hasFiniteLength_of_exact (jacquetMap F n β (subrepInclusionOfLE hcj.le))
        (jacquetMap F n β (subquotientMk (S j) (S (j + 1))))
        (jacquetMap_injective (hs _) (hs _) _ (subrepInclusionOfLE_injective hcj.le) β)
        (exact_jacquetMap (hs _) hq _ _ (exact_subrepInclusionOfLE_subquotientMk hcj.le))
        (ih (by omega))
        (H _ (subquotientRep (S j) (S (j + 1))) hq
          ⟨S (j + 1), subquotientMk _ _, subquotientMk_surjective _ _⟩)
  refine hasFiniteLength_of_surjective (jacquetMap F n β (subrepInclusion (S k)))
    (jacquetMap_surjective _ (fun v => ⟨⟨v, ?_⟩, rfl⟩) β) (key k le_rfl)
  rw [hk]
  trivial

end Jacquet

end Parabolic

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.FiniteLengthLeviJacquet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology MeasureTheory Measure

universe u

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem sqrtModularLeviPar_of_mem_unipotentRadical {β γ δ : Fin n → ℕ} (q : leviPar F n β γ)
    (hq : (q : GL (Fin n) F) ∈ unipotentRadical F n δ) : sqrtModularLeviPar F n β γ q = 1 := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := δ)
    (isCompact_singleton (x := (q : GL (Fin n) F))) (by simpa using hq)
  have hk : rankTorus F n δ e * q * (rankTorus F n δ e)⁻¹ ∈ integralGL F n :=
    (mem_unipotentCompactG.1 (he rfl)).2
  have ht : rankTorus F n δ e ∈ leviPar F n β γ :=
    ⟨diagGL_mem_levi _, levi_le_blockUpper (diagGL_mem_levi _)⟩
  have hkL : rankTorus F n δ e * q * (rankTorus F n δ e)⁻¹ ∈ leviPar F n β γ :=
    (leviPar F n β γ).mul_mem ((leviPar F n β γ).mul_mem ht q.2) ((leviPar F n β γ).inv_mem ht)
  have h1 : sqrtModularLeviPar F n β γ ⟨_, hkL⟩ = 1 := by
    show ((NNReal.sqrt (modularCharacter (⟨_, hkL⟩ : leviPar F n β γ)) : ℝ) : ℂ) = 1
    rw [modularCharacter_leviPar_eq_one_of_mem_integralGL _ hk]
    simp
  have : q = ⟨_, ht⟩⁻¹ * ⟨_, hkL⟩ * ⟨_, ht⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  rw [this, map_mul, map_mul, h1, mul_one, ← map_mul, inv_mul_cancel, map_one]

section Stages

variable {β γ δ : Fin n → ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ (levi F n β) U}

theorem mk_mk_apply_of_mem_leviUnipotent (h : Refines β γ) (hγδ : Refines γ δ)
    (u : leviUnipotent F n β δ) (w : U) :
    Representation.Coinvariants.mk ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
        (Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
          (ρ (u : levi F n β) w)) =
      Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ w) := by
  have huN : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n δ :=
    Subgroup.mem_subgroupOf.1 u.2
  obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 huN
  set p : blockUpper F n γ := ⟨_, hγδ.blockUpper_le F huP⟩
  set m := leviProj F n γ p
  have hmN : ((m : levi F n γ) : GL (Fin n) F) ∈ unipotentRadical F n δ := by
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show ((m : levi F n γ) : GL (Fin n) F) i j = 0
      rw [leviProj_apply]
      split_ifs
      · exact huP hij
      · rfl
    · rw [leviProj_apply, if_pos (hγδ.eq_of_eq hij)]
      exact hu1 i j hij
  have hn' := leviProj_inv_mul_mem p
  set n' : levi F n β := (h.leviIncl F m)⁻¹ * (u : levi F n β)
  have hcoe : ((n' : levi F n β) : GL (Fin n) F) =
      (((leviIncl m)⁻¹ * p : blockUpper F n γ) : GL (Fin n) F) := by
    simp only [n', Subgroup.coe_mul, Subgroup.coe_inv, Refines.coe_leviIncl, leviIncl_coe]
    rfl
  have hn'N : ((n' : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
    rw [hcoe]
    exact hn'
  have hu : (u : levi F n β) = h.leviIncl F m * n' := by simp [n']
  have hn'w : Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype) (ρ n' w) =
      Representation.Coinvariants.mk _ w :=
    Representation.Coinvariants.mk_self_apply (ρ.comp (leviUnipotent F n β γ).subtype)
      ⟨n', Subgroup.mem_subgroupOf.2 hn'N⟩ w
  have hsq : sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) = 1 :=
    sqrtModularLeviPar_of_mem_unipotentRadical _ hmN
  have e1 : ρ (u : levi F n β) w = ρ (h.leviIncl F m) (ρ n' w) := by
    rw [hu, map_mul ρ, Module.End.mul_apply]
  have key : Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
      (ρ (u : levi F n β) w) =
      leviJacquetRep h ρ m (Representation.Coinvariants.mk _ w) :=
    calc _ = Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
          (ρ (h.leviIncl F m) (ρ n' w)) := congrArg _ e1
      _ = sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
          leviJacquetRep h ρ m (Representation.Coinvariants.mk _ (ρ n' w)) :=
        mk_leviIncl_apply ρ h m _
      _ = leviJacquetRep h ρ m (Representation.Coinvariants.mk _ w) :=
        (congrArg (· • leviJacquetRep h ρ m (Representation.Coinvariants.mk _ (ρ n' w))) hsq).trans
          ((one_smul ℂ _).trans (congrArg (leviJacquetRep h ρ m) hn'w))
  exact (congrArg _ key).trans (Representation.Coinvariants.mk_self_apply
    ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
    ⟨m, Subgroup.mem_subgroupOf.2 hmN⟩ _)

theorem subsingleton_coinvariants_leviJacquetRep (h : Refines β γ) (hγδ : Refines γ δ)
    (hs : Subsingleton (LeviJacquetModule β δ ρ)) :
    Subsingleton (Representation.Coinvariants
      ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)) := by
  set q' := Representation.Coinvariants.mk
    ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
  set q := Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
  have hker : Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β δ).subtype) ≤
      LinearMap.ker (q' ∘ₗ q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, w⟩, rfl⟩
    show q' (q (ρ (u : levi F n β) w - w)) = 0
    rw [map_sub q, map_sub q', sub_eq_zero]
    exact mk_mk_apply_of_mem_leviUnipotent h hγδ u w
  have hzero : ∀ x : U, q' (q x) = 0 := by
    intro x
    have hx : x ∈ Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β δ).subtype) :=
      (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hker hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  exact (hzero a).trans (hzero b).symm

end Stages

section Generation

variable {β γ : Fin n → ℕ}

theorem exists_leviPar_mul_integral (h : Refines β γ) (g : levi F n β) :
    ∃ q : leviPar F n β γ, ∃ k : levi F n β, (k : GL (Fin n) F) ∈ integralGL F n ∧
      (g : GL (Fin n) F) = q * k := by
  obtain ⟨p, hp, k, hk, hg⟩ := exists_blockUpper_mul_integralGL' (β := γ) (g : GL (Fin n) F)
  have hpβ : p ∈ blockUpper F n β := h.blockUpper_le F hp
  have hkβ : k ∈ blockUpper F n β := by
    have : k = p⁻¹ * g := by rw [hg]; group
    rw [this]
    exact (blockUpper F n β).mul_mem ((blockUpper F n β).inv_mem hpβ) (levi_le_blockUpper g.2)
  set pβ : blockUpper F n β := ⟨p, hpβ⟩
  set kβ : blockUpper F n β := ⟨k, hkβ⟩
  have hqγ : ((leviProj F n β pβ : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ := by
    intro i j hij
    show ((leviProj F n β pβ : levi F n β) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hp hij
    · rfl
  refine ⟨⟨_, (leviProj F n β pβ).2, hqγ⟩, leviProj F n β kβ, leviProj_mem_integralGL hk, ?_⟩
  have hgβ : (⟨g, levi_le_blockUpper g.2⟩ : blockUpper F n β) = pβ * kβ := Subtype.ext hg
  have := congrArg (fun x => ((leviProj F n β x : levi F n β) : GL (Fin n) F)) hgβ
  simp only [map_mul, Subgroup.coe_mul, leviProj_of_mem_levi g.2] at this
  exact this

variable {U : Type*} [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ (levi F n β) U}

theorem exists_finset_span_leviJacquetRep (h : Refines β γ) (hρ : IsSmooth ρ) {v : U}
    (hv : Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v) = ⊤) :
    ∃ S : Finset (LeviJacquetModule β γ ρ),
      Submodule.span ℂ {x | ∃ m, ∃ s ∈ S, x = leviJacquetRep h ρ m s} = ⊤ := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_congruence_fixed hρ v
  set K₀ : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)
  set Km : Subgroup (levi F n β) := (congruenceSubgroup F n m₀).subgroupOf (levi F n β)
  have hvK : v ∈ fixedVectors ρ Km := fun k hk => hm₀ k (Subgroup.mem_subgroupOf.1 hk)
  have : CompactSpace K₀ :=
    isCompact_iff_compactSpace.1 (isCompact_subgroupOf_levi (isCompact_integralGL F n))
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m₀)).preimage
      continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ Km.subgroupOf K₀)
  let R : Finset (levi F n β) :=
    Finset.univ.image fun q : K₀ ⧸ Km.subgroupOf K₀ => ((Quotient.out q : K₀) : levi F n β)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, ρ k v = ρ r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq ρ hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ Km.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  set q := Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
  refine ⟨R.image fun r => q (ρ r v), ?_⟩
  set T := Submodule.span ℂ {x | ∃ m, ∃ s ∈ R.image fun r => q (ρ r v),
    x = leviJacquetRep h ρ m s}
  have hclaim : ∀ g : levi F n β, q (ρ g v) ∈ T := by
    intro g
    obtain ⟨qq, k, hk, hg⟩ := exists_leviPar_mul_integral h g
    obtain ⟨r, hr, hrv⟩ := hR k (Subgroup.mem_subgroupOf.2 hk)
    set pγ : blockUpper F n γ := ⟨qq, qq.2.2⟩
    set m := leviProj F n γ pγ
    have hn : ((pγ * (leviIncl m)⁻¹ : blockUpper F n γ) : GL (Fin n) F) ∈
        unipotentRadical F n γ := by
      rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, mul_inv_cancel]
    have hnβ : ((pγ * (leviIncl m)⁻¹ : blockUpper F n γ) : GL (Fin n) F) ∈ levi F n β := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe]
      exact (levi F n β).mul_mem qq.2.1 ((levi F n β).inv_mem (h.levi_le F m.2))
    set n' : levi F n β := ⟨_, hnβ⟩
    have hgeq : g = n' * h.leviIncl F m * k := by
      apply Subtype.ext
      simp only [n', Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, Refines.coe_leviIncl, hg]
      show (qq : GL (Fin n) F) * k = (qq : GL (Fin n) F) * (m : GL (Fin n) F)⁻¹ * m * k
      group
    have hn'v : ∀ x, q (ρ n' x) = q x := fun x =>
      Representation.Coinvariants.mk_self_apply (ρ.comp (leviUnipotent F n β γ).subtype)
        ⟨n', Subgroup.mem_subgroupOf.2 hn⟩ x
    have e1 : ρ g v = ρ n' (ρ (h.leviIncl F m) (ρ r v)) := by
      rw [hgeq, map_mul ρ, map_mul ρ, Module.End.mul_apply, Module.End.mul_apply, hrv]
    have e2 : q (ρ g v) = sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
        leviJacquetRep h ρ m (q (ρ r v)) :=
      (congrArg q e1).trans ((hn'v _).trans (mk_leviIncl_apply ρ h m _))
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, q (ρ r v),
      Finset.mem_image_of_mem _ hr, rfl⟩)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  have hy : y ∈ Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v) := by
    rw [hv]
    exact Submodule.mem_top
  have hmap : Submodule.map q (Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v)) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hclaim g
  exact hmap ⟨y, hy, rfl⟩

end Generation

section Embedding

variable {β : Fin n → ℕ}

theorem Refines.trans {β γ δ : Fin n → ℕ} (h₁ : Refines β γ) (h₂ : Refines γ δ) :
    Refines β δ :=
  fun i j h => h₂ i j (h₁ i j h)


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eq_one_of_mem_leviUnipotent_self (u : leviUnipotent F n β β) :
    ((u : levi F n β) : GL (Fin n) F) = 1 := by
  have hu := mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 u.2)
  have hl := mem_levi.1 (u : levi F n β).2
  apply Units.ext
  ext i j
  by_cases hij : β i = β j
  · exact hu.2 i j hij
  · rw [hl i j hij, Units.val_one, one_apply_ne fun e => hij (by rw [e])]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem nontrivial_leviJacquetModule_self {U : Type*} [AddCommGroup U] [Module ℂ U]
    [Nontrivial U] (ρ : Representation ℂ (levi F n β) U) :
    Nontrivial (LeviJacquetModule β β ρ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : U)
  refine ⟨⟨Representation.Coinvariants.mk _ v, 0, fun h => hv ?_⟩⟩
  have hmem := (Representation.Coinvariants.mk_eq_zero _).1 h
  have hle : Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β β).subtype) ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    have hu : (u : levi F n β) = 1 := Subtype.ext (eq_one_of_mem_leviUnipotent_self u)
    simp [hu]
  exact (Submodule.mem_bot ℂ).1 (hle hmem)


set_option maxHeartbeats 1000000 in
theorem exists_embedding_leviParabolicInd {U : Type u} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ (levi F n β) U} [ρ.IsIrreducible] (hρ : IsSmooth ρ) :
    ∃ (γ : Fin n → ℕ) (_ : Refines β γ) (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (levi F n γ) W), τ.IsIrreducible ∧ IsSmooth τ ∧ IsCuspidal τ ∧
        ∃ Φ : Representation.IntertwiningMap ρ (leviParabolicInd F n β γ τ), Function.Injective Φ := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  have : Nontrivial U := ⟨⟨v, 0, hv0⟩⟩
  have hspan := span_range_eq_top_of_isIrreducible (ρ := ρ) hv0

  let P : ℕ → Prop := fun k => ∃ γ : Fin n → ℕ, Refines β γ ∧ (Finset.univ.image γ).card = k ∧
    Nontrivial (LeviJacquetModule β γ ρ)
  have hbound : ∀ γ : Fin n → ℕ, (Finset.univ.image γ).card ≤ n := fun γ =>
    (Finset.card_image_le).trans (by simp)
  have hP0 : P (Finset.univ.image β).card :=
    ⟨β, Refines.refl β, rfl, nontrivial_leviJacquetModule_self ρ⟩
  obtain ⟨γ, hγ, hγcard, hγnt⟩ := Nat.findGreatest_spec (hbound _) hP0
  have hfinest : ∀ δ : Fin n → ℕ, (∃ i j, γ i = γ j ∧ δ i ≠ δ j) →
      Subsingleton (LeviJacquetModule β (refineFun γ δ) ρ) := by
    intro δ hδ
    have hlt := card_image_lt_refineFun hδ
    rw [hγcard] at hlt
    have := Nat.findGreatest_is_greatest hlt (hbound _)
    rw [← not_nontrivial_iff_subsingleton]
    exact fun hnt => this ⟨_, hγ.trans (refines_refineFun γ δ), rfl, hnt⟩

  obtain ⟨S, hS⟩ := exists_finset_span_leviJacquetRep hγ hρ hspan
  have : Nontrivial (LeviJacquetModule β γ ρ) := hγnt
  obtain ⟨Y, hY, hirr⟩ := exists_irreducible_quotient (τ := leviJacquetRep hγ ρ) S hS
  let τ := Representation.quotient (leviJacquetRep hγ ρ) Y hY
  have hτs : IsSmooth τ := isSmooth_quotient (isSmooth_leviJacquetRep hγ hρ) Y hY
  have hτc : IsCuspidal τ := by
    intro δ hδ
    have h1 := subsingleton_coinvariants_leviJacquetRep hγ (refines_refineFun γ δ) (hfinest δ hδ)
    rw [← leviUnipotent_refineFun] at h1
    exact subsingleton_coinvariants_of_surjective (quotientMk Y hY) (quotientMk_surjective Y hY) h1
  refine ⟨γ, hγ, _, inferInstance, inferInstance, τ, hirr, hτs, hτc, ?_⟩

  set Φ := (leviFrobenius ρ τ hγ hρ).symm (quotientMk Y hY)
  refine ⟨Φ, ?_⟩
  rcases Representation.IsIrreducible.injective_or_eq_zero Φ with hΦ | hΦ
  · exact hΦ
  · exfalso
    have h0 : quotientMk Y hY = 0 := by
      rw [← (leviFrobenius ρ τ hγ hρ).apply_symm_apply (quotientMk Y hY)]
      show leviFrobenius ρ τ hγ hρ Φ = 0
      rw [hΦ, map_zero]
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    obtain ⟨x, rfl⟩ := quotientMk_surjective Y hY w
    exact hw (by rw [h0]; rfl)

end Embedding

end Parabolic

end GroundTheory.Automorphic
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Levi

variable {β δ : Fin n → ℕ} {U U' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U']
  [Module ℂ U'] {Y : Representation ℂ (levi F n β) U} {π : Representation ℂ (levi F n β) U'}

theorem leviJacquetMap_injective (h : Refines β δ) (hY : IsSmooth Y) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap Y π) (hi : Injective i) :
    Injective (leviJacquetMap h i) := by
  have hex := exact_leviJacquetMap h hY hπ (0 : Representation.IntertwiningMap Y Y) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : U) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [leviJacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.leviJacquetRep (h : Refines β δ) (hY : IsSmooth Y)
    (hsub : IsSubquotient π Y) : IsSubquotient (leviJacquetRep h π) (leviJacquetRep h Y) := by
  obtain ⟨C, p, hp⟩ := hsub
  refine .of_injective_of_surjective (leviJacquetMap h (subrepInclusion C))
    (leviJacquetMap_injective h (isSmooth_subrep hY C) hY _ (fun a b h => Subtype.ext h))
    (leviJacquetMap h p) fun y => ?_
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, leviJacquetMap_mk _ _ _⟩

theorem surjective_leviFrobenius [Nontrivial U'] (h : Refines β δ) {X : Type*} [AddCommGroup X]
    [Module ℂ X] {τ : Representation ℂ (levi F n δ) X} [τ.IsIrreducible] (hπ : IsSmooth π)
    (Φ : Representation.IntertwiningMap π (leviParabolicInd F n β δ τ)) (hΦ : Injective Φ) :
    Surjective (leviFrobenius π τ h hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero (leviFrobenius π τ h hπ Φ) with h' | h'
  · exact h'
  · exfalso
    have h0 : Φ = 0 := (leviFrobenius π τ h hπ).injective (h'.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : U')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Levi

section Cuspidal

variable {γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {τ : Representation ℂ (levi F n γ) W}

theorem hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β (parabolicInd F n γ τ)) := by
  classical
  set X := parabolicInd F n γ τ
  have hX : IsSmooth X := isSmooth_parabolicInd τ
  have hY : IsSmooth (jacquetRep F n β X) := isSmooth_jacquetRep X hX

  let ι := {δ : Fin n → Fin n // Refines β (fun i => (δ i : ℕ)) ∧
    ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ γ (w a) = γ (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  refine hasFiniteLength_of_coinvariants hY (fun δ : ι => leviUnipotent F n β (dN δ))
    (fun δ => exists_compactOpen_leviUnipotent) (M := fun δ => levi F n (dN δ))
    (fun δ => leviJacquetRep δ.2.1 (jacquetRep F n β X))
    (fun δ m => ⟨δ.2.1.leviIncl F m, _, fun v => leviJacquetRep_mk _ _ m v⟩)
    (fun δ => hasFiniteLength_of_injective (jacquetStages X δ.2.1).toIntertwiningMap
      (fun a b hab => (jacquetStages X δ.2.1).toLinearEquiv.injective hab)
      (hasFiniteLength_jacquetRep_parabolicInd hτ hτc
        (let ⟨w', hw'⟩ := δ.2.2; ⟨w', fun a b => (hdN δ a b).trans (hw' a b)⟩))) ?_
  intro V' _ _ π _ hπ hsub
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
  obtain ⟨δ', h', U, _, _, τ', hτ'i, hτ's, hτ'c, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hπ
  have hq := surjective_leviFrobenius h' hπ Φ hΦ
  have hsubτ : IsSubquotient τ' (jacquetRep F n δ' X) :=
    ((IsSubquotient.of_surjective _ hq).trans (hsub.leviJacquetRep h' hY)).trans
      (IsSubquotient.of_injective (jacquetStages X h').toIntertwiningMap
        (fun a b hab => (jacquetStages X h').toLinearEquiv.injective hab))
  obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hτ hτc hτ's hτ'c hsubτ
  have hrank : ∀ a b, δ' a = δ' b ↔ (rankFun δ' a : ℕ) = rankFun δ' b := fun a b =>
    eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff δ' i j).symm) a b
  let δ : ι := ⟨rankFun δ', fun i j hij => (rankFun_lt_iff δ' j i).2 (h' i j hij),
    w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
  refine ⟨δ, ?_⟩
  have hN : leviUnipotent F n β (dN δ) = leviUnipotent F n β δ' := by
    simp only [leviUnipotent]
    rw [unipotentRadical_congr (rankFun_lt_iff δ')]
  rw [hN]
  obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ')
  obtain ⟨y, hy⟩ := hq u
  exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Cuspidal

section Main

theorem hasFiniteLength_jacquetRep_of_isIrreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} [π.IsIrreducible] (hπ : IsSmooth π) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β π) := by
  obtain ⟨γ, U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
  exact hasFiniteLength_of_injective (jacquetMap F n β Φ)
    (jacquetMap_injective hπ (isSmooth_parabolicInd τ) Φ hΦ β)
    (hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal hτs hτc β)

theorem hasFiniteLength_jacquetRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} (hπ : IsSmooth π) (hfl : HasFiniteLength π)
    (β : Fin n → ℕ) : HasFiniteLength (jacquetRep F n β π) :=
  hasFiniteLength_jacquetRep_of_factors hπ hfl β fun _ _ _ _ _ hπ' _ =>
    hasFiniteLength_jacquetRep_of_isIrreducible hπ' β

theorem hasFiniteLength_parabolicInd_of_isIrreducible {β : Fin n → ℕ} {W : Type*}
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (levi F n β) W} [ρ.IsIrreducible]
    (hρ : IsSmooth ρ) : HasFiniteLength (parabolicInd F n β ρ) := by
  obtain ⟨γ, h, X, _, _, τ, hτi, hτs, hτc, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hρ
  have he : Injective (inductionStages τ h).toIntertwiningMap := fun a b hab =>
    (inductionStages τ h).toLinearEquiv.injective hab
  exact hasFiniteLength_of_injective
    ((inductionStages τ h).toIntertwiningMap.comp (parabolicIndMap Φ))
    (he.comp (parabolicIndMap_injective Φ hΦ))
    (hasFiniteLength_parabolicInd_of_isCuspidal hτs hτc)

theorem hasFiniteLength_parabolicInd {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσ : IsSmooth σ) (hfl : HasFiniteLength σ) :
    HasFiniteLength (parabolicInd F n β σ) :=
  hasFiniteLength_parabolicInd_of_factors hσ hfl fun _ _ _ _ _ hρ _ =>
    hasFiniteLength_parabolicInd_of_isIrreducible hρ

end Main

end Parabolic

end GroundTheory.Automorphic
