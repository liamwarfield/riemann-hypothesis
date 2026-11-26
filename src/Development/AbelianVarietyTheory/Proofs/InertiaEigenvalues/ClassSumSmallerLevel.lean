module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ClassRefine

open scoped Classical

variable {G : Type*} [Group G] (Q : Subgroup G)

def stabQ (J : Subgroup G) (t : G) : Subgroup Q :=
  (J.comap (MulAut.conj t⁻¹).toMonoidHom).comap Q.subtype

variable {Q}

theorem mem_stabQ {J : Subgroup G} {t : G} {q : Q} : q ∈ stabQ Q J t ↔ t⁻¹ * (q : G) * t ∈ J := by
  rw [stabQ, Subgroup.mem_comap, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]

theorem card_stabQ_eq (J : Subgroup G) (t : G) :
    Nat.card (stabQ Q J t) = Nat.card {q : Q // t⁻¹ * (q : G) * t ∈ J} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabQ)

theorem card_stabQ_left (J : Subgroup G) (x : G) (γ : Q) :
    Nat.card (stabQ Q J ((γ : G) * x)) = Nat.card (stabQ Q J x) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨γ⁻¹ * q * γ, ?_⟩
      invFun := fun q => ⟨γ * q * γ⁻¹, ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem card_stabQ_split {J J' : Subgroup G} (hJ : J' ≤ J) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J)
    (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') (t s : G) (γ₀ : Q) (κ₀ : G) (hκ₀ : κ₀ ∈ J)
    (hs : s = (γ₀ : G) * t * κ₀) :
    Nat.card (stabQ Q J t) =
      (F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j).card * Nat.card (stabQ Q J' s) := by
  have hex : ∀ κ ∈ J, ∃ u, u ∈ F ∧ u⁻¹ * κ ∈ J' := fun κ hκ => (hFu κ hκ).exists
  choose! uF huF hJu using hex
  have huniq : ∀ κ ∈ J, ∀ u ∈ F, u⁻¹ * κ ∈ J' → u = uF κ := fun κ hκ u hu h =>
    (hFu κ hκ).unique ⟨hu, h⟩ ⟨huF κ hκ, hJu κ hκ⟩
  have hSΓ : stabQ Q J' (t * κ₀) ≤ stabQ Q J t := by
    intro q hq
    rw [mem_stabQ] at hq ⊢
    have : κ₀ * ((t * κ₀)⁻¹ * (q : G) * (t * κ₀)) * κ₀⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hκ₀ (hJ hq)) (J.inv_mem hκ₀)
    simpa [mul_assoc] using this
  set Γ := stabQ Q J t with hΓ
  set S := stabQ Q J' (t * κ₀) with hS
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j with hU
  let κf : Γ → G := fun q => t⁻¹ * ((q : Q) : G) * t * κ₀
  have hκ : ∀ q : Γ, κf q ∈ J := fun q => J.mul_mem (mem_stabQ.1 q.2) hκ₀
  have hψ : ∀ q : Γ, uF (κf q) ∈ U := by
    intro q
    rw [hU, Finset.mem_filter]
    refine ⟨huF _ (hκ q), (q : Q) * γ₀⁻¹, ((uF (κf q))⁻¹ * κf q)⁻¹, J'.inv_mem (hJu _ (hκ q)), ?_⟩
    simp only [κf, hs]
    push_cast
    group
  let ψ : Γ → U := fun q => ⟨uF (κf q), hψ q⟩
  have hresp : ∀ a b : Γ, a⁻¹ * b ∈ S.subgroupOf Γ → ψ a = ψ b := by
    intro a b h
    rw [Subgroup.mem_subgroupOf, hS, mem_stabQ] at h
    apply Subtype.ext
    show uF (κf a) = uF (κf b)
    refine huniq (κf b) (hκ b) (uF (κf a)) (huF _ (hκ a)) ?_
    have e : (uF (κf a))⁻¹ * κf b =
        ((uF (κf a))⁻¹ * κf a) * ((t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀)) := by
      simp only [κf]
      push_cast
      group
    rw [e]
    exact J'.mul_mem (hJu _ (hκ a)) h
  let Φ : Γ ⧸ S.subgroupOf Γ → U := Quotient.lift ψ (fun a b h => hresp a b (QuotientGroup.leftRel_apply.1 h))
  have hΦ : ∀ a : Γ, Φ (a : Γ ⧸ S.subgroupOf Γ) = ψ a := fun a => rfl
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hΦ, hΦ] at hxy
      have hab : uF (κf a) = uF (κf b) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hS, mem_stabQ]
      have h1 := hJu _ (hκ a)
      have h2 := hJu _ (hκ b)
      rw [hab] at h1
      have e : (t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀) =
          ((uF (κf b))⁻¹ * κf a)⁻¹ * ((uF (κf b))⁻¹ * κf b) := by
        simp only [κf]
        push_cast
        group
      rw [e]
      exact J'.mul_mem (J'.inv_mem h1) h2
    · rintro ⟨u, hu⟩
      have hu' := hu
      rw [hU, Finset.mem_filter] at hu'
      obtain ⟨huF', q, j, hj, e⟩ := hu'
      have hu_eq : u = t⁻¹ * ((q : G) * ((γ₀ : G) * t * κ₀) * j) := by
        rw [← hs, ← e]; group
      have hmem : t⁻¹ * (((q * γ₀ : Q)) : G) * t = u * j⁻¹ * κ₀⁻¹ := by
        rw [hu_eq]; push_cast; group
      have hqΓ : q * γ₀ ∈ Γ := by
        rw [hΓ, mem_stabQ, hmem]
        exact J.mul_mem (J.mul_mem (hF u huF') (J.inv_mem (hJ hj))) (J.inv_mem hκ₀)
      refine ⟨((⟨q * γ₀, hqΓ⟩ : Γ) : Γ ⧸ S.subgroupOf Γ), ?_⟩
      rw [hΦ]
      apply Subtype.ext
      show uF (κf ⟨q * γ₀, hqΓ⟩) = u
      refine (huniq _ (hκ _) u huF' ?_).symm
      have e2 : u⁻¹ * κf ⟨q * γ₀, hqΓ⟩ = j⁻¹ := by
        show u⁻¹ * (t⁻¹ * (((q * γ₀ : Q)) : G) * t * κ₀) = j⁻¹
        rw [hmem]; group
      rw [e2]
      exact J'.inv_mem hj
  have h1 := Subgroup.card_mul_index (S.subgroupOf Γ)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv, Subgroup.index,
    Nat.card_eq_of_bijective Φ hbij, Nat.card_eq_finsetCard] at h1
  have h2 : Nat.card (stabQ Q J' s) = Nat.card S := by
    rw [hS, hs, mul_assoc]
    exact card_stabQ_left J' (t * κ₀) γ₀
  rw [h2, ← h1, mul_comm]

theorem sum_classReps_refine {J J' : Subgroup G} (hJ : J' ≤ J) {T T' : Finset G}
    (hT : ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Q) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ)
    (hT' : ∀ g : G, ∃! t, t ∈ T' ∧ ∃ (γ : Q) (κ : G), κ ∈ J' ∧ g = (γ : G) * t * κ)
    (φ : G → ℂ) (hφQ : ∀ (γ : Q) g, φ ((γ : G) * g) = φ g) (hφJ : ∀ κ ∈ J', ∀ g, φ (g * κ) = φ g)
    {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J) (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') :
    ∑ t' ∈ T', ((Nat.card (stabQ Q J' t') : ℂ))⁻¹ * φ t' =
      ∑ t ∈ T, ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * ∑ u ∈ F, φ (t * u) := by
  choose! rep hrepT hrep using fun g => (hT' g).exists
  have hrepeq : ∀ g t', t' ∈ T' → ∀ (γ : Q) (κ : G), κ ∈ J' → g = γ * t' * κ → rep g = t' :=
    fun g t' ht' γ κ hκ e => (hT' g).unique ⟨hrepT g, hrep g⟩ ⟨ht', γ, κ, hκ, e⟩
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product' (f := fun t u => ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * φ (t * u)),
    ← Finset.sum_fiberwise_of_maps_to (s := T ×ˢ F) (t := T') (g := fun p => rep (p.1 * p.2))
      (fun p _ => hrepT _)]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  obtain ⟨t₀, ht₀, γ₀, κ₀, hκ₀, e₀⟩ := (hT t').exists
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t₀ * u = q * t' * j with hU
  have hfib : (T ×ˢ F).filter (fun p => rep (p.1 * p.2) = t') = {t₀} ×ˢ U := by
    ext ⟨a, u⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, hU]
    constructor
    · rintro ⟨⟨ha, hu⟩, hp⟩
      obtain ⟨γ, κ, hκ, e⟩ := hrep (a * u)
      rw [hp] at e
      have ha0 : a = t₀ := by
        refine (hT a).unique ⟨ha, 1, 1, J.one_mem, by simp⟩
          ⟨ht₀, γ * γ₀, κ₀ * κ * u⁻¹, J.mul_mem (J.mul_mem hκ₀ (hJ hκ)) (J.inv_mem (hF u hu)), ?_⟩
        have ea : a = a * u * u⁻¹ := by group
        rw [ea, e, e₀]
        push_cast
        group
      subst ha0
      exact ⟨rfl, hu, γ, κ, hκ, e⟩
    · rintro ⟨rfl, hu, q, j, hj, e⟩
      exact ⟨⟨ht₀, hu⟩, hrepeq _ t' ht' q j hj e⟩
  rw [hfib, Finset.sum_product, Finset.sum_singleton]
  have hval : ∀ u ∈ U, ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ (t₀ * u) =
      ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ t' := by
    intro u hu
    rw [hU, Finset.mem_filter] at hu
    obtain ⟨_, q, j, hj, e⟩ := hu
    rw [e, mul_assoc, hφQ, hφJ j hj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_stabQ_split hJ hF hFu t₀ t' γ₀ κ₀ hκ₀ e₀]
  have hne : U.card ≠ 0 := by
    obtain ⟨u, hu, hj⟩ := (hFu κ₀ hκ₀).exists
    refine Finset.card_ne_zero_of_mem (s := U) (a := u) ?_
    rw [hU, Finset.mem_filter]
    refine ⟨hu, γ₀⁻¹, (u⁻¹ * κ₀)⁻¹, J'.inv_mem hj, ?_⟩
    rw [e₀]
    push_cast
    group
  have hc : (U.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  rw [nsmul_eq_mul, Nat.cast_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem classSum_smaller_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), IsInvForm a β → ∀ (J J' : Subgroup (GAf L n)) (T T' : Finset (GAf L n)), IsBounded J → J' ≤ J → J'.relIndex J ≠ 0 → IsClassReps J T → IsClassReps J' T' → ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, (∀ κ ∈ J', ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g)) → ∀ F : Finset (GAf L n), (∀ κ ∈ F, κ ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') → classSum a β J' T' f f' = ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * ∑ u ∈ F, β (f (t * u)) (f' (t * u)) := by
  intro L _ _ _ n a β hβ J J' T T' _ hJ _ hT hT' f hf f' hf' hinv F hF hFu
  have key := sum_classReps_refine (Q := GQ L n) hJ hT hT' (fun g => β (f g) (f' g))
    (fun γ g => by rw [hf.1 γ g, hf'.1 γ g, hβ.2.2]) (fun κ hκ g => hinv κ hκ g) hF hFu
  simp only [card_stabQ_eq] at key
  exact key

end GlobalTheory.ClassRefine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.Take

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

section Plain

variable {Γ₀ Γ₁ : Type} [Group Γ₀] [Group Γ₁] {X₀ X₁ : Type} {A : Type} [CommRing A] {n r t : ℕ}

def pull (A : Type) [CommRing A] (e : X₁ ≃ X₀) : (X₀ → A) ≃ₐ[A] (X₁ → A) where
  toFun f := fun x => f (e x)
  invFun f := fun x => f (e.symm x)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def pullT (e : X₁ ≃ X₀) (T : Subalgebra A (X₀ → A)) : Subalgebra A (X₁ → A) :=
  T.map (pull A e : (X₀ → A) →ₐ[A] (X₁ → A))

theorem pull_mem (e : X₁ ≃ X₀) {T : Subalgebra A (X₀ → A)} {f : X₀ → A} (hf : f ∈ T) :
    (fun x => f (e x)) ∈ pullT e T := ⟨f, hf, rfl⟩

def pullR (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀) (rep : X₀ → (Γ₀ →* GL (Fin n) A)) : X₁ → (Γ₁ →* GL (Fin n) A) :=
  fun x => (rep (e x)).comp γ.toMonoidHom

variable (e : X₁ ≃ X₀) (γ : Γ₁ ≃* Γ₀)

theorem inRing_pull {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)}
    {a : X₀ → Matrix (Fin n) (Fin n) A} (h : InRing T rep a) :
    InRing (pullT e T) (pullR e γ rep) (fun x => a (e x)) := by
  obtain ⟨m, f, g, hf, rfl⟩ := h
  refine ⟨m, fun k x => f k (e x), fun k => γ.symm (g k), fun k => pull_mem e (hf k), ?_⟩
  funext x
  simp [pullR, mat, Finset.sum_apply]

theorem inCongruenceModule_pull_equivPoints {T : Subalgebra A (X₀ → A)} {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {π : X₁}
    {a s : X₀ → Matrix (Fin n) (Fin n) A} (h : InMatrixCongruenceModule T rep (e π) a s) :
    InMatrixCongruenceModule (pullT e T) (pullR e γ rep) π (fun x => a (e x)) (fun x => s (e x)) := by
  obtain ⟨m, j, b, hj, rfl⟩ := h
  refine ⟨m, fun k x => j k (e x), fun k x => b k (e x),
    fun k => ⟨pull_mem e (hj k).1, (hj k).2.1, inRing_pull e γ (hj k).2.2⟩, ?_⟩
  funext x
  simp [Finset.sum_apply]

theorem mapRep_comp {B : Type} [CommRing B] (f : A →+* B) (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    mapRep f (ρ.comp γ) = (mapRep f ρ).comp γ := rfl

theorem overK_comp (ρ : Γ₀ →* GL (Fin n) A) (γ : Γ₁ →* Γ₀) :
    overK (ρ.comp γ) = (overK ρ).comp γ := rfl

section Rep
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem isSS_comp {ρ : Representation K Γ₀ V} (h : IsSS ρ) : IsSS (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W fun g v hv => by simpa using hW (γ.symm g) v hv
  exact ⟨W', fun g v hv => h1 (γ g) v hv, h2⟩

theorem absIrrDistinct_comp {ρ : Representation K Γ₀ V} (h : AbsIrrDistinct ρ) :
    AbsIrrDistinct (ρ.comp γ.toMonoidHom : Representation K Γ₁ V) := by
  obtain ⟨ι, i1, i2, Vs, hs, h1, h2, h3, h4⟩ := h
  refine ⟨ι, i1, i2, Vs, fun j g => hs j (γ g), h1, h2, fun j => ?_, fun j j' hj f hf => h4 j j' hj f fun g v => ?_⟩
  · rw [← h3 j]
    congr 1
    exact γ.surjective.range_comp fun g => (ρ g).restrict (hs j g)
  · obtain ⟨g, rfl⟩ := γ.surjective g
    exact hf g v

theorem isInv_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} :
    IsInv (ρ.comp γ.toMonoidHom) W ↔ IsInv ρ W :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := γ.surjective g; exact h g, fun h g => h (γ g)⟩

theorem isSSRep_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} (h : IsSSRep ρ) : IsSSRep (ρ.comp γ.toMonoidHom) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_comp γ).1 hW)
  exact ⟨W', (isInv_comp γ).2 h1, h2⟩

theorem isIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : IsIrrSub ρ W) :
    IsIrrSub (ρ.comp γ.toMonoidHom) W :=
  ⟨h.1, (isInv_comp γ).2 h.2.1, fun W' h1 h2 => h.2.2 W' h1 ((isInv_comp γ).1 h2)⟩

theorem absIrrSub_comp {a : ℕ} {ρ : Γ₀ →* GL (Fin a) K} {W : Submodule K (Fin a → K)} (h : AbsIrrSub ρ W) :
    AbsIrrSub (ρ.comp γ.toMonoidHom) W := by
  unfold AbsIrrSub at h ⊢
  rw [mapRep_comp]
  exact isIrrSub_comp γ h

end Rep

variable [IsDomain A] [IsLocalRing A]

theorem setting_pull {T : Subalgebra A (X₀ → A)} {Z₀ : Finset X₀} {Z₁ : Finset X₁} (hZ : ∀ x ∈ Z₁, e x ∈ Z₀)
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)}
    (h : HidaSetting t T Z₀ rep ρ χ) :
    HidaSetting t (pullT e T) Z₁ (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨((pull A e).subalgebraMap T).toRingEquiv.isLocalRing, fun x y hxy => ?_, fun x => ?_,
    fun g d => pull_mem e (h4 (γ g) d), fun x => ?_, fun x y g => h6 (e x) (e y) (γ g),
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨f, hf, hne⟩ := h2 (e x) (e y) (e.injective.ne hxy)
    exact ⟨_, pull_mem e hf, hne⟩
  · rw [pullR, overK_comp]
    exact isSS_comp γ (h3 (e x))
  · rw [pullR, overK_comp]
    exact absIrrDistinct_comp γ (h5 (e x))
  · obtain ⟨d, hd⟩ := h7 _ (hZ x hx)
    exact ⟨d, fun g => hd (γ g)⟩
  · rw [pullR, mapRep_comp]
    exact absIrrSub_comp γ (h8 _ (hZ x hx))

omit [IsLocalRing A] in
theorem isChoice_pull {T : Subalgebra A (X₀ → A)}
    {rep : X₀ → (Γ₀ →* GL (Fin n) A)} {ρ : X₀ → (Γ₀ →* GL (Fin r) A)} {χ : ℕ → (Γ₀ →* Aˣ)} {π : X₁} {g : Γ₁} {L : ℕ}
    {eB e1 X0 : X₀ → Matrix (Fin n) (Fin n) A} (h : IsChoice t T rep ρ χ (e π) (γ g) L eB e1 X0) :
    IsChoice t (pullT e T) (pullR e γ rep) (pullR e γ ρ) (fun c => (χ c).comp γ.toMonoidHom) π g L
      (fun x => eB (e x)) (fun x => e1 (e x)) (fun x => X0 (e x)) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨d, hd, hd'⟩, ⟨ϖ, s, hϖ, hs, hX⟩, h9⟩ := h
  refine ⟨⟨inRing_pull e γ h1, inRing_pull e γ h2, funext fun x => congrFun h3 (e x), funext fun x => congrFun h4 (e x),
    funext fun x => congrFun h5 (e x), funext fun x => congrFun h6 (e x)⟩, ⟨d, fun g => hd (γ g), hd'⟩,
    ⟨ϖ, fun x => s (e x), hϖ, inCongruenceModule_pull_equivPoints e γ hs, funext fun x => congrFun hX (e x)⟩, fun x => h9 (e x)⟩

end Plain

theorem exists_algebra {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Algebra ℤ_[q] B] [Algebra A B]
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → algebraMap A B (algebraMap _ _ z) = algebraMap _ _ z') :
    ∃ (_ : Algebra ℤ_[q] A), Module.Finite ℤ_[q] A ∧ IsScalarTower ℤ_[q] A B := by
  subst h
  exact ⟨inferInstance, inferInstance, IsScalarTower.of_algebraMap_eq fun z => (hφ z z HEq.rfl).symm⟩

theorem continuous_of_isLocalHom {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsLocalRing R] [IsLocalRing S]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hS : IsAdic (IsLocalRing.maximalIdeal S))
    (f : R →+* S) [IsLocalHom f] : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, hR.hasBasis_nhds_zero.tendsto_iff hS.hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, fun x hx => ?_⟩
  have h1 : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S :=
    Ideal.map_le_iff_le_comap.2 (fun y hy => map_nonunit f y hy)
  have h2 := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem adjoin_eq_span {A B X : Type} [CommRing A] [CommRing B] (φ : A →+* B) (s : Set (X → A)) :
    Subalgebra.toSubmodule (Algebra.adjoin B ((fun f : X → A => fun x => φ (f x)) '' s)) =
      Submodule.span B ((fun f : X → A => fun x => φ (f x)) '' (Algebra.adjoin A s : Set (X → A))) := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_mono fun f hf => ?_
    induction hf using Submonoid.closure_induction with
    | mem f hf => exact Set.image_mono Algebra.subset_adjoin hf
    | one => exact ⟨1, one_mem _, by ext; simp⟩
    | mul f g _ _ hf hg =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, rfl⟩ := hg
      exact ⟨f * g, mul_mem hf hg, by ext; simp⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    change _ ∈ Algebra.adjoin B _
    induction hf using Algebra.adjoin_induction with
    | mem f hf => exact Algebra.subset_adjoin ⟨f, hf, rfl⟩
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (φ c)
    | add f g _ _ hf hg => convert add_mem hf hg using 1; ext; simp
    | mul f g _ _ hf hg => convert mul_mem hf hg using 1; ext; simp

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁}
  {i₀ : N₀.Loc} {i₁ : N₁.Loc} (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁)

theorem continuous_φ : Continuous a.φ := by
  letI := a.φ.toAlgebra
  obtain ⟨_, _, _⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  haveI : Algebra.IsIntegral (N₀.O i₀) (N₁.O i₁) := Algebra.IsIntegral.tower_top ℤ_[N₁.l i₁]
  haveI : FaithfulSMul (N₀.O i₀) (N₁.O i₁) := (faithfulSMul_iff_algebraMap_injective _ _).2 (Model.φ_injective a)
  haveI : IsLocalHom a.φ := Algebra.IsIntegral.isLocalHom (N₀.O i₀) (N₁.O i₁)
  exact continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem goodR_ext {rep : N₀.X i₀ → (GE N₀ →* GL (Fin R.nV) (N₀.O i₀))} (h : GoodR N₀ i₀ rep) :
    GoodR N₁ i₁ fun x => mapRep a.φ (pullR a.e a.γ rep x) := by
  intro x
  obtain ⟨h1, h2, h3⟩ := h (a.e x)
  refine ⟨(h1.comp a.γ_cont).matrix_map (continuous_φ a), ?_, fun w hw B σ hB hσ => ?_⟩
  · let ψ : Kf N₀ i₀ →+* Kf N₁ i₁ := IsFractionRing.map (Model.φ_injective a)
    have hψ : ∀ z, ψ (algebraMap _ _ z) = algebraMap _ _ (a.φ z) := fun z => by simp [ψ, IsFractionRing.map]
    letI := ψ.toAlgebra
    haveI : CharZero (Kf N₀ i₀) := ((A₀.iotaQC i₀).toRingHom.comp (A₀.iotaQ i₀)).charZero
    have h4 : IsSSRep (mapRep ψ _) := ssAscent (Kf N₀ i₀) (Kf N₁ i₁) _ _ _ (isSSRep_comp a.γ h2)
    convert h4 using 1
    ext g b c
    exact (hψ _).symm
  · obtain ⟨B', hB', hσ'⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
    rw [Model.heckePol_map a x w hw, ← h3 w ((a.out w).1 hw) B' _ hB' hσ', ← Matrix.charpoly_map]
    rfl

theorem T_ext : Subalgebra.toSubmodule (N₁.T i₁) = Submodule.span (N₁.O i₁)
    ((fun f : N₁.X i₁ → N₀.O i₀ => fun x => a.φ (f x)) '' (pullT a.e (N₀.T i₀) : Set _)) := by
  rw [← N₁.T_gen i₁, ← N₀.T_gen i₀, pullT, AlgHom.map_adjoin, ← adjoin_eq_span]
  congr 2
  ext f
  constructor
  · rintro ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).1 ⟨h1, h2, h3, h4⟩
    exact ⟨_, ⟨_, ⟨v, k, k1, k2, k3, k4, h5, h6, rfl⟩, rfl⟩, funext fun x => (a.hT v k x ⟨h1, h2, h3, h4⟩ h5 h6).symm⟩
  · rintro ⟨_, ⟨_, ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨k1, k2, k3, k4⟩ := (a.out v).2 ⟨h1, h2, h3, h4⟩
    exact ⟨v, k, k1, k2, k3, k4, h5, h6, funext fun x => (a.hT v k x ⟨k1, k2, k3, k4⟩ h5 h6).symm⟩

end Record

theorem takenWild_of_locExt : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  intro R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a S hC hS
  obtain ⟨rep, ρ, hG, hSet, hch⟩ := hC
  letI := a.φ.toAlgebra
  obtain ⟨j1, j2, j3⟩ := exists_algebra a.l_eq (N₀.O i₀) (N₁.O i₁) a.φ_alg
  refine ⟨_, fun x => mapRep a.φ (pullR a.e a.γ ρ x), goodR_ext a hG, N₀.O i₀, inferInstance, inferInstance,
    inferInstance, j1, j2, inferInstance, j3, pullT a.e (N₀.T i₀), pullR a.e a.γ rep, pullR a.e a.γ ρ,
    fun c => (N₀.chi i₀ c).comp a.γ.toMonoidHom,
    ⟨Model.φ_injective a, T_ext a, fun _ => rfl, fun _ _ => rfl, a.chi⟩,
    setting_pull a.e a.γ (fun x => (a.Z x).1) hSet, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, hg, hc, hr⟩ := hch _ ((a.Z π).1 hπ)
  obtain ⟨g, rfl⟩ := a.γ.surjective g0
  refine ⟨g, L, _, _, _, (Model.localisationCoefficientExtension_isWildInertiaCyclotomic_iff a g).2 hg, isChoice_pull a.e a.γ hc, fun x => ?_⟩
  obtain ⟨α, hα, hP⟩ := hr (a.e x)
  choose β hβ using fun c => hS (α c) (hα c)
  refine ⟨β, ?_⟩
  apply Polynomial.map_injective ((A₁.iotaQC i₁).toRingHom.comp (A₁.iotaQ i₁)) (RingHom.injective _)
  rw [Polynomial.map_map, Polynomial.map_prod]
  refine Eq.trans ?_ (hP.trans ?_)
  · congr 1
    exact RingHom.ext a.φ_iota
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [← hβ c]

end GlobalTheory.CoefDuty.Take

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFixAlt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.UnramInertia

theorem norm_sub_lt_one_of_fix : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l), (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) →
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  intro l _ σ hσ x hx
  have hmem : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 hσ
  exact GlobalTheory.FrobGen.norm_sub_lt hmem x hx

end GlobalTheory.UnramInertia
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

noncomputable section

namespace GlobalTheory.HostImage

theorem host_image_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  intro D i w hw x
  have h := UpperTheory.Small.factorization_condN_le D.host (D.nd.lPrime i).out
  refine UpperTheory.Small.image_mem_Kur_sup D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) ?_ x
  by_cases h2 : D.nd.l i = 2
  · rw [D.nd.restNLevelExponent_of_two i h2, ← h2]
    exact h.2 h2
  · rw [D.nd.restNLevelExponent_of_odd i h2]
    exact h.1

end GlobalTheory.HostImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnityStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  first | exact @GlobalTheory.HostImage.host_image_mem | exact GlobalTheory.HostImage.host_image_mem | (intros; apply GlobalTheory.HostImage.host_image_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCycZEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.Cyc

theorem isCyc_map_cycZ (l : ℕ) [Fact l.Prime] :
    IsCyc ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l)) := by
  intro g m ζ hζ
  haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨_, ?_, cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩
  set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz
  change ‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _
  have h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

theorem exists_inertia_cycZ_eq : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ σ : GQ l, (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) ∧ cycZ (F := ℚ_[l]) (Ω := Om l) l σ = u := by
  intro l _ u
  have hχ := isCyc_map_cycZ l
  set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef
  have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
  have hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])} :=
    isClosed_eq hχ.continuous continuous_const
  have key := hs.isCompact.inter_iInter_nonempty
    (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l)))
    (fun x => by
      haveI := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))
      exact IntermediateField.fixingSubgroup_isClosed _)
    (fun t => by
      let S : Set (Om l) := (fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))
      haveI : Finite S := (t.finite_toSet.image _).to_subtype
      let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S,
        IntermediateField.finiteDimensional_adjoin
          (fun x _ => Algebra.IsIntegral.isIntegral x)⟩
      obtain ⟨g, hg, hgu⟩ := exists_chi_eq K χ hχ _ hu1
      refine ⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩
      refine (mem_fixingSubgroup_adjoin_iff _ g).2 ?_
      rintro y rfl
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)
  obtain ⟨g, hgu, hg⟩ := key
  refine ⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩
  exact (mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl

end GlobalTheory.Cyc
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.EpsInertia

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem mem_GK (σ : GQ l) (h : ∀ x : E, σ (Bw.j (algebraMap E Ω x)) = Bw.j (algebraMap E Ω x)) :
    σ ∈ GK Bw.Kw := by
  have hc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun x => (spectralNorm_eq_of_equiv σ x).symm).continuous
  rintro ⟨x, hx⟩
  have hcl : closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {y | σ y = y} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact h y) (isClosed_eq hc continuous_id)
  exact hcl (Bw.j_dense hx)

theorem cycZ_bridge [IsAlgClosed Ω] (g : ↥Gw) :
    cycZ E Ω l (g : Ω ≃ₐ[E] Ω) = cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := Bw.j.charZero
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective Bw.j.injective
  have ha : (g : Ω ≃ₐ[E] Ω) ζ =
      ζ ^ (((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω (g : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one
  have hb : ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) (Bw.j ζ) = Bw.j ζ ^
      (((cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut (GQ l) (Om l) ((Bw.e g : ↥(GK Bw.Kw)) : GQ l)) _ hζ'.pow_eq_one
  rw [Bw.e_comm, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

end Bridge

theorem fix_roots {l : ℕ} [Fact l.Prime] (σ : GQ l) (s : ℕ) (z : ℤ_[l])
    (h : ((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * z) (y : Om l)
    (hy : y ^ l ^ s = 1) : σ y = y := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hb : σ y = y ^ (((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow s).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) _ hy
  have h0 : ((l : ZMod (l ^ s))) ^ s = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h, map_add (f := _), map_one, map_mul, map_pow, map_natCast, h0, zero_mul, add_zero, ZMod.val_one_eq_one_mod] at hb
  rw [hb, ← pow_eq_pow_mod 1 hy, pow_one]

theorem epsAll : ∀ (D : D7) (i : D.nd.Loc), EpsAll D i := by
  intro D i w hw z
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hs : D.nd.s0 i ≠ 0 := by
    have := UpperTheory.KStar.S0.one_le_localLevel D.nd i
    omega
  have hu : IsUnit (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z) := by
    rw [← sub_neg_eq_add]
    refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
    have h1 := (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    exact PadicInt.irreducible_p.not_isUnit h1
  obtain ⟨u, hu⟩ := hu
  obtain ⟨σ, hσK, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ GK (D.nbr i w hw).Kw := by
    refine mem_GK _ σ fun x => ?_
    have hle : MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i]
        {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      have hm : ∀ y, σ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := fun y hy => by
        rintro ⟨_, k, rfl⟩
        exact (MulAction.stabilizer (GQ (D.nd.l i)) y).zpow_mem hy k
      refine sup_le (fun y hy => hm y (hσK y hy)) (IntermediateField.adjoin_le_iff.2 fun y hy => hm y ?_)
      exact fix_roots σ _ z (by rw [hσu, hu]) y hy
    exact hle (GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity D i w hw x) ⟨σ, Subgroup.mem_zpowers σ⟩
  set g := (D.nbr i w hw).e.symm ⟨σ, hσ⟩ with hg
  have he : (((D.nbr i w hw).e g : ↥(GK (D.nbr i w hw).Kw)) : GQ (D.nd.l i)) = σ := by
    rw [hg, MulEquiv.apply_symm_apply]
  refine ⟨g.1, ⟨g.2, fun x hx => ?_⟩, by rw [cycZ_bridge (D.nbr i w hw) g, he, hσu, hu]⟩
  have h1 := GlobalTheory.UnramInertia.norm_sub_lt_one_of_fix _ σ hσK _
    ((D.nbr_ind i w hw x).1 (((D.nd.plOm.1 w).valuation_le_one_iff x).1 hx))
  rw [← he, (D.nbr i w hw).e_comm, ← map_sub] at h1
  set y := g.1 x - x
  by_cases hy : y = 0
  · rw [hy, map_zero]; exact zero_lt_one
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, h, not_le]
  exact h1

end GlobalTheory.EpsInertia

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_iterate_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h →
      ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) →
        ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  intro l _ P AI T h hh c hc hF
  obtain ⟨E, ω, hEle, hEdim, hEfix, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l h hh
  have hK0 : K0 E = E.1 := inf_eq_left.2 hEle
  have hdim : Module.finrank ℚ_[l] ↥(K0 E) = h := by rw [hK0]; exact hEdim
  have hper : Function.IsPeriodicPt (⇑P.φB) h c := hc
  have hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0 := by
    intro j
    have hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c := by
      conv_lhs => rw [← Nat.mod_add_div j h]
      rw [Function.iterate_add_apply, (hper.mul_const (j / h)).eq]
    have h1 := hF (j % h) (Nat.mod_lt _ hh)
    rw [← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]
    exact h1
  obtain ⟨a, ha⟩ := GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall
  refine ⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩
  · exact (hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1
  · rw [ha]; rfl

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  first | exact @GlobalTheory.PMon.unr_of_iterate_fixed | exact GlobalTheory.PMon.unr_of_iterate_fixed | (intros; apply GlobalTheory.PMon.unr_of_iterate_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

def dpDen (e i n : ℕ) : ℕ := i.factorial * (n / e).factorial

theorem dpDen_pos (e i n : ℕ) : 0 < dpDen e i n := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofW (w : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n => algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K)

def QSet : Set (ZMod a → K⟦X⟧⟦X⟧) := Set.range (ofW t K e)

theorem coeff_ofW (w : ℕ × ℕ → Wq l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (ofW t K e w τ)) = algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K) := by
  simp [ofW, coeff_mk]

variable {K}

def GoodSet (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {z | z ∈ QSet t K e ∧ frob2 φ₂ z ∈ QSet t K e ∧
    ∃ B ∈ QSet t K e, frob2 φ₂ z = z ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B}


variable (K) in
def cstW (c : Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ => C (C (algebraMap O K (emb t τ c)))

end Q

variable (a : ℕ) (K : Type) [NormedField K]

def uFam : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C X

def dFam (e q : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((q.factorial : K)⁻¹) * X ^ (e * q))

def xFam (i : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((i.factorial : K)⁻¹)) * X ^ i

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_toDisc_add_le_max (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : A) :
    ‖toDisc l u ρ (a + b)‖ ≤ max ‖toDisc l u ρ a‖ ‖toDisc l u ρ b‖ := by
  have h1 : ∀ c, ‖toDisc l u ρ c‖ = gauge l u ρ (algebraMap A (PreDisc l u ρ) c) := fun c => norm_ofPre l u ρ _
  rewrite [h1, h1, h1, map_add]
  exact gauge_add_le_max l u ρ _ _

theorem norm_hf_g_X_and_φ_le :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
      (f g : Hom bk.prism B),
      ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) g X)‖ ≤ bk.ρ₀ ∧
        ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (B.D.φ (BK.hf (bk := bk) f X))‖ ≤ bk.ρ₀ := by
  intro l _ K bk B f g
  obtain ⟨hρ0, hρ1, hlρ, hE⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk B.A (BK.hf (bk := bk) f)
  have hd : BK.hf (bk := bk) f bk.E ∣ BK.hf (bk := bk) g X - BK.hf (bk := bk) f X := by
    obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
    obtain ⟨_, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
    rw [← Ideal.mem_span_singleton, ← hfI]
    exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)
  have h : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X ^ 1)‖ ≤ (bk.ρ₀ : ℝ) ^ 1 := norm_toDisc_pow_le 1 hρ0
  have hX : ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f X)‖ ≤ bk.ρ₀ := by simpa only [pow_one] using h
  have key : ∀ a b : B.A, ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (a + b)‖ ≤
      max ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ a‖ ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ b‖ :=
    norm_toDisc_add_le_max l (BK.hf (bk := bk) f X) bk.ρ₀
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := hd
    have e : BK.hf (bk := bk) g X = BK.hf (bk := bk) f X + BK.hf (bk := bk) f bk.E * w := eq_add_of_sub_eq' hw
    rewrite [e]
    refine (key _ _).trans (max_le hX ?_)
    rewrite [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ (BK.hf (bk := bk) f bk.E)‖ * ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ w‖
        ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hE (norm_toDisc_le w) (norm_nonneg _) (by positivity)
      _ ≤ bk.ρ₀ := (mul_one _).trans_le hlρ
  · have e1 : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f (frobS l bk.a X) :=
      (Hom.f_φ f (show bk.prism.A from X)).symm
    have e : B.D.φ (BK.hf (bk := bk) f X) = BK.hf (bk := bk) f X ^ l := by
      rw [e1, frobS_X, map_pow]
    refine (congrArg (fun y => ‖toDisc l (BK.hf (bk := bk) f X) bk.ρ₀ y‖) e).trans_le ((norm_toDisc_pow_le l hρ0).trans ?_)
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  first | exact @GlobalTheory.BSP.norm_hf_g_X_and_φ_le | exact GlobalTheory.BSP.norm_hf_g_X_and_φ_le | (intros; apply GlobalTheory.BSP.norm_hf_g_X_and_φ_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCover
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.cover_po_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C : Obj l ↥(OL K)) (h : Hom B C), Cover h → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q),
    ∃ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a ∧ Function.Injective h'.f := by
  intro l _ K bk d S B C h hc Q a
  obtain ⟨Q', a', h', hpo⟩ := hc.stable.po Q a
  have hc' : Cover h' := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q' h a a' h' hpo).2 hc
  exact ⟨Q', h', a', hpo.comm, (GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q' h' hc').1⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_pushout_of_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C), Cover h → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a ∧ Function.Injective h'.f := by
  first | exact @GlobalTheory.BSP.cover_po_injective | exact GlobalTheory.BSP.cover_po_injective | (intros; apply GlobalTheory.BSP.cover_po_injective <;> assumption)
end
end
