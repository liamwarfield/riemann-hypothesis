module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuBock
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1.MuBock

private theorem sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (K : Subgroup G) (hK : IsClosed (K : Set G)) (hc : commutator G ≤ K)
    (g : G) (hg : g ∉ K) :
    ∃ χ : G → AddCircle (1 : ℚ), IsLocallyConstant χ ∧ (∀ x y, χ (x * y) = χ x + χ y) ∧
      (∀ x ∈ K, χ x = 0) ∧ χ g ≠ 0 := by
  have h := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨K, hK⟩ : ClosedSubgroup G)
  have h' : K = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ K ≤ N} := h
  rw [h', Subgroup.mem_sInf] at hg
  push Not at hg
  obtain ⟨N, ⟨hNo, hKN⟩, hgN⟩ := hg
  have hcN : commutator G ≤ N := hc.trans hKN
  haveI hNn : N.Normal := Subgroup.Normal.of_commutator_le G hcN
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hcN).is_comm.comm
  letI : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hcomm }
  have hne : (Additive.ofMul (g : G ⧸ N)) ≠ 0 := by
    intro e
    exact hgN ((QuotientGroup.eq_one_iff g).1 e)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  refine ⟨fun x => c (Additive.ofMul (x : G ⧸ N)), ?_, ?_, ?_, hc⟩
  · have : IsLocallyConstant (fun x : G => (x : G ⧸ N)) :=
      (IsLocallyConstant.iff_continuous _).2 QuotientGroup.continuous_mk
    exact this.comp (fun y => c (Additive.ofMul y))
  · intro x y
    simp only [QuotientGroup.mk_mul, ofMul_mul, map_add (f := _)]
  · intro x hx
    have : (x : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).2 (hKN hx)
    simp only [this, ofMul_one, map_zero]

private theorem lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G → AddCircle (1 : ℚ)) (h1 : IsLocallyConstant χ) (h2 : ∀ x y, χ (x * y) = χ x + χ y) :
    ∃ (a : G → ℚ) (c : G × G → ℤ), IsLocallyConstant a ∧ IsLocallyConstant c ∧
      (∀ g, (a g : AddCircle (1 : ℚ)) = χ g) ∧ ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h) := by
  have hs : Function.Surjective (fun x : ℚ => (x : AddCircle (1 : ℚ))) := QuotientAddGroup.mk_surjective
  choose σ hσ using hs
  have ha : IsLocallyConstant (fun g => σ (χ g)) := h1.comp σ
  refine ⟨fun g => σ (χ g), fun p => ⌊σ (χ p.1) + σ (χ p.2) - σ (χ (p.1 * p.2))⌋, ha, ?_, fun g => hσ _, ?_⟩
  · have a1 := ha.comp_continuous (continuous_fst : Continuous (Prod.fst : G × G → G))
    have a2 := ha.comp_continuous (continuous_snd : Continuous (Prod.snd : G × G → G))
    have a3 := ha.comp_continuous (continuous_mul : Continuous (fun p : G × G => p.1 * p.2))
    exact ((a1.add a2).sub a3).comp Int.floor
  · intro g h
    have e : ((σ (χ g) + σ (χ h) - σ (χ (g * h)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      have hσ' : ∀ y, ((σ y : ℚ) : AddCircle (1 : ℚ)) = y := hσ
      rw [AddCircle.coe_sub, AddCircle.coe_add, hσ', hσ', hσ', h2, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 e
    simp only [← hn, zsmul_eq_mul, mul_one, Int.floor_intCast]

private theorem divide {G : Type} [Group G] [TopologicalSpace G] (l : ℕ) [Fact l.Prime]
    (a : G → ℚ) (c : G × G → ℤ) (ha : IsLocallyConstant a)
    (hc : ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h)) (f : G → ZMod l) (hf : Continuous f)
    (hfc : ∀ g h, f h - f (g * h) + f g = (c (g, h) : ZMod l)) :
    ∃ ψ : G → AddCircle (1 : ℚ), IsLocallyConstant ψ ∧ (∀ x y, ψ (x * y) = ψ x + ψ y) ∧
      ∀ g, l • ψ g = (a g : AddCircle (1 : ℚ)) := by
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hf' : IsLocallyConstant f := (IsLocallyConstant.iff_continuous _).2 hf
  refine ⟨fun g => (((a g - ((f g).val : ℚ)) / l : ℚ) : AddCircle (1 : ℚ)),
    ha.comp₂ hf' (fun x y => (((x - (y.val : ℚ)) / l : ℚ) : AddCircle (1 : ℚ))), ?_, ?_⟩
  · intro g h
    have e : ((c (g, h) - ((f h).val - (f (g * h)).val + (f g).val : ℤ) : ℤ) : ZMod l) = 0 := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [hfc, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e
    have hk' := congrArg (Int.cast : ℤ → ℚ) hk
    push_cast at hk'
    rw [hc] at hk'
    rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_add, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one]
    field_simp
    linear_combination -hk'
  · intro g
    rw [← sub_eq_zero, ← AddCircle.coe_nsmul, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-((f g).val : ℤ), ?_⟩
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul]
    push_cast
    field_simp
    ring

private theorem cocycle {G : Type} [Group G] [TopologicalSpace G] (l : ℕ) [Fact l.Prime]
    (a : G → ℚ) (c : G × G → ℤ) (hcl : IsLocallyConstant c)
    (hc : ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h)) :
    (fun p => (c p : ZMod l)) ∈ Z2 (charRep (1 : G →* (ZMod l)ˣ)) := by
  refine (mem_cocycles2 _ _).2 ⟨(hcl.comp (Int.cast : ℤ → ZMod l)).continuous, fun g h k => ?_⟩
  have e : c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    have : ((c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hc, hc, hc, hc, mul_assoc]
      ring
    exact_mod_cast this
  have e' := congrArg (Int.cast : ℤ → ZMod l) e
  push_cast at e'
  simpa [charRep_apply] using e'

private theorem add_pow' {G : Type} [Group G] (ψ : G → AddCircle (1 : ℚ))
    (h : ∀ x y, ψ (x * y) = ψ x + ψ y) (x : G) (n : ℕ) : ψ (x ^ n) = n • ψ x := by
  induction n with
  | zero =>
    have := h 1 1
    rw [mul_one] at this
    simpa using this
  | succ n ih => rw [pow_succ, h, ih, succ_nsmul]

private theorem dvd_of_smul (l : ℕ) [Fact l.Prime] (x : AddCircle (1 : ℚ)) (hx : x ≠ 0) (hl : l • x = 0)
    (i : ℤ) (hi : i • x = 0) : (i : ZMod l) = 0 := by
  have e : addOrderOf x = l := addOrderOf_eq_prime hl hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← e]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.2 hi

private theorem core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (l : ℕ) [Fact l.Prime] (C : Subgroup G) (hC : IsClosed (C : Set G))
    (hcC : commutator G ≤ C)
    (hk : ∀ ψ : G → AddCircle (1 : ℚ), IsLocallyConstant ψ → (∀ x y, ψ (x * y) = ψ x + ψ y) → ∀ x ∈ C, ψ x = 0)
    [Finite (H2 (charRep (1 : G →* (ZMod l)ˣ)))] (hcard : Nat.card (H2 (charRep (1 : G →* (ZMod l)ˣ))) ≤ l)
    (s t : G) (hs : s ^ l ∈ C) (ht : t ^ l ∈ C) (hsC : s ∉ C) : ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ C := by
  by_contra hcon
  have hp : l.Prime := Fact.out
  haveI hCn : C.Normal := Subgroup.Normal.of_commutator_le G hcC
  have hfo : IsOfFinOrder (s : G ⧸ C) := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨l, hp.pos, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hs
  haveI : IsClosed (C : Set G) := hC
  let K : Subgroup G := (Subgroup.zpowers (s : G ⧸ C)).comap (QuotientGroup.mk' C)
  have hKc : IsClosed (K : Set G) := by
    haveI : Finite (Subgroup.zpowers (s : G ⧸ C)) := finite_zpowers.2 hfo
    have : IsClosed (Subgroup.zpowers (s : G ⧸ C) : Set (G ⧸ C)) := Set.toFinite _ |>.isClosed
    exact this.preimage QuotientGroup.continuous_mk
  have hCK : C ≤ K := fun x hx => by
    show (x : G ⧸ C) ∈ Subgroup.zpowers (s : G ⧸ C)
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hsK : s ∈ K := Subgroup.mem_zpowers (s : G ⧸ C)
  have htK : t ∉ K := fun h => by
    have h' : (t : G ⧸ C) ∈ Subgroup.zpowers (s : G ⧸ C) := h
    obtain ⟨n, hn⟩ := hfo.mem_powers_iff_mem_zpowers.2 h'
    refine hcon ⟨n, (QuotientGroup.eq_one_iff _).1 ?_⟩
    have hn' : (s : G ⧸ C) ^ n = t := hn
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hn', mul_inv_cancel]
  obtain ⟨χ₁, l1, m1, k1, n1⟩ := sep C hC hcC s hsC
  obtain ⟨χ₂, l2, m2, k2, n2⟩ := sep K hKc (hcC.trans hCK) t htK
  obtain ⟨a₁, c₁, la1, lc1, e1, r1⟩ := lift χ₁ l1 m1
  obtain ⟨a₂, c₂, la2, lc2, e2, r2⟩ := lift χ₂ l2 m2
  let z₁ : Z2 (charRep (1 : G →* (ZMod l)ˣ)) := ⟨_, cocycle l a₁ c₁ lc1 r1⟩
  let z₂ : Z2 (charRep (1 : G →* (ZMod l)ˣ)) := ⟨_, cocycle l a₂ c₂ lc2 r2⟩
  let F : ZMod l × ZMod l → H2 (charRep (1 : G →* (ZMod l)ˣ)) := fun p =>
    Submodule.Quotient.mk (p.1 • z₁ + p.2 • z₂)
  have hF : Function.Injective F := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    have h0 := (Submodule.Quotient.eq _).1 hpq
    obtain ⟨f, hf, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 (Submodule.mem_comap.1 h0)
    obtain ⟨i, hi⟩ := ZMod.intCast_surjective (p₁ - q₁)
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (p₂ - q₂)
    have hla : IsLocallyConstant (fun g => (i : ℚ) * a₁ g + (j : ℚ) * a₂ g) :=
      la1.comp₂ la2 (fun x y => (i : ℚ) * x + (j : ℚ) * y)
    obtain ⟨ψ, lψ, mψ, eψ⟩ := divide l (fun g => (i : ℚ) * a₁ g + (j : ℚ) * a₂ g)
      (fun p => i * c₁ p + j * c₂ p) hla (fun g h => by push_cast; rw [r1, r2]; ring) f hf (fun g h => by
        have := congrFun hd (g, h)
        simp [charRep_apply, z₁, z₂] at this
        push_cast
        rw [hi, hj, this]
        ring)
    have key : ∀ x, x ^ l ∈ C → i • χ₁ x + j • χ₂ x = 0 := fun x hx => by
      have h1 := hk ψ lψ mψ _ hx
      rw [add_pow' ψ mψ, eψ, AddCircle.coe_add, ← zsmul_eq_mul, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_zsmul, e1, e2] at h1
      exact h1
    have hi0 : (i : ZMod l) = 0 := by
      have h1 := key s hs
      rw [k2 s hsK, smul_zero, add_zero] at h1
      exact dvd_of_smul l _ n1 (by rw [← add_pow' χ₁ m1]; exact k1 _ hs) i h1
    have hj0 : (j : ZMod l) = 0 := by
      have h1 := key t ht
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi0
      have h2 : l • χ₁ t = 0 := by rw [← add_pow' χ₁ m1]; exact k1 _ ht
      rw [hk, mul_comm, mul_smul, natCast_zsmul, h2, smul_zero, zero_add] at h1
      exact dvd_of_smul l _ n2 (by rw [← add_pow' χ₂ m2]; exact k2 _ (hCK ht)) j h1
    rw [hi0, eq_comm, sub_eq_zero] at hi
    rw [hj0, eq_comm, sub_eq_zero] at hj
    rw [hi, hj]
  have hle := (Nat.card_le_card_of_injective F hF).trans hcard
  rw [Nat.card_prod, Nat.card_zmod] at hle
  have := hp.two_le
  nlinarith

end UpperTheory.V.Ws.X1.MuBock

theorem UpperTheory.V.Ws.X1.muBock :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → Finite (H2 (charRep (1 : H →* (ZMod l)ˣ))) → Nat.card (H2 (charRep (1 : H →* (ZMod l)ˣ))) ≤ l → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) := by
  intro Γ _ _ _ _ _ _ l _ H hH hfin hcard s hs t ht hsl htl hsC
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH.isCompact
  have hmap : (commutator H).map H.subtype = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  let C : Subgroup H := (⁅H, H⁆ : Subgroup Γ).topologicalClosure.comap H.subtype
  have hC : IsClosed (C : Set H) :=
    (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hcC : commutator H ≤ C := by
    rw [← Subgroup.map_le_iff_le_comap, hmap]
    exact Subgroup.le_topologicalClosure _
  obtain ⟨n, hn⟩ := UpperTheory.V.Ws.X1.MuBock.core l C hC hcC (fun ψ h1 h2 x hx => by
    let φ : H →* Multiplicative (AddCircle (1 : ℚ)) :=
      MonoidHom.mk' (fun x => Multiplicative.ofAdd (ψ x)) (fun x y => by rw [h2, ofAdd_add])
    have hkc : IsClosed (φ.ker : Set H) := (h1.isClopen_fiber 0).isClosed
    have hkc' : IsClosed (φ.ker.map H.subtype : Set Γ) := hH.isClosedMap_subtype_val _ hkc
    have hle : (⁅H, H⁆ : Subgroup Γ) ≤ φ.ker.map H.subtype := by
      rw [← hmap]
      exact Subgroup.map_mono (Abelianization.commutator_subset_ker φ)
    obtain ⟨y, hy, e⟩ := Subgroup.topologicalClosure_minimal _ hle hkc' hx
    have e' : y = x := Subtype.ext e
    rw [← e']
    exact hy) hcard ⟨s, hs⟩ ⟨t, ht⟩ hsl htl hsC
  exact ⟨n, hn⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GenOfMax
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen_of_max {A : Type} [CommGroup A] (l : ℕ)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n)
    (a : ℕ) (z : A) (h1 : z ^ l ^ (a + 1) = 1) (h0 : z ^ l ^ a ≠ 1) :
    ∀ b, b ≤ a + 1 → ∀ s : A, s ^ l ^ b = 1 → s ∈ Subgroup.zpowers z := by
  intro b
  induction b with
  | zero => intro _ s hs; simp at hs; simp [hs]
  | succ b ih =>
    intro hb s hs
    obtain ⟨n, hn⟩ := hl (z ^ l ^ a) (s ^ l ^ b) (by rw [← pow_mul, ← pow_succ, h1])
      (by rw [← pow_mul, ← pow_succ, hs]) h0
    obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
    have h2 : (s / z ^ (l ^ c * n)) ^ l ^ b = 1 := by
      rw [div_pow, hn, ← pow_mul, ← pow_mul, pow_add, mul_right_comm, div_self']
    have h3 := ih (by omega) _ h2
    have h4 := mul_mem h3 (Subgroup.npow_mem_zpowers z (l ^ c * n))
    rwa [div_mul_cancel] at h4

private theorem cyc_abs {A : Type} [CommGroup A] (l : ℕ) (hp : l.Prime)
    (hres : ∀ x : A, x ≠ 1 → ∃ U : Subgroup A, U.index ≠ 0 ∧ x ∉ U)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n) :
    ∃ z : A, (∃ a, z ^ l ^ a = 1) ∧ ∀ s : A, (∃ a, s ^ l ^ a = 1) → ∃ n : ℕ, s = z ^ n := by
  classical
  by_cases hx : ∃ x : A, x ^ l = 1 ∧ x ≠ 1
  · obtain ⟨x, hx1, hx0⟩ := hx
    obtain ⟨U, hU, hxU⟩ := hres x hx0
    let P : ℕ → Prop := fun a => ∃ s : A, s ^ l ^ (a + 1) = 1 ∧ s ^ l ^ a ≠ 1
    have hP0 : P 0 := ⟨x, by simpa using hx1, by simpa using hx0⟩
    have hbd : ∀ a, P a → a ≤ U.index := by
      rintro a ⟨s, h1, h0⟩
      by_contra hlt
      obtain ⟨n, hn⟩ := hl (s ^ l ^ a) x (by rw [← pow_mul, ← pow_succ, h1]) hx1 h0
      apply hxU
      rw [hn]
      apply pow_mem
      have d1 : orderOf (QuotientGroup.mk' U s) ∣ l ^ (a + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, h1, map_one]
      have d2 : orderOf (QuotientGroup.mk' U s) ∣ U.index := orderOf_dvd_natCard _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 d1
      have d3 : l ^ j ≤ U.index := hj ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hU) d2
      have d4 : j < l ^ j := Nat.lt_pow_self hp.one_lt
      have d5 : orderOf (QuotientGroup.mk' U s) ∣ l ^ a := hj ▸ pow_dvd_pow l (by omega)
      have d6 := orderOf_dvd_iff_pow_eq_one.1 d5
      rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at d6
      exact d6
    obtain ⟨z, h1, h0⟩ : P (Nat.findGreatest P U.index) := Nat.findGreatest_spec (Nat.zero_le _) hP0
    refine ⟨z, ⟨_, h1⟩, ?_⟩
    rintro s ⟨c, hc⟩
    have key : ∀ c, s ^ l ^ c = 1 → s ^ l ^ (Nat.findGreatest P U.index + 1) = 1 := by
      intro c
      induction c with
      | zero => intro h; simp at h; simp [h]
      | succ c ih =>
        intro h
        by_cases h' : s ^ l ^ c = 1
        · exact ih h'
        · have hPc : P c := ⟨s, h, h'⟩
          have := Nat.le_findGreatest (hbd c hPc) hPc
          exact orderOf_dvd_iff_pow_eq_one.1
            ((orderOf_dvd_of_pow_eq_one h).trans (pow_dvd_pow l (by omega)))
    have hm := gen_of_max l hl _ z h1 h0 _ le_rfl s (key c hc)
    have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, h1⟩
    obtain ⟨n, hn⟩ := hf.mem_powers_iff_mem_zpowers.2 hm
    exact ⟨n, hn.symm⟩
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rintro s ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [pow_zero]
    induction c with
    | zero => simpa using hc
    | succ c ih =>
      apply ih
      by_contra h
      exact hx ⟨_, by rw [← pow_mul, ← pow_succ, hc], h⟩

theorem UpperTheory.V.Ws.X1.muCyc :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) → ∃ ζ, MuGen H (muOf l H) ζ := by
  intro Γ _ _ _ _ _ _ l hp H hH hl
  unfold MuGen muOf
  have hcl : IsClosed (((⁅H, H⁆ : Subgroup Γ).topologicalClosure : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure :=
    fun a ha b hb => Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator ha hb)
  generalize (⁅H, H⁆ : Subgroup Γ).topologicalClosure = C at hl hcl hcomm ⊢
  haveI hN : (C.subgroupOf H).Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using mul_mem (hcomm h h.2 c c.2) hc⟩
  let π := QuotientGroup.mk' (C.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ∀ x : H, π x = 1 ↔ (x : Γ) ∈ C := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have h2 : ∀ x y : H, π x = π y ↔ (x : Γ) * (y : Γ)⁻¹ ∈ C := fun x y => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, h1]; simp
  letI : CommGroup (H ⧸ C.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ C.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨a, rfl⟩ := hπ a
        obtain ⟨b, rfl⟩ := hπ b
        rw [← map_mul, ← map_mul, h2]
        simpa [mul_assoc] using hcomm a a.2 b b.2 }
  refine (cyc_abs (A := H ⧸ C.subgroupOf H) l hp.out ?_ ?_).elim ?_
  rotate_left 2
  · rintro z ⟨⟨a, ha⟩, hz⟩
    obtain ⟨z, rfl⟩ := hπ z
    refine ⟨z, ⟨z.2, a, ?_⟩, ?_⟩
    · rw [← map_pow, h1] at ha
      simpa using ha
    · rintro s ⟨hs, c, hc⟩
      obtain ⟨n, hn⟩ := hz (π ⟨s, hs⟩) ⟨c, by rw [← map_pow, h1]; simpa using hc⟩
      rw [← map_pow, h2] at hn
      exact ⟨n, by simpa using hn⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := hπ x
    have ho : IsOpen {g : Γ | (x : Γ) * g ∉ C} :=
      hcl.isOpen_compl.preimage (continuous_const_mul (x : Γ))
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
      (by simpa [← h1] using hx)
    refine ⟨(N.toSubgroup.subgroupOf H).map π, ?_, ?_⟩
    · refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_map_dvd _ hπ)
      haveI : Finite (Γ ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact Subgroup.FiniteIndex.index_ne_zero
    · rintro ⟨n, hn, e⟩
      have hn' : (n : Γ)⁻¹ ∈ N.toSubgroup := inv_mem (Subgroup.mem_subgroupOf.1 hn)
      exact hN hn' ((h2 x n).1 e.symm)
  · intro s t hs ht h0
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    rw [← map_pow, h1] at hs ht
    obtain ⟨n, hn⟩ := hl s s.2 t t.2 (by simpa using hs) (by simpa using ht) (by rwa [← h1])
    exact ⟨n, by rw [← map_pow, h2]; simpa using hn⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.muLoc :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ ζ, MuGen (Dec (F := F) A) (muOf l (Dec (F := F) A)) ζ := by
  intro P F Ω _ _ _ _ _ l _ A hA
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  obtain ⟨-, h1, h2, -⟩ := Kum.placeDict F Ω
  obtain ⟨v, hv⟩ := h1 A (h2 A l hl.ne_zero hA)
  have hc : ReciprocityTheory.Gal.ContAction (charRep (1 : Dec (F := F) A →* (ZMod l)ˣ)) := by
    have e : (fun p : Dec (F := F) A × ZMod l => charRep (1 : Dec (F := F) A →* (ZMod l)ˣ) p.1 p.2) = Prod.snd := by
      funext p
      exact one_mul p.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact continuous_snd
  obtain ⟨-, f2, -, -, e2⟩ := GC.locEuler P.loc.lf P.loc.lt P.loc.le F Ω l v A hv (ZMod l) (ZMod l) _ hc
  refine X1.muCyc l _ (isClosed_Dec A) (X1.muBock l _ (isClosed_Dec A) (Module.finite_of_finite (ZMod l)) ?_)
  rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod, e2]
  refine (Nat.pow_le_pow_right hl.pos ((Submodule.finrank_le _).trans ?_)).trans_eq (pow_one l)
  rw [Subspace.dual_finrank_eq, Module.finrank_self]
