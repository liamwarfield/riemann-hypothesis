module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOpenCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolConjEqOneOfMassCNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConj
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section ConjInvariance

variable {H : Type} [Group H]

theorem mem_map_conj_iff (B : Subgroup H) (x y : H) :
    y ∈ B.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ B := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨x⁻¹ * y * x, hy, by simp [mul_assoc]⟩

theorem map_conj_mul (B : Subgroup H) (x s : H) :
    (B.map (MulAut.conj s).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      B.map (MulAut.conj (x * s)).toMonoidHom := by
  ext y
  simp only [mem_map_conj_iff, mul_inv_rev]
  simp [mul_assoc]

def stabInv (A B : Subgroup H) (x : H) : ℚ :=
  ((Nat.card (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H) : ℕ) : ℚ)⁻¹

theorem stabInv_mul (A B : Subgroup H) (x : H) {a b : H} (ha : a ∈ A) (hb : b ∈ B) :
    stabInv A B (a * x * b) = stabInv A B x := by
  unfold stabInv
  have e : (A ⊓ B.map (MulAut.conj (a * x * b)).toMonoidHom : Subgroup H) =
      (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H).map (MulAut.conj a).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_inf, mem_map_conj_iff]
    constructor
    · rintro ⟨hyA, hyB⟩
      refine ⟨A.mul_mem (A.mul_mem (A.inv_mem ha) hyA) ha, ?_⟩
      have := B.mul_mem (B.mul_mem hb hyB) (B.inv_mem hb)
      convert this using 1
      group
    · rintro ⟨hzA, hzB⟩
      refine ⟨?_, ?_⟩
      · have := A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha)
        convert this using 1
        group
      · have := B.mul_mem (B.mul_mem (B.inv_mem hb) hzB) hb
        convert this using 1
        group
  rw [e, Nat.card_congr ((A ⊓ B.map (MulAut.conj x).toMonoidHom).equivMapOfInjective _
    (MulAut.conj a).injective).toEquiv.symm]

theorem stabInv_eq_of_mk_eq (A B : Subgroup H) {x y : H}
    (h : DoubleCoset.mk A B x = DoubleCoset.mk A B y) : stabInv A B x = stabInv A B y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
  exact (stabInv_mul A B x ha hb).symm

def dcMulRight (A B : Subgroup H) (s : H) :
    DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H) ≃
      DoubleCoset.Quotient (A : Set H) (B : Set H) :=
  Quotient.congr (Equiv.mulRight s) (by
    intro x y
    rw [← DoubleCoset.eq'', ← DoubleCoset.eq'', DoubleCoset.eq, DoubleCoset.eq]
    simp only [Equiv.coe_mulRight, mem_map_conj_iff]
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨a, ha, s⁻¹ * k * s, hk, by simp [mul_assoc]⟩
    · rintro ⟨a, ha, k, hk, e⟩
      refine ⟨a, ha, s * k * s⁻¹, by simpa [mul_assoc] using hk, ?_⟩
      have := congrArg (· * s⁻¹) e
      simpa [mul_assoc] using this)

theorem dcMulRight_mk (A B : Subgroup H) (s x : H) :
    dcMulRight A B s (DoubleCoset.mk A (B.map (MulAut.conj s).toMonoidHom) x) =
      DoubleCoset.mk A B (x * s) := rfl

theorem finsum_stabInv_conj (A B : Subgroup H) (s : H) :
    (∑ᶠ q : DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H),
      stabInv A (B.map (MulAut.conj s).toMonoidHom) (Quotient.out q)) =
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (B : Set H), stabInv A B (Quotient.out q) := by
  rw [← finsum_comp_equiv (dcMulRight A B s)]
  refine finsum_congr fun q => ?_
  unfold stabInv
  rw [map_conj_mul]
  refine stabInv_eq_of_mk_eq A B ?_
  rw [← dcMulRight_mk, DoubleCoset.out_eq', DoubleCoset.out_eq']

end ConjInvariance

theorem massC_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T →
    massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  intro G _ Γ' T C t ht _
  have hsub : (C.map (MulAut.conj t).toMonoidHom).subgroupOf T =
      (C.subgroupOf T).map (MulAut.conj (⟨t, ht⟩ : T)).toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_map_conj_iff, mem_map_conj_iff, Subgroup.mem_subgroupOf]
    simp
  unfold massC
  rw [hsub]
  exact finsum_stabInv_conj _ _ _

end GlobalTheory.LKCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConjStatement
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T → massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.massC_map_conj | exact GlobalTheory.LKCount.massC_map_conj | (intros; apply GlobalTheory.LKCount.massC_map_conj <;> assumption)
end
end

open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport
open GlobalTheory.LKCount

namespace GlobalTheory

theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' (H := A) (K := B) q1, ← DoubleCoset.out_eq' (H := A) (K := B) q2]
    obtain ⟨g, hg, k, hk, he⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupportStatement
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∀ y : G, F y ≠ 0 → massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  first | exact @GlobalTheory.massC_ne_zero_of_support | exact GlobalTheory.massC_ne_zero_of_support | (intros; apply GlobalTheory.massC_ne_zero_of_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroup
open GlobalTheory.LKCount

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

noncomputable def foldMap (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G)
    (p : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :
    {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) //
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y} :=
  ⟨DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y), by
    obtain ⟨g, hg, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    rw [he, DoubleCoset.eq]
    refine ⟨(g * ((Quotient.out p : T) : G))⁻¹, T.inv_mem (T.mul_mem (hΓT hg) (Quotient.out p).2),
      k⁻¹, K.inv_mem hk, by group⟩⟩

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory

variable {G : Type} [Group G] in
private lemma mem_map_conj_iff_inv_mul_mul_mem' (K : Subgroup G) (a x : G) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {G : Type} [Group G] in
private lemma foldMap_bijective' (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G) :
    Function.Bijective (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y) := by
  constructor
  · intro p p' h
    have h' : DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) =
        DoubleCoset.mk Γ' K (((Quotient.out p' : T) : G) * y) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, he⟩ := DoubleCoset.eq.mp h'
    have hmem : y * k * y⁻¹ = ((Quotient.out p : T) : G)⁻¹ * γ⁻¹ * ((Quotient.out p' : T) : G) := by
      rw [eq_mul_inv_of_mul_eq he]; group
    have hT : y * k * y⁻¹ ∈ T := by
      rw [hmem]
      exact T.mul_mem (T.mul_mem (T.inv_mem (Quotient.out p).2) (T.inv_mem (hΓT hγ))) (Quotient.out p').2
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' p', DoubleCoset.eq]
    refine ⟨⟨γ, hΓT hγ⟩, by rw [Subgroup.mem_subgroupOf]; exact hγ, ⟨y * k * y⁻¹, hT⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem']
      refine ⟨hT, ?_⟩
      rw [show y⁻¹ * (y * k * y⁻¹) * y = k by group]
      exact hk
    · apply Subtype.ext
      push_cast
      rw [eq_mul_inv_of_mul_eq he]
      group
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht, k, hk, hqe⟩ := DoubleCoset.eq.mp hq.symm
    refine ⟨DoubleCoset.mk (Γ'.subgroupOf T) ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T)
      ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change DoubleCoset.mk Γ' K (((Quotient.out (DoubleCoset.mk (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩) : T) : G) * y) = q
    obtain ⟨γ, hγ, h, hh, hout⟩ := DoubleCoset.mk_out_eq_mul (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩
    rw [hout, ← DoubleCoset.out_eq' q, DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem'] at hh
    refine ⟨(γ : G)⁻¹, Γ'.inv_mem hγ, (y⁻¹ * h * y)⁻¹ * k, K.mul_mem (K.inv_mem hh.2) hk, ?_⟩
    rw [hqe]
    push_cast
    group

variable {G : Type} [Group G] in
private lemma card_subgroupOf_inf_map_conj_eq (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (t : T) (y : G) :
    Nat.card (Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom : Subgroup T) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom : Subgroup G) := by
  set S : Subgroup T := Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom
  have e : S.map T.subtype = Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', Subgroup.mem_map]
    have hconj : ∀ s : T, (((MulAut.conj t).symm s : T) : G) = (t : G)⁻¹ * s * t := by
      intro s
      rw [MulAut.conj_symm_apply]
      push_cast
      rfl
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj] at hs
      refine ⟨hs.1, ?_⟩
      rw [show ((t : G) * y)⁻¹ * (T.subtype s) * ((t : G) * y) = y⁻¹ * ((t : G)⁻¹ * s * t) * y by
        simp only [Subgroup.coe_subtype]; group]
      exact hs.2.2
    · rintro ⟨hx, hxK⟩
      refine ⟨⟨x, hΓT hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj]
      refine ⟨hx, T.mul_mem (T.mul_mem (T.inv_mem t.2) (hΓT hx)) t.2, ?_⟩
      rw [show y⁻¹ * ((t : G)⁻¹ * x * t) * y = ((t : G) * y)⁻¹ * x * ((t : G) * y) by group]
      exact hxK
  rw [← e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).toEquiv

variable {G : Type} [Group G] in
private lemma card_inf_map_conj_mul_mul_eq (Γ' K : Subgroup G) {γ k : G} (hγ : γ ∈ Γ') (hk : k ∈ K) (a : G) :
    Nat.card (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom : Subgroup G) := by
  have e : (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h1 : (γ * a * k)⁻¹ * x * (γ * a * k) = k⁻¹ * (a⁻¹ * (γ⁻¹ * x * γ) * a) * k := by group
    rw [h1, Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk),
      Subgroup.mul_mem_cancel_right Γ' hγ, Subgroup.mul_mem_cancel_left Γ' (Γ'.inv_mem hγ)]
  rw [e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj γ).injective).toEquiv.symm

theorem _root_.GlobalTheory.finsum_fold_intermediate : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((_root_.GlobalTheory.LKCount.massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  intro G _ Γ' T K F hΓT hF _ hfin
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) =>
      ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
        F (Quotient.out q)).Finite :=
    hfin.subset fun q hq => right_ne_zero_of_mul hq
  refine (_root_.GlobalTheory.finsum_fiberwise_of_finite_support (A := DoubleCoset.Quotient (Γ' : Set G) (K : Set G))
    (B := DoubleCoset.Quotient (T : Set G) (K : Set G))
    (fun q => DoubleCoset.mk T K (Quotient.out q)) _ hsupp).trans (finsum_congr fun y' => ?_)
  set y := Quotient.out y'
  have hy' : DoubleCoset.mk T K y = y' := DoubleCoset.out_eq' y'
  have hfib : ∀ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y → F (Quotient.out q) = F y := by
    intro q hq
    obtain ⟨t, ht, k, hk, hqe⟩ := DoubleCoset.eq.mp hq.symm
    rw [hqe, hF t ht y k hk]
  let e : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T) →
      {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) // DoubleCoset.mk T K (Quotient.out q) = y'} :=
    fun p => ⟨(_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).1,
      (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).2.trans hy'⟩
  have hb := foldMap_bijective' Γ' T K hΓT y
  have he : Function.Bijective e := by
    constructor
    · intro p p' h
      have h' := congrArg Subtype.val h
      exact hb.1 (Subtype.ext h')
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := hb.2 ⟨q, hq.trans hy'.symm⟩
      have hp' := congrArg Subtype.val hp
      exact ⟨p, Subtype.ext hp'⟩
  rw [← finsum_eq_of_bijective e he (fun _ => rfl)]
  have hterm : ∀ p, ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out (e p).1)).toMonoidHom :
      Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out (e p).1) =
      ((Nat.card ((Γ'.subgroupOf T) ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj (Quotient.out p)).toMonoidHom : Subgroup T) : ℕ) : ℂ)⁻¹ * F y := by
    intro p
    obtain ⟨γ, hγ, k, hk, hg⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    have hval : (e p).1 = DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) := rfl
    rw [card_subgroupOf_inf_map_conj_eq Γ' T K hΓT, hval, hg, card_inf_map_conj_mul_mul_eq Γ' K hγ hk,
      show γ * (((Quotient.out p : T) : G) * y) * k = (γ * ((Quotient.out p : T) : G)) * y * k by group,
      hF _ (T.mul_mem (hΓT hγ) (Quotient.out p).2) y k hk]
  rw [finsum_congr hterm]
  by_cases hFy : F y = 0
  · simp [hFy]
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} :=
    hfin.to_subtype
  haveI : Finite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :=
    Finite.of_injective
      (β := {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0})
      (fun p => ⟨(e p).1, by
        show F (Quotient.out (e p).1) ≠ 0
        rw [hfib _ ((e p).2.trans hy'.symm)]
        exact hFy⟩)
      (fun p p' h => by
        have h' := congrArg Subtype.val h
        exact he.1 (Subtype.ext h'))
  letI := Fintype.ofFinite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T))
  unfold _root_.GlobalTheory.LKCount.massC
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_mul, Rat.cast_sum]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroupStatement
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  first | exact @GlobalTheory.finsum_fold_intermediate | exact GlobalTheory.finsum_fold_intermediate | (intros; apply GlobalTheory.finsum_fold_intermediate <;> assumption)
end
end

open GlobalTheory.LKCount

noncomputable section
open scoped Classical

namespace GlobalTheory.LKCountPoint

section Gen
variable {G : Type} [Group G]

theorem mem_map_conj {K : Subgroup G} {a z : G} :
    z ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * z * a ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  ext z
  simp only [mem_map_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inf_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) (K : Subgroup G) :
    (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K.map (MulAut.conj t).toMonoidHom := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht, h2⟩

theorem relIndex_inf_inf_ne_zero (H : Subgroup G) {U K : Subgroup G} (h : U.relIndex K ≠ 0) :
    (H ⊓ U).relIndex (H ⊓ K) ≠ 0 := by
  have := Subgroup.relIndex_inter_ne_zero h H
  rwa [inf_comm U H, inf_comm K H] at this

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem prod_map_conj (A : Subgroup G₁) (B : Subgroup G₂) (x : G₁ × G₂) :
    (A.prod B).map (MulAut.conj x).toMonoidHom =
      (A.map (MulAut.conj x.1).toMonoidHom).prod (B.map (MulAut.conj x.2).toMonoidHom) := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

theorem twCent_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (a : G₁) (b : G₂) :
    GlobalTheory.BCT.twCent (θ₁.prodMap θ₂) (a, b) = (GlobalTheory.BCT.twCent θ₁ a).prod (GlobalTheory.BCT.twCent θ₂ b) := by
  ext z
  rw [Subgroup.mem_prod]
  show z * (a, b) = (a, b) * (θ₁.prodMap θ₂) z ↔ z.1 * a = a * θ₁ z.1 ∧ z.2 * b = b * θ₂ z.2
  rw [Prod.ext_iff]
  exact Iff.rfl

theorem relIndex_prod (A C : Subgroup G₁) (B D : Subgroup G₂) :
    (A.prod B).relIndex (C.prod D) = A.relIndex C * B.relIndex D := by
  have e : (A.prod B).subgroupOf (C.prod D) =
      ((A.subgroupOf C).prod (B.subgroupOf D)).comap (Subgroup.prodEquiv C D).toMonoidHom := by
    ext z
    exact Iff.rfl
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv C D).surjective,
    Subgroup.index_prod]
  rfl

theorem vol_prod (C₁ H₁ : Subgroup G₁) (C₂ H₂ : Subgroup G₂) :
    vol (C₁.prod C₂) (H₁.prod H₂) = vol C₁ H₁ * vol C₂ H₂ := by
  unfold vol
  rw [relIndex_prod, relIndex_prod]
  push_cast
  rw [div_mul_div_comm]

theorem stab_eq {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).comap (ι₁.prod ι₂) := by
  rw [prod_map_conj]
  ext g
  exact Iff.rfl

theorem card_stab {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (hι : Function.Injective (ι₁.prod ι₂)) (x : G₁ × G₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ x) =
      Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) := by
  rw [stab_eq, ← Subgroup.map_comap_eq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv

theorem finite_inter {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) (h : Finite (stab ι₁ ι₂ K₁ K₂ x)) :
    (((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) :
      Set (G₁ × G₂)).Finite := by
  rw [← Subgroup.map_comap_eq, ← stab_eq, Subgroup.coe_map]
  exact Set.Finite.image _ (Set.toFinite _)

end Prod

section Core
variable {G : Type} [Group G]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  simp [mem_map_conj]

theorem vol_self (A : Subgroup G) : vol A A = 1 := by
  simp [vol, Subgroup.relIndex_self]

theorem fold_sum (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
        ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) :=
  GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup Γ' T K F hΓT hF hfin hsupp

theorem massC_ne_zero_of_ne (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 :=
  GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support Γ' T K F hΓT hF hfin hsupp y hy

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Core

end GlobalTheory.LKCountPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCountComm

section Gen
variable {G : Type} [Group G]

theorem relIndex_triple_inf_ne_zero_of_relIndex_ne_zero {U V W : Subgroup G} (hV : V.relIndex U ≠ 0) (hW : W.relIndex U ≠ 0) :
    (U ⊓ V ⊓ W).relIndex U ≠ 0 := by
  rw [inf_assoc, Subgroup.inf_relIndex_left]
  exact Subgroup.relIndex_inf_ne_zero hV hW

theorem idxRatio_cocycle_of_commensurable (N : Subgroup G) {U V W : Subgroup G}
    (hUV : U.Commensurable V) (hVW : V.Commensurable W) (hUW : U.Commensurable W) :
    GlobalTheory.FunObj.idxRatio (N ⊓ U) (N ⊓ V) * GlobalTheory.FunObj.idxRatio (N ⊓ V) (N ⊓ W) =
      GlobalTheory.FunObj.idxRatio (N ⊓ U) (N ⊓ W) := by
  have dU : (U ⊓ V ⊓ W).relIndex U ≠ 0 := relIndex_triple_inf_ne_zero_of_relIndex_ne_zero hUV.2.relIndex_ne_zero hUW.2.relIndex_ne_zero
  have dV : (U ⊓ V ⊓ W).relIndex V ≠ 0 := by
    have h := relIndex_triple_inf_ne_zero_of_relIndex_ne_zero (U := V) (V := U) (W := W) hUV.1.relIndex_ne_zero hVW.2.relIndex_ne_zero
    have e : V ⊓ U ⊓ W = U ⊓ V ⊓ W := Subgroup.ext fun z => by simp only [Subgroup.mem_inf]; tauto
    rwa [e] at h
  have dW : (U ⊓ V ⊓ W).relIndex W ≠ 0 := by
    have h := relIndex_triple_inf_ne_zero_of_relIndex_ne_zero (U := W) (V := U) (W := V) hUW.1.relIndex_ne_zero hVW.1.relIndex_ne_zero
    have e : W ⊓ U ⊓ V = U ⊓ V ⊓ W := Subgroup.ext fun z => by simp only [Subgroup.mem_inf]; tauto
    rwa [e] at h
  have nU := GlobalTheory.LKCountPoint.relIndex_inf_inf_ne_zero N dU
  have nV := GlobalTheory.LKCountPoint.relIndex_inf_inf_ne_zero N dV
  have nW := GlobalTheory.LKCountPoint.relIndex_inf_inf_ne_zero N dW
  have sub : ∀ {X Y : Subgroup G}, (N ⊓ (U ⊓ V ⊓ W)).relIndex X ≠ 0 → Y ≤ X →
      (N ⊓ (U ⊓ V ⊓ W)).relIndex Y ≠ 0 :=
    fun hX hYX h => hX (Subgroup.relIndex_eq_zero_of_le_right hYX h)
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  rw [GlobalTheory.FunObj.idxRatio_eq_of_le l1 (sub nU inf_le_left), GlobalTheory.FunObj.idxRatio_eq_of_le l2 (sub nV inf_le_left),
    GlobalTheory.FunObj.idxRatio_eq_of_le l3 (sub nU inf_le_left)]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp

theorem vol_conj_of_commensurable (T K : Subgroup G)
    (hK : ∀ x : G, (K.map (MulAut.conj x).toMonoidHom).Commensurable K)
    {t : G} (ht : t ∈ T) (hvol : vol (T ⊓ K) ((T ⊓ K).map (MulAut.conj t).toMonoidHom) = 1) (x : G) :
    vol (T ⊓ K) ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom) =
      vol (T ⊓ K) (T ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  have hc := idxRatio_cocycle_of_commensurable T ((hK (t * x)).trans (hK t).symm) (hK t) (hK (t * x))
  rw [GlobalTheory.LKCount.OrbKProd.map_conj_mul, GlobalTheory.LKCount.OrbKProd.inf_map_conj T _ ht,
    GlobalTheory.LKCount.OrbKProd.inf_map_conj T _ ht, GlobalTheory.FunObj.idxRatio_map (MulAut.conj t).injective,
    show GlobalTheory.FunObj.idxRatio ((T ⊓ K).map (MulAut.conj t).toMonoidHom) (T ⊓ K) = 1 from hvol, mul_one] at hc
  rw [GlobalTheory.LKCount.OrbKProd.vol_eq_idxRatio, GlobalTheory.LKCount.OrbKProd.vol_eq_idxRatio]
  exact hc.symm

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem commensurable_prod (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (h₁ : ∀ g : G₁, (K₁.map (MulAut.conj g).toMonoidHom).Commensurable K₁)
    (h₂ : ∀ g : G₂, (K₂.map (MulAut.conj g).toMonoidHom).Commensurable K₂) (x : G₁ × G₂) :
    ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).Commensurable (K₁.prod K₂) := by
  rw [GlobalTheory.LKCountPoint.prod_map_conj]
  refine ⟨?_, ?_⟩
  · apply Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
    rw [GlobalTheory.LKCountPoint.relIndex_prod]; exact mul_ne_zero (h₁ x.1).1.relIndex_ne_zero (h₂ x.2).1.relIndex_ne_zero
  · apply Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
    rw [GlobalTheory.LKCountPoint.relIndex_prod]; exact mul_ne_zero (h₁ x.1).2.relIndex_ne_zero (h₂ x.2).2.relIndex_ne_zero

end Prod

section Term
variable {G : Type} [Group G]

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount.OrbKProd

theorem oTerm_inv_of_commensurable (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hK : ∀ x : G, (K.map (MulAut.conj x).toMonoidHom).Commensurable K)
    (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    (hvol : ∀ t ∈ twCent θ δ, vol (twCent θ δ ⊓ K) ((twCent θ δ ⊓ K).map (MulAut.conj t).toMonoidHom) = 1)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    oTerm θ K (twCent θ δ ⊓ K) δ f (t * x * k) = oTerm θ K (twCent θ δ ⊓ K) δ f x := by
  unfold oTerm
  rw [f_inv θ K δ f hf ht hk x, map_conj_mul_three_subgroup_of_mem K hk, GlobalTheory.LKCount.OrbKProd.inf_map_conj _ _ ht,
    vol_conj_of_commensurable _ K hK ht (hvol t ht) x]

theorem oTerm_prod' {G' : Type} [Group G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G')
    (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ) (x : G) (x' : G') :
    oTerm (θ.prodMap θ') (K.prod K') ((twCent θ δ).prod (twCent θ' δ') ⊓ K.prod K') (δ, δ')
        (fun y => f y.1 * f' y.2) (x, x') =
      oTerm θ K (twCent θ δ ⊓ K) δ f x * oTerm θ' K' (twCent θ' δ' ⊓ K') δ' f' x' := by
  unfold oTerm
  rw [GlobalTheory.BCT.OrbProd.twCent_prod, map_conj_prod, prod_inf_prod, prod_inf_prod, GlobalTheory.LKCount.OrbKProd.vol_prod]
  push_cast
  rw [mul_inv, mul_mul_mul_comm]
  rfl

end Term


open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount.OrbKProd in
theorem orbK_prod_of_commensurable {G₁ G₂ : Type} [Group G₁] [Group G₂] (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ₁ : G₁) (δ₂ : G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (hK₁ : ∀ x : G₁, (K₁.map (MulAut.conj x).toMonoidHom).Commensurable K₁)
    (hK₂ : ∀ x : G₂, (K₂.map (MulAut.conj x).toMonoidHom).Commensurable K₂)
    (hf₁ : ∀ k ∈ K₁, ∀ y, f₁ (k⁻¹ * y * θ₁ k) = f₁ y) (hf₂ : ∀ k ∈ K₂, ∀ y, f₂ (k⁻¹ * y * θ₂ k) = f₂ y)
    (hv₁ : ∀ t ∈ twCent θ₁ δ₁, vol (twCent θ₁ δ₁ ⊓ K₁) ((twCent θ₁ δ₁ ⊓ K₁).map (MulAut.conj t).toMonoidHom) = 1)
    (hv₂ : ∀ t ∈ twCent θ₂ δ₂, vol (twCent θ₂ δ₂ ⊓ K₂) ((twCent θ₂ δ₂ ⊓ K₂).map (MulAut.conj t).toMonoidHom) = 1) :
    orbK (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (fun x => f₁ x.1 * f₂ x.2) = orbK θ₁ K₁ δ₁ f₁ * orbK θ₂ K₂ δ₂ f₂ := by
  unfold orbK
  rw [orbC_eq, orbC_eq, orbC_eq, GlobalTheory.BCT.OrbProd.twCent_prod]
  have hz : ∀ z, oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2)
      (Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z)) =
      oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out z.1) *
        oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out z.2) := by
    intro z
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂)) (K₁.prod K₂)
      (Quotient.out z.1, Quotient.out z.2)
    rw [Subgroup.mem_prod] at ha hb
    have e2 : Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z) =
        (a.1 * Quotient.out z.1 * b.1, a.2 * Quotient.out z.2 * b.2) := e
    rw [e2, oTerm_prod', oTerm_inv_of_commensurable θ₁ K₁ δ₁ f₁ hK₁ hf₁ hv₁ ha.1 hb.1,
      oTerm_inv_of_commensurable θ₂ K₂ δ₂ f₂ hK₂ hf₂ hv₂ ha.2 hb.2]
  have hq := finsum_comp_equiv (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂))
    (f := fun q => oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2) (Quotient.out q))
  rw [← hq, finsum_congr hz]
  exact finsum_prod_mul (fun q => oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out q))
    (fun q => oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out q))

section Core
variable {G : Type} [Group G]

theorem core_count_of_commensurable (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hK : ∀ x : G, (K.map (MulAut.conj x).toMonoidHom).Commensurable K)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    (∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ((massC Γ' T (T ⊓ K) : ℚ) : ℂ) *
        ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
          ((vol (T ⊓ K) (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
            F (Quotient.out y)) ∧
    ((∃ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), F (Quotient.out q) ≠ 0) →
      ∀ t ∈ T, vol (T ⊓ K) ((T ⊓ K).map (MulAut.conj t).toMonoidHom) = 1) := by
  have hri1 : ∀ y, (T ⊓ K).relIndex (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := fun y =>
    GlobalTheory.LKCountPoint.relIndex_inf_inf_ne_zero T (hK y).2.relIndex_ne_zero
  have hri2 : ∀ y, (T ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (T ⊓ K) ≠ 0 := fun y =>
    GlobalTheory.LKCountPoint.relIndex_inf_inf_ne_zero T (hK y).1.relIndex_ne_zero
  have hfinC : ∀ t ∈ T, ((Γ' ⊓ (T ⊓ K).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite :=
    fun t _ => (hfin t).subset (SetLike.coe_subset_coe.2 (inf_le_inf_left _ (Subgroup.map_mono inf_le_right)))
  have hfinY : ∀ y, ∀ t ∈ T,
      ((Γ' ⊓ (T ⊓ K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite :=
    fun y t _ => (hfin (t * y)).subset (SetLike.coe_subset_coe.2 (inf_le_inf_left _ (by
      rw [← GlobalTheory.LKCountPoint.map_conj_map_conj]; exact Subgroup.map_mono inf_le_right)))
  have hmc : ∀ y, massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) *
      vol (T ⊓ K) (T ⊓ K.map (MulAut.conj y).toMonoidHom) = massC Γ' T (T ⊓ K) := fun y =>
    GlobalTheory.LKCount.MassChange.massC_mul_vol Γ' T (T ⊓ K) (T ⊓ K.map (MulAut.conj y).toMonoidHom) inf_le_left inf_le_left
      (hri1 y) (hri2 y) hfinC (hfinY y)
  have hvol : ∀ y, vol (T ⊓ K) (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := fun y => by
    unfold vol; exact div_ne_zero (by exact_mod_cast hri1 y) (by exact_mod_cast hri2 y)
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.LKCountPoint.fold_sum Γ' T K F hΓT hF hfin hsupp, mul_finsum]
    refine finsum_congr fun y => ?_
    have hv' : ((vol (T ⊓ K) (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) ≠ 0 := by
      exact_mod_cast hvol (Quotient.out y)
    rw [← hmc (Quotient.out y)]
    push_cast
    rw [mul_assoc, mul_inv_cancel_left₀ hv']
  · rintro ⟨q₀, hq₀⟩ t ht
    have hmC : massC Γ' T (T ⊓ K) ≠ 0 := by
      rw [← hmc (Quotient.out q₀)]
      exact mul_ne_zero (GlobalTheory.LKCountPoint.massC_ne_zero_of_ne Γ' T K F hΓT hF hfin hsupp _ hq₀) (hvol _)
    refine GlobalTheory.LKCount.vol_conj_eq_one_of_massC_ne_zero Γ' T (T ⊓ K) t ht inf_le_left ?_ ?_ hfinC ?_ hmC
    · rw [GlobalTheory.LKCountPoint.map_conj_inf_of_mem ht K]; exact hri1 t
    · rw [GlobalTheory.LKCountPoint.map_conj_inf_of_mem ht K]; exact hri2 t
    · intro s hs
      rw [GlobalTheory.LKCountPoint.map_conj_map_conj]
      exact hfinC (s * t) (T.mul_mem hs ht)

end Core


open GlobalTheory.LKCountPoint in
theorem pointSum_eq_pointSide_of_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ hK₁ hK₂ _ hf₁ hφ hc₁ hc₂ hι hstab hsupp
  have hΓT : (ι₁.prod ι₂).range ≤ GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) := by
    rintro _ ⟨g, rfl⟩
    show (ι₁.prod ι₂) g * (γ, δ) = (γ, δ) * ((MonoidHom.id G₁).prodMap θ) ((ι₁.prod ι₂) g)
    exact Prod.ext (hc₁ g) (hc₂ g)
  have hFinv : ∀ t ∈ GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ), ∀ x : G₁ × G₂, ∀ k ∈ K₁.prod K₂,
      f₁ ((t * x * k).1⁻¹ * γ * (t * x * k).1) * φ ((t * x * k).2⁻¹ * δ * θ (t * x * k).2) =
        f₁ (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2) := by
    intro t ht x k hk
    have ht' : t * (γ, δ) = (γ, δ) * ((MonoidHom.id G₁).prodMap θ) t := ht
    have h1 : t.1 * γ = γ * t.1 := congrArg Prod.fst ht'
    have h2 : t.2 * δ = δ * θ t.2 := congrArg Prod.snd ht'
    have e1 : (t * x * k).1⁻¹ * γ * (t * x * k).1 = k.1⁻¹ * (x.1⁻¹ * (t.1⁻¹ * γ * t.1) * x.1) * k.1 := by
      simp only [Prod.fst_mul]; group
    have e2 : (t * x * k).2⁻¹ * δ * θ (t * x * k).2 =
        k.2⁻¹ * (x.2⁻¹ * (t.2⁻¹ * δ * θ t.2) * θ x.2) * θ k.2 := by
      simp only [Prod.snd_mul, map_mul]; group
    have h1' : t.1⁻¹ * γ * t.1 = γ := by rw [mul_assoc, ← h1, inv_mul_cancel_left]
    have h2' : t.2⁻¹ * δ * θ t.2 = δ := by rw [mul_assoc, ← h2, inv_mul_cancel_left]
    rw [e1, e2, h1', h2', hf₁ _ (Subgroup.mem_prod.1 hk).1, hφ _ (Subgroup.mem_prod.1 hk).2]
  have hfin := fun x => finite_inter ι₁ ι₂ K₁ K₂ x (hstab x)
  have hcore := core_count_of_commensurable (ι₁.prod ι₂).range
    (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ)) (K₁.prod K₂)
    (fun x => f₁ (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)) hΓT (commensurable_prod K₁ K₂ hK₁ hK₂) hFinv hfin hsupp
  have hPS : pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ =
      ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
        ((Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj (Quotient.out q)).toMonoidHom :
          Subgroup (G₁ × G₂)) : ℕ) : ℂ)⁻¹ *
          (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2)) := by
    unfold pointSum
    refine finsum_congr fun q => ?_
    rw [card_stab ι₁ ι₂ K₁ K₂ hι]
  by_cases hne : ∃ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
      f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0
  · have hu := hcore.2 hne
    have hTp : GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) =
        (GlobalTheory.BCT.twCent (MonoidHom.id G₁) γ).prod (GlobalTheory.BCT.twCent θ δ) := twCent_prod _ _ γ δ
    have hCp : GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂ =
        (GlobalTheory.BCT.twCent (MonoidHom.id G₁) γ ⊓ K₁).prod (GlobalTheory.BCT.twCent θ δ ⊓ K₂) := by
      rw [hTp]; ext z; simp only [Subgroup.mem_inf, Subgroup.mem_prod]; tauto
    have hu1 : ∀ t ∈ GlobalTheory.BCT.twCent (MonoidHom.id G₁) γ, vol (GlobalTheory.BCT.twCent (MonoidHom.id G₁) γ ⊓ K₁)
        ((GlobalTheory.BCT.twCent (MonoidHom.id G₁) γ ⊓ K₁).map (MulAut.conj t).toMonoidHom) = 1 := by
      intro t ht
      have hmem : (t, (1 : G₂)) ∈ GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) := by
        rw [hTp]; exact Subgroup.mem_prod.2 ⟨ht, one_mem _⟩
      have h := hu _ hmem
      rw [hCp, prod_map_conj, vol_prod] at h
      dsimp only at h
      rwa [map_conj_one, vol_self, mul_one] at h
    have hu2 : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, vol (GlobalTheory.BCT.twCent θ δ ⊓ K₂)
        ((GlobalTheory.BCT.twCent θ δ ⊓ K₂).map (MulAut.conj t).toMonoidHom) = 1 := by
      intro t ht
      have hmem : ((1 : G₁), t) ∈ GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) := by
        rw [hTp]; exact Subgroup.mem_prod.2 ⟨one_mem _, ht⟩
      have h := hu _ hmem
      rw [hCp, prod_map_conj, vol_prod] at h
      dsimp only at h
      rwa [map_conj_one, vol_self, one_mul] at h
    have hprod := orbK_prod_of_commensurable (MonoidHom.id G₁) θ K₁ K₂ γ δ f₁ φ hK₁ hK₂
      (fun k hk y => hf₁ k hk y) hφ hu1 hu2
    rw [hPS, hcore.1]
    unfold pointSide
    rw [← hprod]
    rfl
  · push_neg at hne
    have hF0 : ∀ x : G₁ × G₂, f₁ (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2) = 0 := by
      intro x
      obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (ι₁.prod ι₂).range (K₁.prod K₂) x
      rw [← hFinv h (hΓT hh) x k hk, ← he]
      exact hne _
    have hor : (∀ x₁ : G₁, f₁ (x₁⁻¹ * γ * x₁) = 0) ∨ (∀ x₂ : G₂, φ (x₂⁻¹ * δ * θ x₂) = 0) := by
      by_contra hc
      push_neg at hc
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
      exact mul_ne_zero ha hb (hF0 (a, b))
    rw [hPS]
    unfold pointSide orbK orbC
    rcases hor with h | h
    · simp [hF0, h]
    · simp [hF0, h]

end GlobalTheory.LKCountComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurableStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitz_pointCount_one_class_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  first | (exact @GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (exact GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (intros; apply GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable  <;> assumption)
end
