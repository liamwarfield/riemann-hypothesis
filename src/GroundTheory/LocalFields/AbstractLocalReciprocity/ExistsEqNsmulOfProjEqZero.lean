module

public import GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger

@[expose] public section

section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
namespace GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

namespace ProfiniteInteger

def multiples (n : ℕ) : AddSubgroup ℤ̂ :=
  (AddMonoidHom.mulLeft (n : ℤ̂)).range

theorem mem_multiples {n : ℕ} {x : ℤ̂} : x ∈ multiples n ↔ ∃ y : ℤ̂, x = n • y := by
  simp only [multiples, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem proj_eq_val_cast {n k : ℕ+} (h : (n : ℕ) ∣ k) (x : ℤ̂) :
    proj n x = ((proj k x).val : ZMod n) := by
  rw [← castHom_proj h x, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem proj_surjective (n : ℕ+) : Function.Surjective (proj n) := fun z =>
  ⟨((z.val : ℕ) : ℤ̂), by rw [map_natCast, ZMod.natCast_zmod_val]⟩

theorem exists_eq_nsmul_of_proj_eq_zero {n : ℕ+} {x : ℤ̂} (hx : proj n x = 0) :
    ∃ y : ℤ̂, x = (n : ℕ) • y := by

  let v : ℕ+ → ℕ := fun m => (proj (n * m) x).val
  have hdvd : ∀ m : ℕ+, (n : ℕ) ∣ v m := by
    intro m
    have h := proj_eq_val_cast (n := n) (k := n * m) (by simp) x
    rw [hx, eq_comm, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hmod : ∀ m k : ℕ+, (m : ℕ) ∣ (k : ℕ) → v k ≡ v m [MOD (n : ℕ) * m] := by
    intro m k hmk
    have h := proj_eq_val_cast (n := n * m) (k := n * k) (by simpa using Nat.mul_dvd_mul_left _ hmk) x
    have h2 : ((v m : ℕ) : ZMod ((n * m : ℕ+) : ℕ)) = proj (n * m) x := ZMod.natCast_zmod_val _
    rw [← h2, ZMod.natCast_eq_natCast_iff, PNat.mul_coe] at h
    exact h.symm
  let yf : ∀ m : ℕ+, ZMod m := fun m => ((v m / n : ℕ) : ZMod m)
  have hy : yf ∈ profiniteIntegers := by
    rw [mem_profiniteIntegers]
    intro m k hmk
    simp only [yf, map_natCast]
    rw [ZMod.natCast_eq_natCast_iff]
    have h := hmod m k hmk
    obtain ⟨a, ha⟩ := hdvd k
    obtain ⟨b, hb⟩ := hdvd m
    rw [ha, hb] at h ⊢
    rw [Nat.mul_div_cancel_left _ n.pos, Nat.mul_div_cancel_left _ n.pos]
    exact Nat.ModEq.mul_left_cancel' n.ne_zero h
  refine ⟨⟨yf, hy⟩, ?_⟩
  ext m
  rw [map_nsmul, nsmul_eq_mul]
  change proj m x = (n : ZMod m) * ((v m / n : ℕ) : ZMod m)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m)]
  exact proj_eq_val_cast (n := m) (k := n * m) (by simp) x

theorem proj_eq_zero_iff {n : ℕ+} {x : ℤ̂} : proj n x = 0 ↔ x ∈ multiples n := by
  rw [mem_multiples]
  refine ⟨exists_eq_nsmul_of_proj_eq_zero, ?_⟩
  rintro ⟨y, rfl⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem ker_proj (n : ℕ+) : (proj n).toAddMonoidHom.ker = multiples n := by
  ext x
  exact proj_eq_zero_iff

theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ̂} (h : n • x = 0) : x = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
  ext m
  rw [map_zero, proj_eq_val_cast (n := m) (k := N * m) (by simp) x, ZMod.natCast_eq_zero_iff]
  have h' := congrArg (proj (N * m)) h
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h'
  have h'' : (((N : ℕ) * (proj (N * m) x).val : ℕ) : ZMod ((N * m : ℕ+) : ℕ)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h'
  rw [ZMod.natCast_eq_zero_iff] at h''
  have h3 : (N : ℕ) * m ∣ (N : ℕ) * (proj (N * m) x).val := by
    rw [← PNat.mul_coe]
    exact h''
  exact Nat.dvd_of_mul_dvd_mul_left N.pos h3

instance : IsAddTorsionFree ℤ̂ where
  eq_of_nsmul_eq_nsmul_of_addCommute n hn x y _ h := by
    rw [← sub_eq_zero]
    apply eq_zero_of_nsmul_eq_zero hn
    rw [nsmul_sub, h, sub_self]

theorem index_multiples (n : ℕ+) : (multiples n).index = n := by
  rw [← ker_proj, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (proj_surjective n)]
  simp

theorem eq_multiples_index {H : AddSubgroup ℤ̂} (hH : H.index ≠ 0) : H = multiples H.index := by
  have hle : multiples H.index ≤ H := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_multiples.1 hx
    exact H.nsmul_index_mem y
  have hidx := AddSubgroup.relIndex_mul_index hle
  have hm := index_multiples ⟨H.index, Nat.pos_of_ne_zero hH⟩
  simp only [PNat.mk_coe] at hm
  rw [hm] at hidx
  have h1 : (multiples H.index).relIndex H = 1 := (Nat.mul_eq_right hH).1 hidx
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle

theorem intCast_mem_multiples_iff {n : ℕ} (hn : 0 < n) {k : ℤ} :
    (k : ℤ̂) ∈ multiples n ↔ (n : ℤ) ∣ k := by
  rw [mem_multiples]
  refine ⟨fun ⟨w, hw⟩ => dvd_of_intCast_eq_nsmul hn hw, ?_⟩
  rintro ⟨c, rfl⟩
  exact ⟨(c : ℤ̂), by push_cast; rw [nsmul_eq_mul]⟩

end ProfiniteInteger

end GroundTheory.LocalField.Abstract
end

section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
namespace GroundTheory.LocalField.Abstract

section FixedModule

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]

def fixedModule (H : Subgroup G) : Subgroup A where
  carrier := {a | ∀ g ∈ H, g • a = a}
  mul_mem' {a b} ha hb g hg := by rw [smul_mul', ha g hg, hb g hg]
  one_mem' g _ := smul_one g
  inv_mem' {a} ha g hg := by rw [smul_inv', ha g hg]

variable {A}

theorem mem_fixedModule {H : Subgroup G} {a : A} :
    a ∈ fixedModule A H ↔ ∀ g ∈ H, g • a = a :=
  Iff.rfl

theorem fixedModule_anti {H H' : Subgroup G} (h : H ≤ H') : fixedModule A H' ≤ fixedModule A H :=
  fun _ ha g hg => ha g (h hg)

theorem smul_mem_fixedModule {H : Subgroup G} {a : A} (ha : a ∈ fixedModule A H) (g : G) :
    g • a ∈ fixedModule A (H.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨h, hh, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← mul_smul]
  rw [show g * h * g⁻¹ * g = g * h by group, mul_smul, ha h hh]

end FixedModule

section Discrete

class IsDiscreteModule (G : Type*) [Group G] [TopologicalSpace G] (A : Type*) [CommGroup A]
    [MulDistribMulAction G A] : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (MulAction.stabilizer G a : Set G)

variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

theorem isDiscreteModule_iff [ContinuousMul G] :
    IsDiscreteModule G A ↔ ∀ a : A, ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) := by
  constructor
  · intro h a
    exact ⟨⟨MulAction.stabilizer G a, h.isOpen_stabilizer a⟩, fun g hg => hg⟩
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨U, hU⟩ := h a
    exact Subgroup.isOpen_mono (H₁ := (U : Subgroup G)) (fun g hg => hU g hg) U.isOpen

end Discrete

section Norm

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)

def cosetSMul (a : fixedModule A L) : K ⧸ L.subgroupOf K → A :=
  Quotient.lift (fun σ : K => (σ : G) • (a : A)) fun σ τ hστ => by
    have h : σ⁻¹ * τ ∈ L.subgroupOf K := QuotientGroup.leftRel_apply.mp hστ
    rw [Subgroup.mem_subgroupOf] at h
    have ha := a.2 _ h
    calc (σ : G) • (a : A) = (σ : G) • ((((σ⁻¹ * τ : K)) : G) • (a : A)) := by rw [ha]
      _ = (τ : G) • (a : A) := by rw [smul_smul]; simp

variable {A K L}

@[simp] theorem cosetSMul_mk (a : fixedModule A L) (σ : K) :
    cosetSMul A K L a (σ : K ⧸ L.subgroupOf K) = (σ : G) • (a : A) :=
  rfl

theorem cosetSMul_one (q : K ⧸ L.subgroupOf K) : cosetSMul A K L 1 q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp

theorem cosetSMul_mul (a b : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    cosetSMul A K L (a * b) q = cosetSMul A K L a q * cosetSMul A K L b q := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp [smul_mul']

theorem smul_cosetSMul (a : fixedModule A L) (g : K) (q : K ⧸ L.subgroupOf K) :
    (g : G) • cosetSMul A K L a q = cosetSMul A K L a (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, smul_smul]
    rfl

theorem smul_mem_fixedModule_of_normal (hLK : L ≤ K) [hN : (L.subgroupOf K).Normal] {g : G}
    (hg : g ∈ K) {a : A} (ha : a ∈ fixedModule A L) : g • a ∈ fixedModule A L := by
  intro h hh
  have hc : g⁻¹ * h * g ∈ L := by
    have := hN.conj_mem ⟨h, hLK hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh) ⟨g, hg⟩⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  calc h • g • a = g • (g⁻¹ * h * g) • a := by simp [smul_smul, mul_assoc]
    _ = g • a := by rw [ha _ hc]

variable (A K L)

noncomputable def normFun (a : fixedModule A L) : A :=
  ∏ᶠ q, cosetSMul A K L a q

variable [(L.subgroupOf K).FiniteIndex]

theorem normFun_mem_fixedModule (a : fixedModule A L) : normFun A K L a ∈ fixedModule A K := by
  intro g hg
  unfold normFun
  rw [smul_finprod']
  simp_rw [smul_cosetSMul a ⟨g, hg⟩]
  exact finprod_comp_equiv (MulAction.toPerm (⟨g, hg⟩ : K))

noncomputable def norm : fixedModule A L →* fixedModule A K where
  toFun a := ⟨normFun A K L a, normFun_mem_fixedModule A K L a⟩
  map_one' := by
    ext
    simp [normFun, cosetSMul_one]
  map_mul' a b := by
    classical
    let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
    ext
    simp only [normFun, Subgroup.coe_mul, finprod_eq_prod_of_fintype, cosetSMul_mul,
      Finset.prod_mul_distrib]

variable {A K L}

theorem coe_norm (a : fixedModule A L) :
    (norm A K L a : A) = ∏ᶠ q, cosetSMul A K L a q :=
  rfl

theorem norm_smul [(L.subgroupOf K).Normal] (g : K) (a : fixedModule A L)
    (hga : (g : G) • (a : A) ∈ fixedModule A L) :
    norm A K L ⟨(g : G) • (a : A), hga⟩ = norm A K L a := by
  ext
  rw [coe_norm, coe_norm]
  have h : ∀ q : K ⧸ L.subgroupOf K,
      cosetSMul A K L ⟨(g : G) • (a : A), hga⟩ q = cosetSMul A K L a (q * (g : K ⧸ L.subgroupOf K)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [← QuotientGroup.mk_mul, cosetSMul_mk, cosetSMul_mk]
      simp [smul_smul]
  simp_rw [h]
  exact finprod_comp_equiv (Equiv.mulRight _)

variable (A K L)

def augmentation : Subgroup A :=
  Subgroup.closure {x | ∃ g ∈ K, ∃ a ∈ fixedModule A L, x = g • a / a}

abbrev tateZero : Type _ :=
  fixedModule A K ⧸ (norm A K L).range

abbrev tateNegOne : Type _ :=
  (norm A K L).ker ⧸
    (augmentation A K L).comap ((fixedModule A L).subtype.comp (norm A K L).ker.subtype)

variable {A K L}

end Norm

section Data

open scoped GroundTheory.LocalField.Abstract

instance finiteIndex_openSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

variable {G : Type*} [Group G]

noncomputable def inertiaDegree (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  (K.map d).index

noncomputable def ramificationIndex (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  K.relIndex d.ker

variable (G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (A : Type*) [CommGroup A] [MulDistribMulAction G A]

structure ClassFieldData where

  deg : G →* Multiplicative ℤ̂
  continuous_deg : Continuous deg
  surjective_deg : Function.Surjective deg

  val : fixedModule A (⊤ : Subgroup G) →* Multiplicative ℤ̂

  intCast_mem_range_val : ∀ n : ℤ, Multiplicative.ofAdd (n : ℤ̂) ∈ val.range

  exists_eq_intCast_add_nsmul : ∀ n : ℕ, 0 < n → ∀ a : fixedModule A (⊤ : Subgroup G),
    ∃ (m : ℤ) (b : fixedModule A (⊤ : Subgroup G)),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b)

  range_val_comp_norm : ∀ K : OpenSubgroup G,
    (val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range =
      val.range.map (powMonoidHom (inertiaDegree deg (K : Subgroup G)))

def ClassFieldAxiom : Prop :=
  ∀ K L : OpenSubgroup G, L ≤ K → ∀ [((L : Subgroup G).subgroupOf K).Normal],
    IsCyclic (K ⧸ (L : Subgroup G).subgroupOf K) →
      Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) = (L : Subgroup G).relIndex K ∧
        Nat.card (tateNegOne A (K : Subgroup G) (L : Subgroup G)) = 1

structure ClassFieldTheory extends ClassFieldData G A where
  isDiscreteModule : IsDiscreteModule G A
  classFieldAxiom : ClassFieldAxiom G A

end Data

end GroundTheory.LocalField.Abstract
end
