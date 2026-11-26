module

public import GroundTheory.LocalFields.AbstractLocalReciprocity.IsoCyclic
public import GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality

@[expose] public section

section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.FunctorialityTransfer
section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.FunctorialityNorm
namespace GroundTheory.LocalField.Abstract

section DoubleCoset

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def doubleCosetMap {K K' S M : Subgroup G} (hK'K : K' ≤ K) {τ : G} (hτ : τ ∈ K)
    (hM : ∀ k ∈ K', k ∈ M → τ * k * τ⁻¹ ∈ S) : K' ⧸ M.subgroupOf K' → K ⧸ S.subgroupOf K :=
  Quotient.map' (fun k : K' => (⟨k * τ⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem hτ)⟩ : K)) fun k k' h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
    have := hM _ (K'.mul_mem (K'.inv_mem k.2) k'.2) (by simpa using h)
    simpa [mul_assoc] using this

theorem coe_norm_eq_prod_norm_inf {K K' S : Subgroup G} (hK'K : K' ≤ K)
    [(S.subgroupOf K).FiniteIndex] {ι : Type*} [Fintype ι] (τ : ι → G) (hτ : ∀ i, τ i ∈ K)
    (M : ι → Subgroup G) [∀ i, ((M i).subgroupOf K').FiniteIndex]
    (hM : ∀ i, ∀ k ∈ K', k ∈ M i ↔ τ i * k * (τ i)⁻¹ ∈ S)
    (hcover : ∀ c ∈ K, ∃ i, ∃ k ∈ K', τ i * k⁻¹ * c ∈ S)
    (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ S → i = j)
    (a : fixedModule A S) (ha : ∀ i, (τ i)⁻¹ • (a : A) ∈ fixedModule A (M i)) :
    (norm A K S a : A) = ∏ i, (norm A K' (M i) ⟨(τ i)⁻¹ • (a : A), ha i⟩ : A) := by
  classical
  let f : ∀ i, K' ⧸ (M i).subgroupOf K' → K ⧸ S.subgroupOf K := fun i =>
    doubleCosetMap hK'K (hτ i) (fun k hk hkM => (hM i k hk).1 hkM)
  let F : (Σ i, K' ⧸ (M i).subgroupOf K') → K ⧸ S.subgroupOf K := fun p => f p.1 p.2
  have hFmk : ∀ i (k : K'), F ⟨i, (k : K' ⧸ (M i).subgroupOf K')⟩ =
      ((⟨k * (τ i)⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem (hτ i))⟩ : K) : K ⧸ S.subgroupOf K) :=
    fun _ _ => rfl
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H k =>
      induction y using QuotientGroup.induction_on with
      | H k' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        have hxy' : τ i * (k : G)⁻¹ * k' * (τ j)⁻¹ ∈ S := by simpa [mul_assoc] using hxy
        obtain rfl := hdisj i j k k.2 k' k'.2 hxy'
        have hkk : (k : G)⁻¹ * k' ∈ M i :=
          (hM i _ (K'.mul_mem (K'.inv_mem k.2) k'.2)).2 (by simpa [mul_assoc] using hxy')
        have : ((k : K' ⧸ (M i).subgroupOf K')) = (k' : K' ⧸ (M i).subgroupOf K') := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hkk
        rw [this]
    · intro y
      induction y using QuotientGroup.induction_on with
      | H c =>
        obtain ⟨i, k, hk, hc⟩ := hcover c c.2
        refine ⟨⟨i, ((⟨k, hk⟩ : K') : K' ⧸ (M i).subgroupOf K')⟩, ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using hc
  have : ∀ i, Fintype (K' ⧸ (M i).subgroupOf K') := fun i => Fintype.ofFinite _
  let _ := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF), finprod_eq_prod_of_fintype,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk]
    exact mul_smul _ _ _

theorem conj_mem_of_normal {K L : Subgroup G} [hN : (L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) (hkL : k ∈ L) : τ * k * τ⁻¹ ∈ L := by
  have := hN.conj_mem ⟨k, hk⟩ (Subgroup.mem_subgroupOf.2 hkL) ⟨τ, hτ⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem conj_mem_iff_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) : τ * k * τ⁻¹ ∈ L ↔ k ∈ L := by
  refine ⟨fun h => ?_, conj_mem_of_normal hτ hk⟩
  have := conj_mem_of_normal (K.inv_mem hτ) (K.mul_mem (K.mul_mem hτ hk) (K.inv_mem hτ)) h
  simpa [mul_assoc] using this

end DoubleCoset

section Inclusion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem norm_mem_range_norm_of_le {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (b : fixedModule A (L : Subgroup G)) :
    (⟨norm A (K : Subgroup G) (L : Subgroup G) b,
        fixedModule_anti hK'K (norm A (K : Subgroup G) (L : Subgroup G) b).2⟩ :
        fixedModule A (K' : Subgroup G)) ∈ (norm A (K' : Subgroup G) (L : Subgroup G)).range := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  let _ := Fintype.ofFinite ((K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K)
  let τ : (K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K → G := fun i => ((Quotient.out i : K) : G)
  have hτ : ∀ i, τ i ∈ (K : Subgroup G) := fun i => (Quotient.out i : K).2
  have ha : ∀ i, (τ i)⁻¹ • (b : A) ∈ fixedModule A (L : Subgroup G) := fun i =>
    smul_mem_fixedModule_of_normal hLK ((K : Subgroup G).inv_mem (hτ i)) b.2
  have key := coe_norm_eq_prod_norm_inf (A := A) (S := (L : Subgroup G)) hK'K τ hτ
    (fun _ => (L : Subgroup G)) (fun i k hk => (conj_mem_iff_of_normal (hτ i) (hK'K hk)).symm)
    (fun c hc => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((K' : Subgroup G).subgroupOf K)
        (⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G))
      refine ⟨((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _), (h : G),
        Subgroup.mem_subgroupOf.1 h.2, ?_⟩
      have : τ ((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _) = c⁻¹ * (h : G) := by
        simp only [τ, hh, Subgroup.coe_mul]
      rw [this]
      simp)
    (fun i j k hk k' hk' hy => by
      rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hyK : τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ (K : Subgroup G) := hLK hy
      have hc := conj_mem_of_normal ((K : Subgroup G).inv_mem (hτ j)) ((K : Subgroup G).inv_mem hyK)
        ((L : Subgroup G).inv_mem hy)
      have hmem : k⁻¹ * k' * ((τ j)⁻¹ * (τ i * k⁻¹ * k' * (τ j)⁻¹)⁻¹ * (τ j)⁻¹⁻¹) ∈
          (K' : Subgroup G) :=
        (K' : Subgroup G).mul_mem ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk) hk')
          (hLK' hc)
      convert hmem using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, τ]
      group)
    b ha
  refine ⟨∏ i, ⟨(τ i)⁻¹ • (b : A), ha i⟩, Subtype.ext ?_⟩
  rw [map_prod]
  simp only [SubmonoidClass.coe_finsetProd]
  exact key.symm

noncomputable def tateZeroIncl {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] :
    tateZero A (K : Subgroup G) (L : Subgroup G) →* tateZero A (K' : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (fixedModule_anti (A := A) hK'K)) (by
    rintro _ ⟨b, rfl⟩
    exact norm_mem_range_norm_of_le hLK' hK'K b)

theorem tateZeroIncl_mk {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    tateZeroIncl hLK' hK'K (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk ⟨(a : A), fixedModule_anti hK'K a.2⟩ : tateZero A (K' : Subgroup G) (L : Subgroup G)) :=
  rfl

end Inclusion

end GroundTheory.LocalField.Abstract
end

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger MulAction

section Transfer

theorem map_transfer {Γ : Type*} [Group Γ] {H : Subgroup Γ} [H.FiniteIndex] {B C : Type*} [CommGroup B]
    [CommGroup C] (φ : H →* B) (f : B →* C) (g : Γ) : f (φ.transfer g) = (f.comp φ).transfer g := by
  classical
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers g) (Γ ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rfl

end Transfer

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem exists_eq_zpow_mul_of_mem_frobeniusClosure (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ frobeniusClosure d L σ) : ∃ m : ℤ, ∃ l ∈ L, y = σ ^ m * l := by
  have hy' : y ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hy
  have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (L : Set G)) :=
    hL.preimage (continuous_const.mul continuous_id)
  have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' (L : Set G) := by
    show y⁻¹ * y ∈ L
    rw [inv_mul_cancel]
    exact L.one_mem
  obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
  obtain ⟨m, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhS
  refine ⟨m, j * (y⁻¹ * (σ ^ m * j))⁻¹, L.mul_mem hj.1 (L.inv_mem hhO), by group⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_pow_eq_inf (hd : Continuous d) (hL : IsOpen (L : Set G)) {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) (hLK' : L ≤ K') {ρ : G}
    (hρ : ρ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdρ : d ρ = Multiplicative.ofAdd (N : ℤ̂)) {f : ℕ} (hf : 0 < f) (hρf : ρ ^ f ∈ K')
    (hdiv : ∀ k : ℤ, ρ ^ k ∈ K' → (f : ℤ) ∣ k) :
    frobeniusClosure d L (ρ ^ f) = K' ⊓ frobeniusClosure d L ρ := by
  have hρf' : ρ ^ f ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G) := Subgroup.pow_mem _ hρ f
  have hdρf : d (ρ ^ f) = Multiplicative.ofAdd ((f * N : ℕ) : ℤ̂) := by
    rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul]
  have hle : frobeniusClosure d L (ρ ^ f) ≤ frobeniusClosure d L ρ :=
    frobeniusClosure_le isClosed_frobeniusClosure (Subgroup.pow_mem _ mem_frobeniusClosure_self f)
      le_frobeniusClosure
  apply le_antisymm
  · refine frobeniusClosure_le ((OpenSubgroup.isClosed ⟨K', hK'⟩).inter isClosed_frobeniusClosure)
      ⟨hρf, Subgroup.pow_mem _ mem_frobeniusClosure_self f⟩ ?_
    exact le_inf (inf_le_left.trans hLK') le_frobeniusClosure
  · intro y hy
    obtain ⟨hyK', hyS⟩ := Subgroup.mem_inf.1 hy
    set M : ℕ+ := ⟨f * N, Nat.mul_pos hf (Nat.pos_of_ne_zero hN)⟩ with hMdef
    set V : Set G := (L : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
    have hV : IsOpen V := hL.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
    have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
    have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' V := by
      simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
      exact ⟨L.one_mem, (multiples M).zero_mem⟩
    have hy' : y ∈ closure ((Subgroup.zpowers ρ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hyS
    obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
    have hhS' : h ∈ frobeniusClosure d L ρ := Subgroup.le_topologicalClosure _ hhS
    obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hρ).1 hhS
    obtain ⟨huL, huM⟩ := hhO
    set u := y⁻¹ * (ρ ^ k * j) with hudef

    have hρk : ρ ^ k ∈ K' := by
      have : ρ ^ k = y * u * j⁻¹ := by rw [hudef]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem hyK' (hLK' huL)) (K'.inv_mem (hLK' hj.1))
    obtain ⟨k', rfl⟩ := hdiv k hρk
    have hhf : ρ ^ ((f : ℤ) * k') * j ∈ frobeniusClosure d L (ρ ^ f) := by
      refine Subgroup.mul_mem _ ?_ (le_frobeniusClosure hj)
      rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ mem_frobeniusClosure_self k'

    have huS : u ∈ frobeniusClosure d L ρ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hhS'
    have hmap := map_frobeniusClosure hd hρf' hdρf
    have hdu : d u ∈ (frobeniusClosure d L (ρ ^ f)).map d := by
      rw [hmap]
      exact huM
    obtain ⟨z, hz, hzu⟩ := hdu
    have hzu' : z⁻¹ * u ∈ frobeniusClosure d L ρ ⊓ d.ker := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle hz)) huS, ?_⟩
      exact (MonoidHom.mem_ker).2 (by rw [map_mul, map_inv, hzu, inv_mul_cancel])
    rw [frobeniusClosure_inf_ker hd hL hρ hN hdρ] at hzu'
    have hu : u ∈ frobeniusClosure d L (ρ ^ f) := by
      have : u = z * (z⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ hz (le_frobeniusClosure hzu')
    have : y = ρ ^ ((f : ℤ) * k') * j * u⁻¹ := by rw [hudef]; group
    rw [this]
    exact Subgroup.mul_mem _ hhf (Subgroup.inv_mem _ hu)

end FixedField

section Ver

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]


omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem map_conj_eq_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] (hLK : L ≤ K) {τ : G}
    (hτ : τ ∈ K) : L.map (MulAut.conj τ).toMonoidHom = L := by
  ext y
  rw [mem_map_conj]
  constructor
  · intro h
    have := conj_mem_of_normal hτ (hLK h) h
    simpa [mul_assoc] using this
  · intro h
    have := conj_mem_of_normal (K.inv_mem hτ) (hLK h) h
    simpa using this

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]


omit [IsTopologicalGroup G] [CompactSpace G] in
theorem galRestrict_injective (hK'K : K' ≤ K) :
    Function.Injective (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq


omit [IsTopologicalGroup G] [CompactSpace G] in
theorem mk_mem_range_galRestrict_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (k : (K : Subgroup G)) :
    (k : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range ↔
      (k : G) ∈ (K' : Subgroup G) := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [galRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have h := (K' : Subgroup G).mul_mem k'.2 (hLK' hq)
      simpa using h
  · intro hk
    exact ⟨((⟨k, hk⟩ : (K' : Subgroup G)) : _ ⧸ _), rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (a b : (K : Subgroup G)) :
    ((a : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
        _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((b : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (a : G)⁻¹ * b ∈ (K' : Subgroup G) := by
  rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    mk_mem_range_galRestrict_iff hLK' hK'K]
  simp

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem zpow_smul_mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    mk_mk_eq_iff hLK' hK'K]
  have e : (((σ ^ k * x : (K : Subgroup G)) : G))⁻¹ * x = ((x : G)⁻¹ * (σ : G) ^ k * x)⁻¹ := by
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
    group
  rw [e, Subgroup.inv_mem_iff]

noncomputable def verlagerung (hK'K : K' ≤ K) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      Group.Abelianization ((K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') :=
  (Group.Abelianization.of.comp
    (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom).transfer

end Ver

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}


omit [TotallyDisconnectedSpace G] in
theorem exists_frobeniusLift_of_deg {K : OpenSubgroup G} {x : G} (hx : x ∈ (K : Subgroup G)) {N : ℕ}
    (hN : 0 < N) (hd : D.deg x = Multiplicative.ofAdd (N : ℤ̂)) :
    ∃ s : D.FrobeniusLift K, s.elt = x := by
  have hm := toAdd_deg_mem_multiples (D := D) K hx
  rw [hd, toAdd_ofAdd, ← Int.cast_natCast,
    intCast_mem_multiples_iff (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))] at hm
  obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  exact ⟨⟨x, hx, m, hm0, by rw [hd, Nat.mul_comm]⟩, rfl⟩

section Ver

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

theorem reciprocity_mk_conj_pow (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (s : D.FrobeniusLift K) (x : (K : Subgroup G)) {f : ℕ}
    (hf0 : 0 < f) (hf : ∀ k : ℤ, (x : G)⁻¹ * s.elt ^ k * x ∈ (K' : Subgroup G) ↔ (f : ℤ) ∣ k)
    (hmem : (x : G)⁻¹ * s.elt ^ f * x ∈ (K' : Subgroup G))
    {π : fixedModule A ((s.field L (hLK'.trans hK'K) : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L (hLK'.trans hK'K)) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK' hax ((⟨_, hmem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L (hLK'.trans hK'K)) : OpenSubgroup G) : Subgroup G)
        ⟨(x : G)⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : G, ρ = (x : G)⁻¹ * s.elt * x := ⟨_, rfl⟩
  have hρK : ρ ∈ (K : Subgroup G) := by
    rw [hρdef]
    exact (K : Subgroup G).mul_mem ((K : Subgroup G).mul_mem ((K : Subgroup G).inv_mem x.2) s.mem) x.2
  have hρn := FrobeniusLift.mem_normalizer (D := D) hLK hρK
  have hdρ : D.deg ρ = Multiplicative.ofAdd ((s.deg * inertiaDegree D.deg K : ℕ) : ℤ̂) := by
    rw [hρdef, map_mul, map_mul, map_inv, mul_comm _ (D.deg s.elt), mul_assoc, inv_mul_cancel,
      mul_one, s.deg_eq]
  have hN : s.deg * inertiaDegree D.deg K ≠ 0 := s.degree_ne_zero
  have hρz : ∀ k : ℤ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_zpow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hρn' : ∀ k : ℕ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_pow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hmemρ : ρ ^ f ∈ (K' : Subgroup G) := by
    rw [hρn']
    exact hmem
  have hdivρ : ∀ k : ℤ, ρ ^ k ∈ (K' : Subgroup G) → (f : ℤ) ∣ k := fun k hk =>
    (hf k).1 (by rwa [hρz] at hk)
  obtain ⟨t, ht⟩ := exists_frobeniusLift_of_deg (D := D) (K := K') hmemρ
    (N := f * (s.deg * inertiaDegree D.deg K)) (Nat.mul_pos hf0 (Nat.pos_of_ne_zero hN))
    (by rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul]; norm_cast)
  have hconjS : ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) =
      frobeniusClosure D.deg L ρ := by
    rw [coe_conjOpen, s.coe_field hLK, map_conj_frobeniusClosure,
      map_conj_eq_of_normal hLK ((K : Subgroup G).inv_mem x.2), inv_inv, hρdef]
  have hkey := frobeniusClosure_pow_eq_inf D.continuous_deg L.isOpen K'.isOpen hLK' hρn hN hdρ hf0
    hmemρ hdivρ
  have htfield : ((t.field L hLK' : OpenSubgroup G) : Subgroup G) =
      ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) := by
    rw [t.coe_field hLK', ht, hkey, ← hconjS]
    rfl
  have hle : t.field L hLK' ≤ conjOpen (x : G)⁻¹ (s.field L hLK) := by
    intro y hy
    have : y ∈ ((t.field L hLK' : OpenSubgroup G) : Subgroup G) := hy
    rw [htfield] at this
    exact (Subgroup.mem_inf.1 this).2
  have ha : (x : G)⁻¹ • (π : A) ∈
      fixedModule A ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) :=
    smul_mem_fixedModule π.2 _
  have hv1 : D.valuation (conjOpen (x : G)⁻¹ (s.field L hLK)) ⟨_, ha⟩ = Multiplicative.ofAdd 1 := by
    rw [valuation_conj (x : G)⁻¹ rfl π ⟨_, ha⟩ rfl, hπ]
  have hram : relRamificationIndex D.deg (conjOpen (x : G)⁻¹ (s.field L hLK)) (t.field L hLK') = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    obtain ⟨hyk, hyS⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ frobeniusClosure D.deg L ρ ⊓ D.deg.ker := by
      refine ⟨?_, hyk⟩
      rw [← hconjS]
      exact hyS
    rw [frobeniusClosure_inf_ker D.continuous_deg L.isOpen hρn hN hdρ] at hy'
    show y ∈ frobeniusClosure D.deg L t.elt
    rw [ht]
    exact le_frobeniusClosure hy'
  have hπ' : D.valuation (t.field L hLK') ⟨(x : G)⁻¹ • (π : A), fixedModule_anti hle ha⟩ =
      Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hle ha, hv1, hram, pow_one]
  have he : ((⟨_, hmem⟩ : (K' : Subgroup G)) : (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K' : Subgroup G)) : _ ⧸ _) := by
    congr 1
    apply Subtype.ext
    show _ = t.elt
    rw [ht, hρn']
  rw [he, D.reciprocity_mk_eq_norm hLK' hax t hπ']
  congr 1
  apply Subtype.ext
  exact coe_norm_congr rfl htfield _

theorem reciprocity_verlagerung (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (hLK' : L ≤ K')
    (hK'K : K' ≤ K) (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Group.Abelianization.lift (D.reciprocity hLK' hax) (verlagerung hK'K g) =
      tateZeroIncl hLK' hK'K (D.reciprocity (hLK'.trans hK'K) hax g) := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK g
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  rw [D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroIncl_mk, verlagerung, map_transfer]
  set H := (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range with hH
  set γ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
    ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) with hγ
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers γ)
    (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  let τ : Quotient (orbitRel (Subgroup.zpowers γ)
      (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) → (K : Subgroup G) :=
    fun q => q.out.out.out
  have hqτ : ∀ q, q.out = (((τ q : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
      _ ⧸ H) := fun q => by
    simp only [τ, QuotientGroup.out_eq']
  have hper : ∀ q (k : ℤ), ((τ q : G))⁻¹ * s.elt ^ k * τ q ∈ (K' : Subgroup G) ↔
      (Function.minimalPeriod (γ • ·) q.out : ℤ) ∣ k := fun q k => by
    rw [← zpow_smul_eq_iff_minimalPeriod_dvd, hqτ q, hγ, zpow_smul_mk_mk_eq_iff hLK' hK'K]
  have hpos : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), 0 < Function.minimalPeriod (γ • ·) q.out := fun q =>
    Nat.pos_of_dvd_of_pos (pow_smul_eq_iff_minimalPeriod_dvd.1 (by rw [pow_orderOf_eq_one, one_smul]))
      (orderOf_pos γ)
  have hmemf : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((τ q : G))⁻¹ * s.elt ^ Function.minimalPeriod (γ • ·) q.out * τ q ∈
      (K' : Subgroup G) := fun q => by
    have := (hper q (Function.minimalPeriod (γ • ·) q.out)).2 dvd_rfl
    rwa [zpow_natCast] at this
  have hfac : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((Group.Abelianization.lift (D.reciprocity hLK' hax)).comp
      (Group.Abelianization.of.comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom))
        ⟨(q.out.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H γ q.out⟩ =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G)
        ⟨((τ q : G))⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
    intro q
    refine Eq.trans ?_ (reciprocity_mk_conj_pow hax hLK' hK'K s (τ q) (hpos q) (hper q) (hmemf q) hπ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Group.Abelianization.lift_apply_of]
    congr 1
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, galRestrict_mk]
    show (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out = _
    have hL : (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out =
        ((((τ q)⁻¹ * ⟨s.elt, s.mem⟩ ^ Function.minimalPeriod (γ • ·) q.out * τ q : (K : Subgroup G))) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      simp only [τ, QuotientGroup.out_eq']
      rfl
    rw [hL]
    congr 1
  rw [Finset.prod_congr rfl fun q _ => hfac q, ← QuotientGroup.mk_prod]
  congr 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  refine (coe_norm_eq_prod_norm_inf hK'K (fun q => (τ q : G)) (fun q => (τ q).2)
    (fun q => ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G))
    ?_ ?_ ?_ π (fun q => fixedModule_anti (inf_le_right (a := K'))
      (smul_mem_fixedModule π.2 _))).symm
  · intro q k hk
    show k ∈ (K' : Subgroup G) ⊓ ((conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) :
      Subgroup G) ↔ _
    rw [Subgroup.mem_inf, mem_conjOpen, inv_inv]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  · intro c hc
    let p : ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H :=
      (((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ H)
    let q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) := Quotient.mk'' p
    obtain ⟨⟨z, hz⟩, hzp⟩ := orbitRel_apply.1 (Quotient.mk_out' p : orbitRel _ _ q.out p)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hzp' : γ ^ m • p = q.out := hzp
    rw [hqτ q, hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K] at hzp'
    refine ⟨q, _, hzp', ?_⟩
    have e : (τ q : G) * ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m *
        ⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : G)⁻¹ * τ q)⁻¹ * c = s.elt ^ m := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (s.elt_mem_field hLK) m
  · intro q q' k hk k' hk' hy
    obtain ⟨m, l, hl, hyeq⟩ := exists_eq_zpow_mul_of_mem_frobeniusClosure L.isOpen
      (FrobeniusLift.mem_normalizer (D := D) hLK s.mem) hy
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    refine (orbitRel_apply (G := Subgroup.zpowers γ)).2 ⟨⟨γ ^ m, Subgroup.zpow_mem_zpowers γ m⟩, ?_⟩
    show γ ^ m • q'.out = q.out
    rw [hqτ q, hqτ q', hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K]
    have hl1 : s.elt ^ m * l * (s.elt ^ m)⁻¹ ∈ (L : Subgroup G) :=
      conj_mem_of_normal ((K : Subgroup G).zpow_mem s.mem m) (hLK hl) hl
    have hl2 := conj_mem_of_normal ((K : Subgroup G).inv_mem (τ q).2) (hLK hl1) hl1
    have hτ' : (τ q' : G) = (s.elt ^ m * l)⁻¹ * ((τ q : G) * k⁻¹ * k') := by
      rw [← hyeq]
      group
    have e : ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m * τ q' : (K : Subgroup G)) : G))⁻¹ * τ q =
        k'⁻¹ * k * (((τ q : G))⁻¹ * (s.elt ^ m * l * (s.elt ^ m)⁻¹) * ((τ q : G))⁻¹⁻¹) := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      rw [hτ']
      group
    rw [e]
    exact (K' : Subgroup G).mul_mem
      ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk') hk) (hLK' hl2)

end Ver

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Normal

variable {G : Type*} [Group G]

theorem normal_subgroupOf_of_le {K L M : Subgroup G} (hMK : M ≤ K) [hN : (L.subgroupOf K).Normal] :
    (L.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩

theorem card_quotient_eq_relIndex (K L : Subgroup G) :
    Nat.card (K ⧸ L.subgroupOf K) = L.relIndex K :=
  (Subgroup.index_eq_card _).symm

end Normal

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

def fixedOpen (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G where
  toSubgroup := (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G)) (fun x hx => ⟨⟨x, hLK hx⟩, by
      show ((⟨x, hLK hx⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H
      rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact H.one_mem, rfl⟩) L.isOpen

theorem mem_fixedOpen {H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)} {g : G} :
    g ∈ ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ↔
      ∃ h : g ∈ (K : Subgroup G), ((⟨g, h⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H := by
  show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hH⟩
    exact ⟨⟨g, h⟩, hH, rfl⟩

variable (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))

theorem le_fixedOpen : L ≤ fixedOpen hLK H := fun x hx =>
  (mem_fixedOpen hLK).2 ⟨hLK hx, by
    rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact H.one_mem⟩

theorem fixedOpen_le : fixedOpen hLK H ≤ K := fun _ hx => ((mem_fixedOpen hLK).1 hx).1

instance normal_fixedOpen_self :
    ((L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)).Normal :=
  normal_subgroupOf_of_le (K := (K : Subgroup G)) (fun _ hx => ((mem_fixedOpen hLK).1 hx).1)

instance normal_fixedOpen [hH : H.Normal] :
    (((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, hnH⟩ := (mem_fixedOpen hLK).1 hn
    refine (mem_fixedOpen hLK).2 ⟨(g * n * g⁻¹).2, ?_⟩
    exact hH.conj_mem _ hnH (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)⟩

theorem range_galRestrict_fixedOpen [CompactSpace G] :
    (galRestrict (K := K) (L := L) (K' := fixedOpen hLK H) (L' := L) (fixedOpen_le hLK H)
      le_rfl).range = H := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩

noncomputable def galFixedEquiv [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ⧸
      (L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ≃* H :=
  (MonoidHom.ofInjective (galRestrict_injective (K := K) (L := L) (fixedOpen_le hLK H))).trans
    (MulEquiv.subgroupCongr (range_galRestrict_fixedOpen hLK H))

theorem relIndex_fixedOpen [CompactSpace G] :
    (L : Subgroup G).relIndex (fixedOpen hLK H) = Nat.card H := by
  rw [← card_quotient_eq_relIndex]
  exact Nat.card_congr (galFixedEquiv hLK H).toEquiv

theorem relIndex_fixedOpen_eq_index [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).relIndex K = H.index := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := (L : Subgroup G))
    (K := ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)) (L := (K : Subgroup G))
    (fun x hx => le_fixedOpen hLK H hx) (fun x hx => fixedOpen_le hLK H hx)
  rw [relIndex_fixedOpen, ← card_quotient_eq_relIndex (K : Subgroup G) (L : Subgroup G),
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end FixedField

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]


omit [IsTopologicalGroup G] [CompactSpace G] in
theorem galRestrict_surjective {K L M : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((M : Subgroup G).subgroupOf K).Normal] (hLM : L ≤ M) :
    Function.Surjective (galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨(τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K), rfl⟩


omit [CompactSpace G] in
theorem conjOpen_eq_of_normal {K M : OpenSubgroup G} (hMK : M ≤ K)
    [((M : Subgroup G).subgroupOf K).Normal] {g : G} (hg : g ∈ (K : Subgroup G)) :
    conjOpen g M = M := by
  have h := map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg
  apply OpenSubgroup.ext
  intro x
  show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)
  rw [coe_conjOpen, h]

theorem Abelianization.lift_injective_of_ker_le {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H q =>
    have hq : Abelianization.lift f (Abelianization.of q) = 1 := hz
    change f q = 1 at hq
    have := h hq
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at this
    exact this

end Restrict

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_congr {K₁ K₂ L₁ L₂ : OpenSubgroup G} (hK : K₁ = K₂) (hL : L₁ = L₂)
    (h1 : L₁ ≤ K₁) (h2 : L₂ ≤ K₂) [((L₁ : Subgroup G).subgroupOf K₁).Normal]
    [((L₂ : Subgroup G).subgroupOf K₂).Normal] {τ : G} (hτ1 : τ ∈ (K₁ : Subgroup G))
    (hτ2 : τ ∈ (K₂ : Subgroup G)) {a : A} (ha1 : a ∈ fixedModule A (K₁ : Subgroup G))
    (ha2 : a ∈ fixedModule A (K₂ : Subgroup G))
    (h : D.reciprocity h1 hax ((⟨τ, hτ1⟩ : (K₁ : Subgroup G)) :
        (K₁ : Subgroup G) ⧸ (L₁ : Subgroup G).subgroupOf K₁) =
      ((⟨a, ha1⟩ : fixedModule A (K₁ : Subgroup G)) : tateZero A (K₁ : Subgroup G) (L₁ : Subgroup G))) :
    D.reciprocity h2 hax ((⟨τ, hτ2⟩ : (K₂ : Subgroup G)) :
        (K₂ : Subgroup G) ⧸ (L₂ : Subgroup G).subgroupOf K₂) =
      ((⟨a, ha2⟩ : fixedModule A (K₂ : Subgroup G)) : tateZero A (K₂ : Subgroup G) (L₂ : Subgroup G)) := by
  subst hK hL
  exact h

section Tower

variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]

theorem reciprocity_surjective_of_tower (h1 : Function.Surjective (D.reciprocity hLM hax))
    (h2 : Function.Surjective (D.reciprocity hMK hax)) :
    Function.Surjective (D.reciprocity (hLM.trans hMK) hax) := by
  have hLK : L ≤ K := hLM.trans hMK
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨q', hq'⟩ := h2 (a : tateZero A (K : Subgroup G) (M : Subgroup G))
    obtain ⟨q, rfl⟩ := galRestrict_surjective (K := K) hLM q'
    have e1 := D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (D.reciprocity hLK hax q)
    rw [hq', ← hc, normTateZero_mk, norm_self, MonoidHom.id_apply, QuotientGroup.eq] at e1
    obtain ⟨b, hb⟩ := e1
    obtain ⟨p, hp⟩ := h1 ((b⁻¹ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    have e2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl p
    refine ⟨q * galRestrict hMK le_rfl p, ?_⟩
    rw [map_mul, e2, hp, ← hc, normTateZero_mk, map_inv, hb, ← QuotientGroup.mk_mul]
    congr 1
    group

theorem ker_reciprocity_le_of_tower
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
    (hs : Function.Surjective (D.reciprocity hLM hax))
    (hk : (D.reciprocity hLM hax).ker ≤ commutator ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)) :
    (D.reciprocity (hLM.trans hMK) hax).ker ≤
      commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  have hLK : L ≤ K := hLM.trans hMK
  have hMK' : (M : Subgroup G) ≤ K := fun _ hx => hMK hx
  have hLM' : (L : Subgroup G) ≤ M := fun _ hx => hLM hx
  have hLK' : (L : Subgroup G) ≤ K := fun _ hx => hLK hx
  set ι := galRestrict (K := K) (L := L) (K' := M) (L' := L) hMK le_rfl with hι
  set S := (commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).comap ι with hS

  have hconj : ∀ (g : G) (hg : g ∈ (K : Subgroup G)) (τ : G) (hτ : τ ∈ (M : Subgroup G)) (x : A)
      (hx : x ∈ fixedModule A (M : Subgroup G)),
      D.reciprocity hLM hax ((⟨τ, hτ⟩ : (M : Subgroup G)) :
          (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) →
      D.reciprocity hLM hax ((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' hτ) hτ⟩ :
          (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨g • x, smul_mem_fixedModule_of_normal hMK' hg hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) := by
    intro g hg τ hτ x hx h
    have e := D.reciprocity_galConj hax g hLM
      ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)
    rw [galConj_mk, h, tateZeroConj_mk] at e
    exact D.reciprocity_congr hax (conjOpen_eq_of_normal hMK hg) (conjOpen_eq_of_normal hLK hg)
      (conjOpen_mono g hLM) hLM _ _ (a := g • x) _ _ e
  intro q hq
  rw [MonoidHom.mem_ker] at hq

  have hq1 : galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM q = 1 := by
    apply (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcyc).1
    rw [map_one, D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q, hq, map_one]
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  set t : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M :=
    ((⟨k, hq1⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) with ht
  have hιt : ι t = QuotientGroup.mk k := rfl
  rw [← hιt] at hq ⊢

  have h2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl t
  rw [hq] at h2
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hLM hax t)
  rw [← ha, normTateZero_mk] at h2
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h2.symm
  set a' : fixedModule A (M : Subgroup G) := a * (norm A (M : Subgroup G) (L : Subgroup G) b)⁻¹
    with ha'def
  have ha' : norm A (K : Subgroup G) (M : Subgroup G) a' = 1 := by
    rw [ha'def, map_mul, map_inv, norm_norm hLM' hMK' b, hb, mul_inv_cancel]
  have hmk : (QuotientGroup.mk a' : tateZero A (M : Subgroup G) (L : Subgroup G)) =
      D.reciprocity hLM hax t := by
    rw [← ha, QuotientGroup.eq]
    exact ⟨b, by rw [ha'def]; group⟩

  have hsub : Subsingleton (tateNegOne A (K : Subgroup G) (M : Subgroup G)) :=
    (Nat.card_eq_one_iff_unique.1 (hax K M hMK hcyc).2).1
  have haug : (a' : A) ∈ augmentation A (K : Subgroup G) (M : Subgroup G) := by
    have h0 : ((⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker) :
        tateNegOne A (K : Subgroup G) (M : Subgroup G)) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff
      (⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker)).1 h0

  set P : Subgroup A := ((S.map (D.reciprocity hLM hax)).comap
    (QuotientGroup.mk' (norm A (M : Subgroup G) (L : Subgroup G)).range)).map
      (fixedModule A (M : Subgroup G)).subtype with hP
  have hAP : augmentation A (K : Subgroup G) (M : Subgroup G) ≤ P := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, x, hx, rfl⟩
    obtain ⟨ρ, hρ⟩ := hs ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective ρ
    have e := hconj g hg τ τ.2 x hx hρ
    refine ⟨⟨g • x / x, (fixedModule A (M : Subgroup G)).div_mem
      (smul_mem_fixedModule_of_normal hMK' hg hx) hx⟩, ?_, rfl⟩
    refine ⟨((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' τ.2) τ.2⟩ : (M : Subgroup G)) :
      (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) * (τ : (M : Subgroup G) ⧸ _)⁻¹, ?_, ?_⟩
    · show ι (_ * _) ∈ commutator _
      rw [map_mul, map_inv]
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((⟨g, hg⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
        (Subgroup.mem_top ((⟨τ, hMK' τ.2⟩ : (K : Subgroup G)) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
      rw [commutatorElement_def] at hc
      exact hc
    · rw [map_mul, map_inv, e, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext (div_eq_mul_inv _ _).symm
  obtain ⟨y, hy, hya⟩ := hAP haug
  obtain rfl : y = a' := Subtype.ext hya
  obtain ⟨s, hsS, hrs⟩ := hy
  rw [QuotientGroup.mk'_apply, hmk] at hrs
  have hts : t * s⁻¹ ∈ (D.reciprocity hLM hax).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]
  have hcomm : ι (t * s⁻¹) ∈ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    have h := hk hts
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at h ⊢
    rw [← Abelianization.map_of, h, map_one]
  have e3 : ι t = ι (t * s⁻¹) * ι s := by rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [e3]
  exact Subgroup.mul_mem _ hcomm hsS

end Tower

section PGroup

theorem reciprocity_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    ∀ {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal],
      (L : Subgroup G).relIndex K = n →
      IsPGroup p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →
      Function.Surjective (D.reciprocity hLK hax) ∧
        (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hLK _ hn hP
  by_cases hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  · have hb := reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc
    refine ⟨hb.2, fun q hq => ?_⟩
    rw [(injective_iff_map_eq_one _).1 hb.1 q hq]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hcyc (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.1 hk).1)

  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p
    (pow_dvd_pow p (Nat.sub_le k 1) |>.trans hk.symm.dvd)
  have hpk : p ^ (k - 1) * p = p ^ k := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
  have hHi : H.index = p := by
    have h := H.card_mul_index
    rw [hH, hk, ← hpk] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h
  have hmin : (p ^ k).minFac = p := by
    have h2 : (p ^ k).minFac.Prime := Nat.minFac_prime (Nat.one_lt_pow hk0 hp.out.one_lt).ne'
    exact (Nat.prime_dvd_prime_iff_eq h2 hp.out).1 (h2.dvd_of_dvd_pow (Nat.minFac_dvd _))
  have hHn : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hHi, hk, hmin])
  set M := fixedOpen hLK H with hM
  have hLM : L ≤ M := le_fixedOpen hLK H
  have hMK : M ≤ K := fixedOpen_le hLK H

  have hcycM : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K) :=
    isCyclic_of_prime_card (p := p) (by
      rw [card_quotient_eq_relIndex, hM, relIndex_fixedOpen_eq_index, hHi])

  have hPM : IsPGroup p ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) :=
    (hP.to_subgroup H).of_equiv (galFixedEquiv hLK H).symm
  have hLMn : (L : Subgroup G).relIndex M = p ^ (k - 1) := by
    rw [hM, relIndex_fixedOpen, hH]
  have hlt : p ^ (k - 1) < n := by
    rw [← hn, ← card_quotient_eq_relIndex, hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
  obtain ⟨hs, hker⟩ := ih _ hlt hLM hLMn hPM
  exact ⟨D.reciprocity_surjective_of_tower hax hLM hMK hs
      (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcycM).2,
    D.ker_reciprocity_le_of_tower hax hLM hMK hcycM hs hker⟩

end PGroup

end ClassFieldData

end GroundTheory.LocalField.Abstract
