module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsAlt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RebasingHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniPart
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SdBasisBot
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem sd_basis_bot {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun v => ?_, ?_⟩
  · rw [spanS_empty]
    constructor
    · rintro rfl
      exact M.zero_mem
    · intro hv
      have := hM.le v hv
      rwa [hW, Submodule.mem_bot] at this
  · rw [hW, Set.range_eq_empty, Submodule.span_empty]

theorem sup_cutW {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    K ∙ x ⊔ cutW h W x = W := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) inf_le_left
  · intro w hw
    have e : w = (h x w * (h x x)⁻¹) • x + (w - (h x w * (h x x)⁻¹) • x) := by abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ?_
    refine mem_cutW.mpr ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hxx, mul_one, sub_self]

theorem sd_basis (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  intro n
  induction n with
  | zero =>
    intro W M hn hM
    exact sd_basis_bot hM (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro W M hn hM
    by_cases hbot : W = ⊥
    · exact sd_basis_bot hM hbot
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    have hxW := hM.le x hx
    obtain ⟨k, f, hfo, hfu, hfM, hfW⟩ := ih _ _
      (by have := finrank_cutW_lt (h := h) hxW hu.1; omega) (hM.cut hx hu)
    have hfc : ∀ i, f i ∈ cutW h W x := fun i => by
      rw [← hfW]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfm : ∀ i, f i ∈ M := fun i =>
      (mem_cutM.mp ((hfM (f i)).mp (mem_spanS_self f i))).1
    refine ⟨k + 1, Fin.cons x f, ?_, ?_, fun v => ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_cutW.mp (hfc j)).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using symm_zero hs (mem_cutW.mp (hfc i)).2
        | succ j =>
          simpa using hfo i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hfu i
    · constructor
      · rintro ⟨c, hc, rfl⟩
        refine M.sum_mem fun i _ => hM.smul_mem _ (hc i) _ ?_
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using hfm i
      · intro hv
        obtain ⟨d, hd', hdv⟩ := (hfM _).mpr (proj_mem hM.toIsLatIn hx hu hv)
        refine ⟨Fin.cons (h x v * (h x x)⁻¹) d, fun i => ?_, ?_⟩
        · cases i using Fin.cases with
          | zero => simpa using S.mul_mem (hM.int _ hx _ hv) hu.2.2
          | succ i => simpa using hd' i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hdv]
          abel
    · rw [Fin.range_cons, Submodule.span_insert, hfW]
      exact sup_cutW hxW hu.1

end

end Formalism.L2.SG.Pf.G3
end
end

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

private theorem mem_iff_lemma {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

private theorem smul_mem_lemma_2 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {a : K} (ha : a ∈ S)
    {v : V} (hv : v ∈ spanS S g) : a • v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  exact ⟨fun i => a * d i, fun i => S.mul_mem ha (hd i), by simp [Finset.smul_sum, mul_smul]⟩

private theorem spanS_le_lemma_3 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  exact AddSubgroup.sum_mem _ fun k _ => smul_mem_lemma_2 (hc k) (hfg k)

private theorem mem_span_lemma_4 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {v : V}
    (hv : v ∈ spanS S g) : v ∈ Submodule.span K (Set.range g) := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem spans_eq_lemma_5 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (h1 : ∀ k, f k ∈ spanS S g) (h2 : ∀ i, g i ∈ spanS S f) :
    Submodule.span K (Set.range f) = Submodule.span K (Set.range g) ∧
      ∀ v, v ∈ spanS S f ↔ v ∈ spanS S g := by
  refine ⟨le_antisymm ?_ ?_, fun v => ⟨spanS_le_lemma_3 h1, spanS_le_lemma_3 h2⟩⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact mem_span_lemma_4 (h1 k)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_lemma_4 (h2 i)

private theorem linInd_lemma_6 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} {f : ι → V} (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0)
    (hn : ∀ i, h (f i) (f i) ≠ 0) : LinearIndependent K f := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 := congrArg (h (f i)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro h'
    exact absurd hi h'

private theorem form_sum_lemma_7 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (a c : ι → K) :
    h (∑ i, a i • b i) (∑ j, c j • b j) = ∑ i, star (a i) * c i * h (b i) (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  · intro j _ hji
    rw [map_smulₛₗ, LinearMap.smul_apply, ho j i hji, smul_zero]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

private theorem mem_self_lemma_9 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

private theorem isSD_lemma_8 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {S : Subring K} (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι]
    [DecidableEq ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i))) :
    IsSD S h (Submodule.span K (Set.range b)) (spanS S b) := by
  refine ⟨⟨fun _ hm => mem_span_lemma_4 hm, fun _ ha _ hm => smul_mem_lemma_2 ha hm,
    ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    rw [mem_iff_lemma] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    rw [form_sum_lemma_7 ho]
    exact sum_mem fun i _ => S.mul_mem (S.mul_mem (hS.star_mem _ (ha i)) (hc i)) (hu i).2.1
  · intro x hx
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    choose T hTS hT0 hTg using fun i => hS.frac (g i)
    refine ⟨∏ i, T i, Finset.prod_ne_zero_iff.2 fun i _ => hT0 i, ?_⟩
    rw [mem_iff_lemma]
    refine ⟨fun i => (∏ j, T j) * g i, fun i => ?_, ?_⟩
    · dsimp only
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
      exact S.mul_mem (S.prod_mem fun j _ => hTS j) (hTg i)
    · rw [Finset.smul_sum]
      simp only [smul_smul]
  · intro x hx hdual
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    rw [mem_iff_lemma]
    refine ⟨g, fun i => ?_, rfl⟩
    have h1 := hdual (b i) (mem_self_lemma_9 b i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single i] at h1
    · rw [map_smul, smul_eq_mul] at h1
      have h2 := S.mul_mem h1 (hu i).2.2
      rwa [mul_assoc, mul_inv_cancel₀ (hu i).1, mul_one] at h2
    · intro j _ hji
      rw [map_smul, ho i j (Ne.symm hji), smul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'

theorem uni_part {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    {e : ι → ℕ} {i₀ : ι} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) (x : ι → K) (hx : ∀ i, x i ∈ S)
    (hX : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧ (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
      c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧ (∀ k, e k ≠ e i₀ → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  set Xs := ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i with hXs
  have hπ0 : π ≠ 0 := hπ.ne
  have hp0 : π ^ e i₀ ≠ 0 := pow_ne_zero _ hπ0
  obtain ⟨h', hh'⟩ : ∃ h' : V →ₗ⋆[K] V →ₗ[K] K, ∀ v w, h' v w = (π ^ e i₀)⁻¹ * h v w :=
    ⟨(π ^ e i₀)⁻¹ • h, fun v w => by simp only [LinearMap.smul_apply, smul_eq_mul]⟩
  have hstar : ∀ v w, star (h v w) = h w v := fun v w => by
    rw [← starRingEnd_apply]
    exact hs.eq v w
  have hpstar : star ((π ^ e i₀)⁻¹) = (π ^ e i₀)⁻¹ := by rw [star_inv₀, star_pow, hπ.fix]
  have hs' : h'.IsSymm := LinearMap.IsSymm.mk fun v w => by
    rw [hh', hh', starRingEnd_apply, star_mul, hstar, hpstar, mul_comm]
  have hz : ∀ v w, h' v w = 0 → h v w = 0 := fun v w hvw => by
    rw [hh'] at hvw
    exact (mul_eq_zero.1 hvw).resolve_left (inv_ne_zero hp0)
  have hd' : ∀ v, h' v v = 0 → v = 0 := fun v hv => hd v (hz v v hv)
  have hconv : ∀ v, h' v v = h v v * (π ^ e i₀)⁻¹ := fun v => by rw [hh', mul_comm]
  obtain ⟨bP, hbP⟩ : ∃ bP : {i // e i = e i₀} → V, ∀ p, bP p = b p := ⟨fun p => b p, fun _ => rfl⟩
  have hoP : ∀ p q, p ≠ q → h' (bP p) (bP q) = 0 := fun p q hpq => by
    rw [hh', hbP, hbP, ho _ _ (fun hq => hpq (Subtype.ext hq)), mul_zero]
  have huP : ∀ p, IsUnitIn S (h' (bP p) (bP p)) := fun p => by
    rw [hconv, hbP]
    have := hu p
    rwa [p.2] at this
  have hSD := isSD_lemma_8 hS hoP huP
  have hXeq : Xs = ∑ p : {i // e i = e i₀}, x p • bP p := by
    simp only [hbP]
    exact Finset.sum_subtype _ (fun i => by simp) (fun i => x i • b i)
  have hXL : Xs ∈ spanS S bP := (mem_iff_lemma _ _).2 ⟨fun p => x p, fun p => hx p, hXeq⟩
  have hXu' : IsUnitIn S (h' Xs Xs) := by
    rw [hconv]
    exact hX
  have hXX : h' Xs Xs ≠ 0 := hXu'.1
  have hX0 : Xs ≠ 0 := fun h0 => hXX (by rw [h0, map_zero])
  have hXW : Xs ∈ Submodule.span K (Set.range bP) := mem_span_lemma_4 hXL
  obtain ⟨k, f, hof, huf, hspf, hspanf⟩ := sd_basis hS hπ hs' hd' _
    (cutW h' (Submodule.span K (Set.range bP)) Xs) (cutM h' (spanS S bP) Xs) le_rfl
    (hSD.cut hXL hXu')
  have hinf : K ∙ Xs ⊓ cutW h' (Submodule.span K (Set.range bP)) Xs = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv1
    have hv2' : t • Xs ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hv2
    have ht := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv2').2
    rw [map_smul, smul_eq_mul] at ht
    rw [(mul_eq_zero.1 ht).resolve_right hXX, zero_smul]
    exact Submodule.zero_mem _
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ Xs)
    (cutW h' (Submodule.span K (Set.range bP)) Xs)
  rw [sup_cutW hXW hXX, hinf, finrank_bot, finrank_span_singleton hX0, ← hspanf,
    finrank_span_eq_card (linInd_lemma_6 hof (fun j => (huf j).1)),
    finrank_span_eq_card (linInd_lemma_6 hoP (fun p => (huP p).1)), Fintype.card_fin] at e1
  set p₀ : {i // e i = e i₀} := ⟨i₀, rfl⟩ with hp₀
  have hQ : Fintype.card {p : {i // e i = e i₀} // p ≠ p₀} = k := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  let σ := Fintype.equivFinOfCardEq hQ
  obtain ⟨gP, hg0, hgq⟩ : ∃ gP : {i // e i = e i₀} → V, gP p₀ = Xs ∧
      ∀ q : {p : {i // e i = e i₀} // p ≠ p₀}, gP q.1 = f (σ q) :=
    ⟨fun p => if hp : p = p₀ then Xs else f (σ ⟨p, hp⟩), dif_pos rfl, fun q => dif_neg q.2⟩
  obtain ⟨c, hcP, hcn⟩ : ∃ c : ι → V, (∀ p : {i // e i = e i₀}, c p = gP p) ∧
      ∀ i, e i ≠ e i₀ → c i = b i :=
    ⟨fun i => if hi : e i = e i₀ then gP ⟨i, hi⟩ else b i, fun p => dif_pos p.2,
      fun i hi => dif_neg hi⟩
  have hc0 : c i₀ = Xs := (hcP p₀).trans hg0
  have hXf : ∀ j, h Xs (f j) = 0 := fun j => by
    have hm : f j ∈ cutW h' (Submodule.span K (Set.range bP)) Xs := by
      rw [← hspanf]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hm' : f j ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hm
    exact hz _ _ (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hm').2)
  have hfX : ∀ j, h (f j) Xs = 0 := fun j => by rw [← hstar, hXf, star_zero]
  have hgo : ∀ p p' : {i // e i = e i₀}, p ≠ p' → h (gP p) (gP p') = 0 := by
    intro p p' hpp
    by_cases hp : p = p₀
    · have hp' : p' ≠ p₀ := fun hq => hpp (hp.trans hq.symm)
      rw [hp, hg0, show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
      exact hXf _
    · by_cases hp' : p' = p₀
      · rw [hp', hg0, show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
        exact hfX _
      · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩,
          show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
        exact hz _ _ (hof _ _ (fun hq => hpp (congrArg Subtype.val (σ.injective hq))))
  have hfL : ∀ j, f j ∈ spanS S bP := fun j => (mem_cutM.1 ((hspf _).1 (mem_self_lemma_9 f j))).1
  have hgL : ∀ p, gP p ∈ spanS S bP := fun p => by
    by_cases hp : p = p₀
    · rw [hp, hg0]
      exact hXL
    · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
      exact hfL _
  have hperp : ∀ w ∈ Submodule.span K (Set.range bP), ∀ j, e j ≠ e i₀ →
      h w (b j) = 0 ∧ h (b j) w = 0 := by
    intro w hw j hj
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    have hne : ∀ p : {i // e i = e i₀}, (p : ι) ≠ j := fun p hq => hj (hq ▸ p.2)
    constructor
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, LinearMap.sum_apply]
        exact Finset.sum_eq_zero fun p _ => by
          rw [map_smulₛₗ, LinearMap.smul_apply, hbP, ho _ _ (hne p), smul_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum]
        exact Finset.sum_eq_zero fun p _ => by
          rw [map_smul, hbP, ho _ _ (hne p).symm, smul_zero]
  have hoc : ∀ i j, i ≠ j → h (c i) (c j) = 0 := by
    intro i j hij
    by_cases hi : e i = e i₀
    · by_cases hj : e j = e i₀
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact hgo _ _ (fun hq => hij (congrArg Subtype.val hq))
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hcn j hj]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) j hj).1
    · rw [hcn i hi]
      by_cases hj : e j = e i₀
      · rw [show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) i hi).2
      · rw [hcn j hj]
        exact ho i j hij
  have huc : ∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹) := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hi, ← hconv]
      by_cases hp : (⟨i, hi⟩ : {i // e i = e i₀}) = p₀
      · rw [hp, hg0]
        exact hXu'
      · rw [show gP ⟨i, hi⟩ = f (σ ⟨⟨i, hi⟩, hp⟩) from hgq ⟨⟨i, hi⟩, hp⟩]
        exact huf _
    · rw [hcn i hi]
      exact hu i
  have h1 : ∀ i, c i ∈ spanS S b := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩]
      exact spanS_le_lemma_3 (fun p => by rw [hbP]; exact mem_self_lemma_9 b p) (hgL _)
    · rw [hcn i hi]
      exact mem_self_lemma_9 b i
  have hfc : ∀ j, f j ∈ spanS S c := fun j => by
    have hfj : f j = c (σ.symm j).1.1 := by rw [hcP, hgq, Equiv.apply_symm_apply]
    rw [hfj]
    exact mem_self_lemma_9 c _
  have h2 : ∀ i, b i ∈ spanS S c := by
    intro i
    by_cases hi : e i = e i₀
    · have hbi : b i ∈ spanS S bP := by
        have hm := mem_self_lemma_9 (S := S) bP ⟨i, hi⟩
        rwa [hbP] at hm
      have hr := (hspf _).2 (proj_mem hSD.toIsLatIn hXL hXu' hbi)
      have ha : h' Xs (b i) * (h' Xs Xs)⁻¹ ∈ S := S.mul_mem (hSD.int _ hXL _ hbi) hXu'.2.2
      have key : b i = (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs
          + (b i - (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs) := by abel
      rw [key]
      refine add_mem (smul_mem_lemma_2 ha ?_) (spanS_le_lemma_3 hfc hr)
      rw [← hc0]
      exact mem_self_lemma_9 c i₀
    · rw [← hcn i hi]
      exact mem_self_lemma_9 c i
  obtain ⟨hspc, hiffc⟩ := spans_eq_lemma_5 h1 h2
  exact ⟨c, hoc, huc, hc0, hcn, hspc, hiffc⟩

end Formalism.L2.SG.Pf.G3
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SumFilterSmul
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sums {J : Type} [Fintype J] {b : J → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c d : J → K) :
    h (∑ i, c i • b i) (∑ i, d i • b i) = ∑ i, star (c i) * d i * h (b i) (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ₂, G3.form_sum_orth ho d i, starRingEnd_apply, smul_eq_mul, mul_assoc]

theorem sum_filter_smul {J : Type} [Fintype J] (p : J → Prop) [DecidablePred p] (x : J → K)
    (b : J → V) :
    ∑ i ∈ Finset.univ.filter p, x i • b i = ∑ i, (if p i then x i else 0) • b i := by
  simp only [Finset.sum_filter, ite_smul, zero_smul]

private theorem unit_mul_lemma {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) :
    IsUnitIn S (a * b) := by
  obtain ⟨ha0, haS, haI⟩ := ha
  obtain ⟨hb0, hbS, hbI⟩ := hb
  refine (⟨mul_ne_zero ha0 hb0, S.mul_mem haS hbS, ?_⟩ : a * b ≠ 0 ∧ a * b ∈ S ∧ (a * b)⁻¹ ∈ S)
  rw [mul_inv]
  exact S.mul_mem haI hbI

private theorem unit_add_dv_lemma_2 (hπ : IsUnif S π) {u d : K} (hu : IsUnitIn S u) (hd : Dv S π d) :
    IsUnitIn S (u + d) := by
  have hu' : u ≠ 0 ∧ u ∈ S ∧ u⁻¹ ∈ S := hu
  have hd' : d * π⁻¹ ∈ S := hd
  have e : u * (1 + π * (u⁻¹ * (d * π⁻¹))) = u + d := by
    rw [mul_add, mul_one, mul_left_comm u π, mul_inv_cancel_left₀ hu'.1, mul_left_comm π d,
      mul_inv_cancel₀ hπ.3, mul_one]
  rw [← e]
  exact unit_mul_lemma hu (hπ.5 _ (S.mul_mem hu'.2.2 hd'))

theorem rebaseAt_of (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hUP : ∀ (J : Type) [Fintype J] [DecidableEq J] (b : J → V) (e : J → ℕ) (i₀ : J),
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∀ x : J → K, (∀ i, x i ∈ S) →
      IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
        (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧
        (∀ k, e k ≠ e i₀ → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b)
    (hAB : ∀ (J : Type) [Fintype J] [DecidableEq J] (e : J → ℕ) (i₀ : J) (x : J → K),
      (∀ i, x i ∈ S) → ∀ T : Finset J, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : J → V,
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧ (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b) :
    G3.RebaseAt S π h := by
  intro J _ _ b e i₀ ho hu hmin X hX hXu
  obtain ⟨x, hxS, rfl⟩ := hX
  have hπ0 : π ≠ 0 := hπ.3
  have hterm : ∀ i, e i ≠ e i₀ →
      Dv S π (star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹) := by
    intro i hi
    have hlt : e i₀ < e i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
    have hP : π ^ e i ≠ 0 := pow_ne_zero _ hπ0
    have hw : h (b i) (b i) * (π ^ e i)⁻¹ ∈ S := (show _ ∧ _ ∧ _ from hu i).2.1
    have hs : star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) ∈ S :=
      S.mul_mem (S.mul_mem (hS.1 _ (hxS i)) (hxS i)) hw
    have hk : Dv S π (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [← pow_sub₀ π hπ0 (hmin i)]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      show π ^ (e i - e i₀) * π⁻¹ ∈ S
      rw [hm, show e i₀ + m + 1 - e i₀ = m + 1 by omega, pow_succ, mul_inv_cancel_right₀ hπ0]
      exact S.pow_mem hπ.1 m
    have e1 : star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹ =
        star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) * (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [mul_assoc _ (_ * _⁻¹), mul_assoc (h (b i) (b i)), inv_mul_cancel_left₀ hP, ← mul_assoc]
    rw [e1]
    exact Dv.mul_left hk hs
  have hD : Dv S π (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹ -
      h (∑ i, x i • b i) (∑ i, x i • b i) * (π ^ e i₀)⁻¹) := by
    rw [sum_filter_smul, form_sums ho, form_sums ho, ← sub_mul, ← Finset.sum_sub_distrib,
      Finset.sum_mul]
    refine Finset.sum_induction _ (Dv S π) (fun _ _ ha hb => Dv.add ha hb) ?_ fun i _ => ?_
    · show (0 : K) * π⁻¹ ∈ S
      rw [zero_mul]
      exact S.zero_mem
    · by_cases hi : e i = e i₀
      · rw [if_pos hi, sub_self, zero_mul]
        show (0 : K) * π⁻¹ ∈ S
        rw [zero_mul]
        exact S.zero_mem
      · rw [if_neg hi, star_zero, zero_mul, zero_mul, zero_sub, neg_mul]
        exact Dv.neg (hterm i hi)
  have hYu : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) := by
    have e2 : ∀ p q : K, p + (q - p) = q := fun p q => by ring
    have := unit_add_dv_lemma_2 hπ hXu hD
    rwa [e2] at this
  obtain ⟨c, hco, hcu, hci0, hck, hspan, hspanS⟩ := hUP J b e i₀ ho hu x hxS hYu
  have hi₀T : i₀ ∉ Finset.univ.filter (fun j => ¬ e j = e i₀) := fun hm =>
    (Finset.mem_filter.mp hm).2 rfl
  have hTlt : ∀ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), e i₀ < e j := fun j hj =>
    lt_of_le_of_ne (hmin j) (Ne.symm (Finset.mem_filter.mp hj).2)
  obtain ⟨c', hco', hcu', hc'i0, hc'k, hspan', hspanS'⟩ :=
    hAB J e i₀ x hxS _ hi₀T hTlt c hco hcu
  have hT' : ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • c j =
      ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • b j :=
    Finset.sum_congr rfl fun j hj => by rw [hck j (Finset.mem_filter.mp hj).2]
  refine ⟨c', hco', hcu', ?_, hspan'.trans hspan, fun v => (hspanS' v).trans (hspanS v)⟩
  rw [hc'i0, hci0, hT', Finset.sum_filter_add_sum_filter_not]

end

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem rebasing_holds : G3.Rebase := by
  intro K V _ _ _ _ _ S π h hS hπ hs hd
  exact rebaseAt_of hS hπ
    (fun J _ _ b e i₀ ho hu x hx hX => G3.uni_part hS hπ hs hd ho hu x hx hX)
    (fun J _ _ e i₀ x hx T hT hlt b ho hu => G3.absorb hS hπ hs x hx T hT hlt b ho hu)

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSpanHolds
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds :
    ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
      [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
      (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F),
      𝔭.IsMaximal → ∀ (n : ℕ) (b : Fin n → V),
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
        Submodule.span K (Set.range b) = ⊤ := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  letI : Submodule.IsFullLattice K L := hL
  rw [eq_top_iff, ← Submodule.IsFullLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have span_of_jordan (c : Fin (finrank K (⊤ : Submodule K V)) → V)
      (d : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
      (ho : ∀ i j, i ≠ j → h (c i) (c j) = 0)
      (hn : ∀ i, h (c i) (c i) = algebraMap F K ((d i : 𝓞 F) : F))
      (hd : ∀ i, d i ≠ 0) : Submodule.span K (Set.range c) = ⊤ := by
    have hi : LinearIndependent K c := LinearMap.linearIndependent_of_isOrthoᵢ ho (fun i => by
      rw [hn i]
      apply (map_ne_zero (algebraMap F K)).2
      intro hz
      apply hd i
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using hz))
    apply hi.span_eq_top_of_card_eq_finrank'
    simp
  have hsp := span_of_jordan b a hbo hbn hba
  have hsp' := span_of_jordan b' a' hbo' hbn' hba'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
