module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrAlg
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}

theorem step_basis (β : Module.Basis (Fin n) K V) {s : ℕ} (hs : s ≤ n) {W : Submodule K V}
    (hW : W = Submodule.span K (β '' {k | (k : ℕ) < s})) :
    ∃ γ : Module.Basis (Fin s) K W, (∀ k, (γ k : V) = β (Fin.castLE hs k)) ∧
      (∀ (x : W) k, β.repr x (Fin.castLE hs k) = γ.repr x k) ∧
      ∀ (x : W) (l : Fin n), s ≤ l → β.repr x l = 0 := by
  subst hW
  have hmem : ∀ k : Fin s, β (Fin.castLE hs k) ∈ Submodule.span K (β '' {k | (k : ℕ) < s}) :=
    fun k => Submodule.subset_span ⟨Fin.castLE hs k, by simp, rfl⟩
  let f : Fin s → Submodule.span K (β '' {k | (k : ℕ) < s}) := fun k => ⟨β (Fin.castLE hs k), hmem k⟩
  have hli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (Submodule.span K (β '' {k | (k : ℕ) < s})).subtype
    exact β.linearIndependent.comp _ (Fin.castLE_injective hs)
  have hsp : ⊤ ≤ Submodule.span K (Set.range f) := by
    rw [← Submodule.span_span_coe_preimage (R := K) (s := β '' {k | (k : ℕ) < s})]
    apply Submodule.span_mono
    intro y hy
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    show β (Fin.castLE hs ⟨k, hk⟩) = y
    exact hky
  let γ := Module.Basis.mk hli hsp
  have hγ : ∀ k, (γ k : V) = β (Fin.castLE hs k) := fun k => by simp [γ, f]
  have key : ∀ (x : Submodule.span K (β '' {k | (k : ℕ) < s})) (l : Fin n),
      β.repr x l = ∑ k, γ.repr x k * (if Fin.castLE hs k = l then 1 else 0) := by
    intro x l
    conv_lhs => rw [← γ.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, hγ, map_sum, map_smul,
        Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
        smul_eq_mul]
  refine ⟨γ, hγ, fun x k => ?_, fun x l hl => ?_⟩
  · rw [key, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [(Fin.castLE_injective hs).ne hj]
    · simp
  · rw [key]
    apply Finset.sum_eq_zero
    intro k _
    have : Fin.castLE hs k ≠ l := by
      intro h
      rw [← h] at hl
      simp at hl
      omega
    simp [this]

private theorem isLatOf_sub_of_basis_castLE (C : ACurve K) {Λ : C.I → AddSubgroup V} (i : C.I)
    (e : Module.Basis (Fin n) K V) {s : ℕ} (hs : s ≤ n) {W : Submodule K V}
    (ε : Module.Basis (Fin s) K W)
    (h2 : ∀ (x : W) k, e.repr x (Fin.castLE hs k) = ε.repr x k)
    (h3 : ∀ (x : W) (l : Fin n), s ≤ l → e.repr x l = 0)
    (he : IsLatOf C i e (Λ i)) : IsLatOf C i ε (sub C Λ W i) := by
  unfold IsLatOf at he ⊢
  intro x
  have hx : x ∈ sub C Λ W i ↔ (x : V) ∈ Λ i := Iff.rfl
  rw [hx, he]
  constructor
  · intro h k
    rw [← h2]
    exact h _
  · intro h q
    by_cases hq : (q : ℕ) < s
    · have hq' : q = Fin.castLE hs ⟨q, hq⟩ := rfl
      rw [hq', h2]
      exact h _
    · rw [h3 x q (by omega)]
      simp

private theorem v_repr_le_one_of_basis_change (C : ACurve K) (i : C.I) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : Module.Basis ι K V) (e' : Module.Basis ι' K V) (hee : ∀ k l, C.v i (e'.repr (e k) l) ≤ 1)
    (x : V) (hx : ∀ k, C.v i (e.repr x k) ≤ 1) (l : ι') : C.v i (e'.repr x l) ≤ 1 := by
  have hsum : e'.repr x l = ∑ k, e.repr x k * e'.repr (e k) l := by
    conv_lhs => rw [← e.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hsum]
  apply Valuation.map_sum_le
  intro k _
  rw [map_mul]
  exact mul_le_one' (hx k) (hee k l)

private theorem finite_setOf_not_isLatOf (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) : {i | ¬ IsLatOf C i β (Λ i)}.Finite := by
  obtain ⟨-, b0, hb0⟩ := hΛ
  have hfin : ∀ e : K, {i | 1 < C.v i e}.Finite := by
    intro e
    by_cases he : e = 0
    · simp [he]
    · exact (C.fin e he).subset (fun i hi => ne_of_gt hi)
  have hS : ({i | ¬IsLatOf C i b0 (Λ i)} ∪ (⋃ k, ⋃ l, {i | 1 < C.v i (β.repr (b0 k) l)}) ∪
      (⋃ k, ⋃ l, {i | 1 < C.v i (b0.repr (β k) l)})).Finite :=
    (hb0.union (Set.finite_iUnion fun k => Set.finite_iUnion fun l => hfin _)).union
      (Set.finite_iUnion fun k => Set.finite_iUnion fun l => hfin _)
  apply hS.subset
  intro i hi
  by_contra hni
  apply hi
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_lt,
    not_not] at hni
  obtain ⟨⟨h0, h1⟩, h2⟩ := hni
  unfold IsLatOf at h0 ⊢
  intro x
  rw [h0 x]
  exact ⟨fun hx l => v_repr_le_one_of_basis_change C i b0 β h1 x hx l, fun hx l => v_repr_le_one_of_basis_change C i β b0 h2 x hx l⟩

private theorem isLatOf_reindex' (C : ACurve K) (i : C.I) {U : Type} [AddCommGroup U] [Module K U]
    {m r : ℕ} (d : Module.Basis (Fin m) K U) (e : Fin m ≃ Fin r) (L : AddSubgroup U)
    (h : IsLatOf C i d L) : IsLatOf C i (d.reindex e) L := by
  unfold IsLatOf at h ⊢
  intro x
  rw [h x]
  simp only [Module.Basis.repr_reindex_apply]
  exact ⟨fun hx q => hx _, fun hx k => by simpa using hx (e k)⟩

theorem subDeg_step [FiniteDimensional K V] (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V) (hb : ∀ i, IsLatOf C i (b i) (Λ i))
    {s : ℕ} (hs : s ≤ n) (tri : ∀ i (k l : Fin n), (k : ℕ) < s → k < l → β.repr (b i k) l = 0) :
    (∀ i, ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) ≠ 0) ∧
      {i | C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k)) ≠ 1}.Finite ∧
      subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s})) =
        ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) := by
  set W := Submodule.span K (β '' {k | (k : ℕ) < s}) with hWdef
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := step_basis β hs (W := W) rfl
  have hbi : ∀ i, W = Submodule.span K ((b i) '' {k | (k : ℕ) < s}) := by
    intro i
    obtain ⟨δ, -, -, -⟩ := step_basis (b i) hs (W := Submodule.span K ((b i) '' {k | (k : ℕ) < s})) rfl
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, hWdef, β.mem_span_image]
      intro l hl
      rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
      simp only [Set.mem_setOf_eq]
      by_contra hls
      exact hl (tri i k l hk (Fin.lt_iff_val_lt_val.mpr (by simp only [Set.mem_setOf_eq] at hk; omega)))
    · rw [Module.finrank_eq_card_basis δ, Module.finrank_eq_card_basis γ]
  choose δ hδ1 hδ2 hδ3 using fun i => step_basis (b i) hs (hbi i)
  have hlat : ∀ i, IsLatOf C i (δ i) (sub C Λ W i) :=
    fun i => isLatOf_sub_of_basis_castLE C i (b i) hs (δ i) (hδ2 i) (hδ3 i) (hb i)
  have hD : ∀ i, γ.det (δ i) = ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) := by
    intro i
    rw [Module.Basis.det_apply, Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_congr rfl
      intro k _
      rw [Module.Basis.toMatrix_apply, ← hγ2, hδ1]
    · intro k l hlk
      rw [Module.Basis.toMatrix_apply, ← hγ2, hδ1]
      exact tri i _ _ (by simp) (Fin.lt_iff_val_lt_val.mpr (by simpa using hlk))
  have hne : ∀ i, ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) ≠ 0 := by
    intro i
    rw [← hD]
    exact (γ.isUnit_det (δ i)).ne_zero
  have hfinP : {i | C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k)) ≠ 1}.Finite := by
    apply (finite_setOf_not_isLatOf C hΛ β).subset
    intro i hi hβ
    apply hi
    rw [← hD]
    exact Inhab.v_det C (isLatOf_sub_of_basis_castLE C i β hs γ hγ2 hγ3 hβ) (hlat i)
  refine ⟨hne, hfinP, ?_⟩
  have hr : Module.finrank K W = s := by rw [Module.finrank_eq_card_basis γ, Fintype.card_fin]
  set e : Fin s ≃ Fin (Module.finrank K W) := finCongr hr.symm
  have hdeg : subDeg C Λ W = ∑ᶠ i, (C.w i : ℤ) *
      WithZero.log (C.v i ((Module.finBasis K W).det ((δ i).reindex e))) :=
    Inhab.deg_eq C _ (fun i => isLatOf_reindex' C i (δ i) e _ (hlat i))
  rw [hdeg]
  set c := (Module.finBasis K W).det (γ.reindex e)
  have hc : c ≠ 0 := ((Module.finBasis K W).isUnit_det _).ne_zero
  have hsplit : ∀ i, (Module.finBasis K W).det ((δ i).reindex e) =
      c * ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k) := by
    intro i
    rw [← hD, ← (Module.finBasis K W).det_mul_det (γ.reindex e) ((δ i).reindex e),
      Module.Basis.det_reindex]
    congr 2
    ext k
    simp
  simp_rw [hsplit]
  have hlog : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (c * ∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs k)) (Fin.castLE hs k))) := by
    intro i
    rw [map_mul, WithZero.log_mul ((C.v i).ne_zero_iff.mpr hc) ((C.v i).ne_zero_iff.mpr (hne i)), mul_add]
  simp_rw [hlog]
  rw [finsum_add_distrib, C.prod c hc, zero_add]
  · apply (C.fin c hc).subset
    intro i hi h1
    apply hi
    simp [h1]
  · apply hfinP.subset
    intro i hi h1
    apply hi
    simp [h1]

theorem subDeg_succ [FiniteDimensional K V] (C : ACurve K) {Λ : C.I → AddSubgroup V} (hΛ : IsBun C Λ)
    (β : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V) (hb : ∀ i, IsLatOf C i (b i) (Λ i))
    (s : Fin n) (tri : ∀ i (k l : Fin n), k ≤ s → k < l → β.repr (b i k) l = 0) :
    (∀ i, β.repr (b i s) s ≠ 0) ∧ {i | C.v i (β.repr (b i s) s) ≠ 1}.Finite ∧
      subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s + 1})) -
          subDeg C Λ (Submodule.span K (β '' {k | (k : ℕ) < s})) =
        ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (β.repr (b i s) s)) := by
  have hs1 : (s : ℕ) + 1 ≤ n := s.isLt
  have hs0 : (s : ℕ) ≤ n := s.isLt.le
  obtain ⟨ne1, fin1, eq1⟩ := subDeg_step C hΛ β b hb hs1 (fun i k l hk hkl =>
    tri i k l (Fin.le_iff_val_le_val.mpr (by omega)) hkl)
  obtain ⟨ne0, fin0, eq0⟩ := subDeg_step C hΛ β b hb hs0 (fun i k l hk hkl =>
    tri i k l (Fin.le_iff_val_le_val.mpr (by omega)) hkl)
  have hprod : ∀ i, ∏ k : Fin ((s : ℕ) + 1), β.repr (b i (Fin.castLE hs1 k)) (Fin.castLE hs1 k) =
      (∏ k : Fin s, β.repr (b i (Fin.castLE hs0 k)) (Fin.castLE hs0 k)) * β.repr (b i s) s := by
    intro i
    rw [Fin.prod_univ_castSucc]
    have h1 : ∀ k : Fin s, Fin.castLE hs1 (Fin.castSucc k) = Fin.castLE hs0 k := fun k => Fin.ext (by simp)
    have h2 : Fin.castLE hs1 (Fin.last s) = s := Fin.ext (by simp)
    simp only [h1, h2]
  have hd : ∀ i, β.repr (b i s) s ≠ 0 := by
    intro i
    have := ne1 i
    rw [hprod] at this
    exact right_ne_zero_of_mul this
  have hdfin : {i | C.v i (β.repr (b i s) s) ≠ 1}.Finite := by
    apply (fin1.union fin0).subset
    intro i hi
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, hprod, map_mul] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [h2, one_mul] at h1
    exact hi h1
  refine ⟨hd, hdfin, ?_⟩
  rw [eq1, eq0]
  have hlog : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin ((s : ℕ) + 1),
      β.repr (b i (Fin.castLE hs1 k)) (Fin.castLE hs1 k))) =
      (C.w i : ℤ) * WithZero.log (C.v i (∏ k : Fin s, β.repr (b i (Fin.castLE hs0 k)) (Fin.castLE hs0 k))) +
        (C.w i : ℤ) * WithZero.log (C.v i (β.repr (b i s) s)) := by
    intro i
    rw [hprod, map_mul, WithZero.log_mul ((C.v i).ne_zero_iff.mpr (ne0 i)) ((C.v i).ne_zero_iff.mpr (hd i)),
      mul_add]
  simp_rw [hlog]
  rw [finsum_add_distrib, add_sub_cancel_left]
  · apply fin0.subset
    intro i hi h1
    apply hi
    simp [h1]
  · apply hdfin.subset
    intro i hi h1
    apply hi
    simp [h1]

end PositivityTheory.HtPt.Ci
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_zero' {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) : ValAt ξ z 0 0 :=
  ⟨h, 0, map_zero _, map_zero _⟩

theorem lieValAt_sum {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {ER : Type} [AddCommGroup ER] [Module R ER]
    {MR : LieModel G z ER} {ι : Type} (T : Finset ι) {e : ι → V} {v : ι → ER}
    (hv : ∀ k, M.ValAt z (e k) (MR.pt (v k))) : M.ValAt z (∑ k ∈ T, e k) (MR.pt (∑ k ∈ T, v k)) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, MR.pt_zero]; exact M.valAt_zero h
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, MR.add]; exact (hv a).add ih

theorem val_coords (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {ER : Type} [AddCommGroup ER] [Module R ER]
    {MR : LieModel G z ER} {n : ℕ} {B : Fin n → V} (hB : M.lat.IsFrameAt B ⟨centre z, h⟩)
    {bz : Module.Basis (Fin n) R ER} (hbz : ∀ q, M.ValAt z (B q) (MR.pt (bz q))) {e : V} {v : ER}
    (hv : M.ValAt z e (MR.pt v)) : ∃ c : Fin n → Ω, e = ∑ k, c k • B k ∧ ∀ k, ValAt ξ z (c k) (bz.repr v k) := by
  obtain ⟨_, he⟩ := (M.exists_valAt_iff z e).1 ⟨_, hv⟩
  rw [hB.2, Submodule.mem_span_range_iff_exists_fun] at he
  obtain ⟨c, hc⟩ := he
  choose s hs using fun q => (c q).2
  have hval : ∀ k, ValAt ξ z (c k : Ω) ((Scheme.stalkClosedPointTo z).hom (s k)) := fun k => ⟨h, s k, hs k, rfl⟩
  have h1 := lieValAt_sum h Finset.univ fun k => lieValAt_smul (hbz k) (hval k)
  have he : e = ∑ k, (c k : Ω) • B k := hc.symm
  rw [← he] at h1
  refine ⟨fun k => c k, he, fun k => ?_⟩
  rw [MR.inj (hv.unique hξ h1), bz.repr_sum_self]
  exact hval k

theorem coord_zero {n : ℕ} {B : Fin n → V} (hB : LinearIndependent Ω B) {c : Fin n → Ω} {T : Set (Fin n)}
    (h : ∑ k, c k • B k ∈ Submodule.span Ω (B '' T)) {l : Fin n} (hl : l ∉ T) : c l = 0 := by
  obtain ⟨φ, h1, h0⟩ := FlagGrGen.exists_coord hB l
  have h2 : Submodule.span Ω (B '' T) ≤ LinearMap.ker φ := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact h0 k fun e => hl (e ▸ hk))
  have h3 : φ (∑ k, c k • B k) = 0 := h2 h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single l (fun k _ hk => by rw [map_smul, h0 k hk, smul_zero]) (by simp)] at h3
  simpa [h1] using h3

theorem flagStep_of_append {r r' : ℕ} {b : Fin r → V} {B : Fin (r + r') → V} (hB : ∀ k, B (Fin.castAdd r' k) = b k)
    {s : ℕ} (hs : s ≤ r) : flagStep Ω b s = Submodule.span Ω (B '' {k | (k : ℕ) < s}) := by
  unfold flagStep
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Fin.castAdd r' k, hk, hB k⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, lt_of_lt_of_le hk hs⟩, hk, (hB _).symm⟩

theorem exists_frame {S : Set (Cpt ξ)} {Λ L L' : Lat ξ V} {r r' : ℕ} {b₀ : Fin r → V} {U' : Submodule Ω V}
    (hL : L.IsFlagVBOn S b₀) (hL' : L'.IsVBOn S r' U') (hc : IsCompl (Submodule.span Ω (Set.range b₀)) U')
    (hΛ : ∀ q ∈ S, Λ q = L q ⊔ L' q) {p : Cpt ξ} (hp : p ∈ S) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∃ (b : Fin r → V) (B : Fin (r + r') → V), (∀ k, B (Fin.castAdd r' k) = b k) ∧
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ ∀ q ∈ S, q.1 ∈ U → L.IsFrameAt b q ∧ Λ.IsFrameAt B q := by
  obtain ⟨U₁, h1, b, hb, hb'⟩ := hL p hp
  obtain ⟨U₂, h2, c, hc1, hc'⟩ := hL' p hp
  have hr : ∀ b : Fin r → V, flagStep Ω b r = Submodule.span Ω (Set.range b) := fun b => by
    unfold flagStep
    congr 1
    ext x
    simp
  have e : Fin.append b c = Sum.elim b c ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp
  refine ⟨U₁ ⊓ U₂, ⟨h1, h2⟩, b, Fin.append b c, fun k => Fin.append_left _ _ _, hb, fun q hq hU => ?_⟩
  have f1 := hb' q hq hU.1
  have f2 := hc' q hq hU.2
  refine ⟨f1, ?_, ?_⟩
  · rw [e]
    refine (f1.1.sum_type f2.1 ?_).comp _ finSumFinEquiv.symm.injective
    rw [← hr, hb, hr, hc1]
    exact hc.disjoint
  · rw [hΛ q hq, f1.2, f2.2, e, finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]

theorem gr_deg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  intro X Ω _ ξ K _ C z Y G _ _ V _ _ M Vz _ _ _ Mz h₀ h S L L' r r' b₀ U' hξ hs hz hS hb₀ hL hL' hc hΛ
  obtain ⟨U, hU, b, B, hB, hb, hfr⟩ := exists_frame hL hL' hc hΛ hz
  obtain ⟨fb, fB⟩ := hfr _ hz hU
  obtain ⟨β, hβ⟩ := frame_basis hξ hs M z h₀ Mz fB
  have hloc : ∀ i, ∃ (b : Fin r → V) (B : Fin (r + r') → V), (∀ k, B (Fin.castAdd r' k) = b k) ∧
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ L.IsFrameAt b ⟨_, h i⟩ ∧ M.lat.IsFrameAt B ⟨_, h i⟩ := fun i => by
    obtain ⟨U, hU, b, B, hB, hb, hfr⟩ := exists_frame hL hL' hc hΛ (hS i)
    exact ⟨b, B, hB, hb, hfr _ (hS i) hU⟩
  choose bi Bi hBi hbi fbi fBi using hloc
  choose βi hβi hlat using fun i => frame_lat hξ hs M Y Mz i (h i) (fBi i)
  have hbun : IsBun C (Y.lieLat Mz) := by
    have hn : Module.finrank K Vz = r + r' := by rw [Module.finrank_eq_card_basis β, Fintype.card_fin]
    rw [IsBun, hn]
    refine ⟨fun i => ⟨_, hlat i⟩, β, (Y.ae U hU).subset fun i hi hiU => hi ?_⟩
    obtain ⟨β', h1, h2⟩ := frame_lat hξ hs M Y Mz i (h i) (hfr _ (hS i) hiU).2
    have : β' = β := Module.Basis.eq_of_apply_eq fun q => Mz.inj ((h1 q).unique hξ (hβ q))
    exact this ▸ h2
  refine ⟨fun s => Submodule.span K (β '' {k | (k : ℕ) < s}), by simp, le_antisymm ?_ ?_, fun s => ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨B k, ?_, hβ k⟩
    rw [fb.2]
    exact Submodule.subset_span ⟨⟨k, hk⟩, (hB _).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨e, he, hv⟩
    obtain ⟨c, hc1, hc2⟩ := val_coords hξ h₀ fB hβ hv
    have h1 : e ∈ flagStep Ω b r := by
      rw [fb.2] at he
      refine Submodule.span_subset_span _ Ω _ (Submodule.span_mono ?_ he)
      rintro _ ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    rw [flagStep_of_append hB le_rfl, hc1] at h1
    refine β.mem_span_image.2 fun l hl => ?_
    by_contra hcon
    have h2 := hc2 l
    rw [coord_zero fB.1 h1 hcon] at h2
    exact Finsupp.mem_support_iff.1 hl (LieTangent.valAt_unique hξ h2 (valAt_zero' h₀))
  · choose c hc1 hc2 using fun i k => val_coords hξ h₀ fB hβ (hβi i k)
    have hcz : ∀ i (k : Fin r) (l : Fin (r + r')), (k : ℕ) < l → c i (Fin.castAdd r' k) l = 0 := by
      intro i k l hl
      have h1 : bi i k ∈ flagStep Ω (bi i) (k + 1) := Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
      rw [hbi, ← hb, flagStep_of_append hB k.2, ← hBi, hc1] at h1
      exact coord_zero fB.1 h1 (Nat.not_lt.2 hl)
    obtain ⟨d1, d2, d3⟩ := subDeg_succ C hbun β βi hlat (Fin.castAdd r' s) fun i k l hk hl => by
      have h2 := hc2 i k l
      have hk' : (k : ℕ) < r := Nat.lt_of_le_of_lt hk s.2
      rw [show c i k l = 0 from hcz i ⟨k, hk'⟩ l hl] at h2
      exact LieTangent.valAt_unique hξ h2 (valAt_zero' h₀)
    obtain ⟨t, ht⟩ : ∃ t : Ω, b s - t • b₀ s ∈ flagStep Ω b₀ s := by
      have h1 : b s ∈ flagStep Ω b (s + 1) := Submodule.subset_span ⟨s, Nat.lt_succ_self _, rfl⟩
      have e : {k : Fin r | (k : ℕ) < s + 1} = insert s {k : Fin r | (k : ℕ) < s} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hb, flagStep, e, Set.image_insert_eq, Submodule.mem_span_insert] at h1
      obtain ⟨t, y, hy, h1⟩ := h1
      exact ⟨t, by rw [h1, add_sub_cancel_left]; exact hy⟩
    have g0 := FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ b _ s t hb₀ hb fb ht
    refine ⟨h₀, h, t, fun i => c i (Fin.castAdd r' s) (Fin.castAdd r' s) * t,
      fun i => β.repr (βi i (Fin.castAdd r' s)) (Fin.castAdd r' s), g0, fun i => ?_, fun i => ⟨d1 i, ?_⟩, d2, d3⟩
    · refine FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ (bi i) _ s _ hb₀ (hbi i) (fbi i) ?_
      have h1 : bi i s - c i (Fin.castAdd r' s) (Fin.castAdd r' s) • b s ∈ flagStep Ω b₀ s := by
        rw [← hb, flagStep_of_append hB s.2.le, ← hBi, ← hB]
        nth_rw 1 [hc1]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.castAdd r' s)), add_sub_cancel_left]
        refine sum_mem fun l hl => ?_
        by_cases hls : (l : ℕ) < s
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hls, rfl⟩)
        · have : (l : ℕ) ≠ s := fun e => (Finset.mem_erase.1 hl).1 (Fin.ext e)
          rw [hcz i s l (by omega), zero_smul]
          exact zero_mem _
      have h2 := add_mem h1 (Submodule.smul_mem _ (c i (Fin.castAdd r' s) (Fin.castAdd r' s)) ht)
      rwa [smul_sub, sub_add_sub_cancel, smul_smul] at h2
    · rw [mul_div_cancel_right₀ _ g0.1]
      exact hc2 i _ _

end PositivityTheory.HtPt.Ci
