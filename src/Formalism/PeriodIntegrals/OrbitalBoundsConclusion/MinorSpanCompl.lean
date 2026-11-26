module

public import Formalism.GradedWeylDivisibility.FinalD

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.MinorSpanCompl
noncomputable section

namespace PI

def minorX (R : Type) [CommRing R] (N p : ℕ) (I : Fin p ↪o Fin N) : MvPolynomial (ℕ × Fin N) R :=
  Matrix.det (Matrix.of fun i k : Fin p => MvPolynomial.X ((i : ℕ), I k))

def nablaSpan (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram) :
    Submodule R (MvPolynomial (ℕ × Fin N) R) :=
  Submodule.span R (Set.range fun I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) ↪o Fin N =>
    ∏ c : Fin (nu.rowLen 0), minorX R N (nu.colLen c) (I c))

def MinorSpanCompl : Prop :=
  ∀ (R : Type) [CommRing R] (N : ℕ) (nu : YoungDiagram),
    ∃ Cm : Submodule R (MvPolynomial (ℕ × Fin N) R), IsCompl (nablaSpan R N nu) Cm

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.RenameInitMinor
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.ShapeColumnDegreeColumnSizes
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.MSC

theorem card_colLen_gt (ν : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card = ν.rowLen t := by
  have hk : ν.rowLen t ≤ ν.rowLen 0 := ν.rowLen_anti 0 t (Nat.zero_le _)
  have hiff : ∀ c : Fin (ν.rowLen 0), t < ν.colLen c ↔ (c : ℕ) < ν.rowLen t := fun c => by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  simp_rw [hiff]
  rw [← Finset.card_map Fin.valEmbedding]
  have hm : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => (c : ℕ) < ν.rowLen t).map Fin.valEmbedding =
      Finset.range (ν.rowLen t) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [hm, Finset.card_range]

theorem rowLen_eq_zero (ν : YoungDiagram) {t : ℕ} (ht : ν.colLen 0 ≤ t) : ν.rowLen t = 0 := by
  by_contra h
  have h0 : (t, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero h)
  have h1 := YoungDiagram.mem_iff_lt_colLen.1 h0
  omega

theorem colLen_pos (ν : YoungDiagram) (c : Fin (ν.rowLen 0)) : 0 < ν.colLen c := by
  exact YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 c.2)

theorem card_fiber {γ : Type*} [Fintype γ] (h : γ → ℕ) {v : ℕ} (hv : 0 < v) :
    (Finset.univ.filter fun x => h x = v).card + (Finset.univ.filter fun x => v < h x).card =
      (Finset.univ.filter fun x => v - 1 < h x).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      omega
    · intro hx
      omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega

def sz0 (ν : YoungDiagram) : Fin (ν.rowLen 0) → ℕ := fun c => ν.colLen c

theorem hsz0 (ν : YoungDiagram) : ∀ c, sz0 ν c ≤ ν.colLen 0 := fun c => ν.colLen_anti 0 c (Nat.zero_le _)

def nuR (ν : YoungDiagram) : Fin (ν.colLen 0) → ℕ := fun t => ν.rowLen t

theorem shapeColumnDegree_columnSizes (ν : YoungDiagram) : shapeDeg (sz0 ν) (n := ν.colLen 0) = nuR ν := by
  funext t
  exact card_colLen_gt ν t

theorem initMinor_cast (R : Type) [CommRing R] {r n s s' : ℕ} (h : s' = s) (I : Fin s → Fin r)
    (hs : s ≤ n) (hs' : s' ≤ n) :
    initMinor R (I ∘ Fin.cast h) hs' = initMinor R I hs := by
  subst h
  rfl

theorem initMinor_zero (R : Type) [CommRing R] {r n s : ℕ} (h : s = 0) (I : Fin s → Fin r)
    (hs : s ≤ n) : initMinor R I hs = 1 := by
  subst h
  simp [initMinor]

private theorem reorder_lemma {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (h : ∀ v, Nat.card {x // f x = v} = Nat.card {y // g y = v}) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  classical
  have h' : ∀ v, Nonempty ({x // f x = v} ≃ {y // g y = v}) := fun v => Finite.card_eq.1 (h v)
  let ev : ∀ v, {x // f x = v} ≃ {y // g y = v} := fun v => (h' v).some
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight ev).trans
    (Equiv.sigmaFiberEquiv g)), fun x => ?_⟩
  exact (ev (f x) ⟨x, rfl⟩).2

theorem reorder (R : Type) [CommRing R] (ν : YoungDiagram) (N : ℕ) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ ν.colLen 0) (I : ∀ k, Fin (sz k) → Fin N) (hI : ∀ k, StrictMono (I k))
    (hsh : shapeDeg sz = nuR ν) :
    ∃ J : ∀ c : Fin (ν.rowLen 0), Fin (sz0 ν c) → Fin N, (∀ c, StrictMono (J c)) ∧
      bideterminant R sz hsz I = bideterminant R (sz0 ν) (hsz0 ν) J := by
  classical
  have hcnt : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < ν.colLen 0
    · have h := congrFun hsh ⟨t, ht⟩
      simpa [shapeDeg, nuR] using h
    · rw [rowLen_eq_zero ν (not_lt.1 ht), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hfib : ∀ v, 0 < v → (Finset.univ.filter fun k => sz k = v).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card := by
    intro v hv
    have h1 := card_fiber sz hv
    have h2 : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card +
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v < ν.colLen c).card =
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v - 1 < ν.colLen c).card :=
      card_fiber (fun c : Fin (ν.rowLen 0) => ν.colLen c) hv
    rw [hcnt, hcnt] at h1
    omega
  have hcard : ∀ v, Nat.card {x : {k : Fin K // 0 < sz k} // sz x.1 = v} =
      Nat.card {c : Fin (ν.rowLen 0) // ν.colLen c = v} := by
    intro v
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [Fintype.card_eq_zero_iff.2 ⟨fun x => by have := x.2; have := x.1.2; omega⟩,
        Fintype.card_eq_zero_iff.2 ⟨fun c => by have := c.2; have := colLen_pos ν c.1; omega⟩]
    · rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun k => 0 < sz k)
        (fun k => sz k = v)), Fintype.card_subtype, Fintype.card_subtype, ← hfib v hv]
      have hf : (Finset.univ.filter fun k : Fin K => 0 < sz k ∧ sz k = v) =
          Finset.univ.filter fun k => sz k = v :=
        Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      rw [hf]
  obtain ⟨e, he⟩ := reorder_lemma (fun x : {k : Fin K // 0 < sz k} => sz x.1)
    (fun c : Fin (ν.rowLen 0) => ν.colLen c) hcard
  have hJ : ∀ c, sz0 ν c = sz (e.symm c).1 := by
    intro c
    have h := he (e.symm c)
    rw [e.apply_symm_apply] at h
    exact h
  refine ⟨fun c => I (e.symm c).1 ∘ Fin.cast (hJ c), fun c => ?_, ?_⟩
  · intro a b hab
    exact hI _ hab
  · unfold bideterminant
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => 0 < sz k)]
    have h1 : ∏ k : {k // ¬ 0 < sz k}, initMinor R (I k.1) (hsz k.1) = 1 :=
      Finset.prod_eq_one fun k _ => initMinor_zero R (by have := k.2; omega) _ _
    rw [h1, mul_one]
    exact (Fintype.prod_equiv e.symm _ _
      (fun c => initMinor_cast R (hJ c) (I (e.symm c).1) (hsz _) (hsz0 ν c))).symm

end PI.MSC
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.ExistsCoeffNeZeroOfMemSpan
open MvPolynomial

noncomputable section

namespace PI.MSC

open scoped MonomialOrder

variable {σ R : Type*} [CommRing R]

theorem exists_coeff_ne_zero_of_mem_span (O : MonomialOrder σ) {ι : Type*}
    (c : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => O.degree (c i))
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) {g : MvPolynomial σ R}
    (hg : g ∈ Submodule.span R (Set.range c)) (hg0 : g ≠ 0) :
    ∃ i, g.coeff (O.degree (c i)) ≠ 0 := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hg0
    rw [Finsupp.support_eq_empty.mp h, Finsupp.sum_zero_index]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image f.support (fun j => O.toSyn (O.degree (c j))) hne
  refine ⟨i, ?_⟩
  have hlt : ∀ j ∈ f.support, j ≠ i → O.toSyn (O.degree (c j)) < O.toSyn (O.degree (c i)) := by
    intro j hj hji
    refine lt_of_le_of_ne (hmax j hj) ?_
    intro heq
    exact hji (hinj (O.toSyn.injective heq))
  rw [Finsupp.sum, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have h1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
    rw [h1, mul_one]
    exact Finsupp.mem_support_iff.mp hi
  · intro j hj hji
    rw [MvPolynomial.coeff_smul, MonomialOrder.coeff_eq_zero_of_lt (hlt j hj hji), smul_zero]
  · intro h
    exact absurd hi h

theorem monomial_mem_sup (O : MonomialOrder σ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) (e : σ →₀ ℕ) (a : R) :
    monomial e a ∈ Submodule.span R (Set.range c) ⊔
      restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
  classical
  haveI := O.wf
  have key : ∀ s : O.syn, ∀ e : σ →₀ ℕ, O.toSyn e = s → ∀ a : R,
      monomial e a ∈ Submodule.span R (Set.range c) ⊔
        restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
    intro s
    induction s using WellFoundedLT.induction with
    | _ s ih =>
      intro e he a
      by_cases hmem : e ∈ Set.range fun i => O.degree (c i)
      · obtain ⟨i, rfl⟩ := hmem
        have hdecomp : monomial (O.degree (c i)) a =
            a • c i - a • (c i - monomial (O.degree (c i)) 1) := by
          rw [smul_sub, sub_sub_cancel, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hdecomp]
        refine Submodule.sub_mem _
          (Submodule.mem_sup_left (Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)))
          (Submodule.smul_mem _ a ?_)
        have hlc1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
        set q := c i - monomial (O.degree (c i)) 1 with hq
        rw [MvPolynomial.as_sum q]
        refine Submodule.sum_mem _ fun d hd => ih (O.toSyn d) ?_ d rfl _
        rw [← he]
        have hd' : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have hne : d ≠ O.degree (c i) := by
          intro hdeq
          apply hd'
          rw [hdeq, hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hlc1, sub_self]
        have hci : (c i).coeff d ≠ 0 := by
          rw [hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne),
            sub_zero] at hd'
          exact hd'
        have hle := MonomialOrder.le_degree (m := O) (MvPolynomial.mem_support_iff.mpr hci)
        exact lt_of_le_of_ne hle (fun h => hne (O.toSyn.injective h))
      · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hmem))
  exact key _ e rfl a

theorem isCompl_map_rename (O : MonomialOrder σ) {τ : Type*} {φ : σ → τ}
    (hφ : Function.Injective φ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hinj : Function.Injective fun i => O.degree (c i)) (hlc : ∀ i, O.leadingCoeff (c i) = 1) :
    IsCompl (Submodule.map (rename φ).toLinearMap (Submodule.span R (Set.range c)))
      (restrictSupport R (Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i))ᶜ) := by
  classical
  have hmapinj : Function.Injective (Finsupp.mapDomain φ : (σ →₀ ℕ) → (τ →₀ ℕ)) :=
    Finsupp.mapDomain_injective hφ
  constructor
  · rw [Submodule.disjoint_def]
    intro g hg1 hg2
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hg1
    by_contra hne
    have hh0 : h ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    obtain ⟨i, hi⟩ := exists_coeff_ne_zero_of_mem_span O c hinj hlc hh hh0
    have hsupp := (MvPolynomial.mem_restrictSupport_iff R).mp hg2
    have hmem : Finsupp.mapDomain φ (O.degree (c i)) ∈ ((rename φ).toLinearMap h).support := by
      rw [MvPolynomial.mem_support_iff]
      show AddMonoidAlgebra.coeff (rename φ h) (Finsupp.mapDomain φ (O.degree (c i))) ≠ 0
      rw [MvPolynomial.coeff_rename_mapDomain φ hφ]
      exact hi
    exact hsupp (Finset.mem_coe.mpr hmem) ⟨O.degree (c i), ⟨i, rfl⟩, rfl⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro g _
    rw [MvPolynomial.as_sum g]
    refine Submodule.sum_mem _ fun d _ => ?_
    by_cases hd : d ∈ Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i)
    · obtain ⟨e, _, rfl⟩ := hd
      have h1 := monomial_mem_sup O c hlc e (g.coeff (Finsupp.mapDomain φ e))
      rw [← MvPolynomial.rename_monomial]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
      rw [← hyz, map_add (f := _)]
      refine Submodule.add_mem_sup (Submodule.mem_map_of_mem hy) ?_
      rw [MvPolynomial.mem_restrictSupport_iff] at hz ⊢
      intro d' hd'
      have hd2 : d' ∈ (rename φ z).support := hd'
      rw [MvPolynomial.support_rename_of_injective hφ] at hd2
      obtain ⟨d'', hd'', rfl⟩ := Finset.mem_image.mp hd2
      rintro ⟨e', he', heq⟩
      exact hz (Finset.mem_coe.mpr hd'') (hmapinj heq ▸ he')
    · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hd))

end PI.MSC
end
end

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.MSC

def phi (N n : ℕ) : Fin N × Fin n → ℕ × Fin N := fun v => ((v.2 : ℕ), v.1)

theorem phi_inj (N n : ℕ) : Function.Injective (phi N n) := by
  rintro ⟨a, s⟩ ⟨a', s'⟩ h
  simp only [phi, Prod.mk.injEq] at h
  ext
  · exact congrArg Fin.val h.2
  · exact h.1

theorem rename_initMinor (R : Type) [CommRing R] (N n s : ℕ) (hs : s ≤ n) (I : Fin s ↪o Fin N) :
    rename (phi N n) (initMinor R (r := N) (n := n) (fun p => I p) hs) = PI.minorX R N s I := by
  unfold initMinor PI.minorX
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [phi, Matrix.transpose_apply, rename_X]

theorem map_bidet (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map (Int.castRingHom R) (bideterminant ℤ sz hsz I) = bideterminant R sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

def gen (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram)
    (I : ∀ c : Fin (ν.rowLen 0), Fin (ν.colLen c) ↪o Fin N) :
    MvPolynomial (Fin N × Fin (ν.colLen 0)) R :=
  bideterminant R (sz0 ν) (hsz0 ν) fun c => I c

theorem nablaSpan_eq (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram) :
    PI.nablaSpan R N ν = Submodule.map (rename (phi N (ν.colLen 0))).toLinearMap
      (Submodule.span R (Set.range (gen R N ν))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  unfold PI.nablaSpan
  congr 1
  apply congrArg Set.range
  funext I
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, gen, bideterminant, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact (rename_initMinor R N (ν.colLen 0) (sz0 ν c) (hsz0 ν c) (I c)).symm

theorem span_map_le {σ : Type*} (R : Type) [CommRing R] {A B : Set (MvPolynomial σ ℤ)}
    (h : A ⊆ Submodule.span ℤ B) :
    Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' A) ≤
      Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' B) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have := h ha
  clear ha
  induction this using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul R]
    exact Submodule.smul_mem _ _ hx

theorem minorSpanCompl : PI.MinorSpanCompl := by
  intro R _ N ν
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨⊤, ?_⟩
    have h0 : PI.nablaSpan R N ν = ⊥ :=
      eq_bot_iff.mpr fun x _ => (Submodule.mem_bot R).mpr (Subsingleton.elim x 0)
    rw [h0]
    exact isCompl_bot_top
  set n := ν.colLen 0
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis ℤ N n (nuR ν)

  have hZ : Submodule.span ℤ (Set.range (gen ℤ N ν)) = Submodule.span ℤ (Set.range b) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨I, rfl⟩
      rw [SetLike.mem_coe, hspan]
      have := bideterminantMem ℤ N n (ν.rowLen 0) (sz0 ν) (hsz0 ν) fun c => I c
      rwa [shapeColumnDegree_columnSizes] at this
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      obtain ⟨K, sz, hsz, I, hsh, hI, hbm⟩ := (hb m).2.2
      rw [SetLike.mem_coe, hbm]
      obtain ⟨J, hJ, heq⟩ := reorder ℤ ν N sz hsz I hI hsh
      rw [heq]
      exact Submodule.subset_span ⟨fun c => OrderEmbedding.ofStrictMono (J c) (hJ c), rfl⟩
  set c : ssIdx N n (nuR ν) → MvPolynomial (Fin N × Fin n) R :=
    fun m => MvPolynomial.map (Int.castRingHom R) (b m) with hcdef
  have hT : Submodule.span R (Set.range (gen R N ν)) = Submodule.span R (Set.range c) := by
    have e1 : Set.range (gen R N ν) = MvPolynomial.map (Int.castRingHom R) '' Set.range (gen ℤ N ν) := by
      rw [← Set.range_comp]
      congr 1
      funext I
      exact (map_bidet R (sz0 ν) (hsz0 ν) (fun c => I c)).symm
    have e2 : Set.range c = MvPolynomial.map (Int.castRingHom R) '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, e2]
    apply le_antisymm
    · exact span_map_le R (by rw [← hZ]; exact Submodule.subset_span)
    · exact span_map_le R (by rw [hZ]; exact Submodule.subset_span)
  have hdl : ∀ m, (colLex N n).degree (c m) = m.1 ∧ (colLex N n).leadingCoeff (c m) = 1 := by
    intro m
    obtain ⟨K, sz, hsz, I, _, hI, hbm⟩ := (hb m).2.2
    have hR := column_lex_bideterminant R N n K sz hsz I hI
    have hZd := column_lex_bideterminant ℤ N n K sz hsz I hI
    have hdeg := (hb m).1
    rw [hbm] at hdeg
    simp only [hcdef, hbm, map_bidet]
    exact ⟨hR.1.trans (hZd.1.symm.trans hdeg), hR.2⟩
  have hinj : Function.Injective fun m => (colLex N n).degree (c m) := by
    intro m m' h
    apply Subtype.ext
    simpa [(hdl m).1, (hdl m').1] using h
  rw [nablaSpan_eq, hT]
  exact ⟨_, isCompl_map_rename (colLex N n) (phi_inj N n) c hinj fun m => (hdl m).2⟩

end PI.MSC
end
end

theorem minor_span_complement : PI.MinorSpanCompl := PI.MSC.minorSpanCompl
