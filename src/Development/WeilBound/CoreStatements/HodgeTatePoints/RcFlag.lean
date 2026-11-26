module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Invres
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

lemma unimod {S V ι : Type} [CommRing S] [CommRing V] [Algebra S V] [Fintype ι] (f : ι → V)
    (b : ι → S) (h1 : 1 = ∑ j, b j • f j)
    (hmul : ∀ i j, f j * f i ∈ Submodule.span S (Set.range f)) :
    ∃ e : ι → S, algebraMap S V (∑ j, e j * b j) = 1 := by
  let A : Submodule S V := Submodule.span S (Set.range f)
  let J : Ideal S := Ideal.span (Set.range b)
  have hJ : A ≤ J • A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, b j • (f j * f i) := by
      conv_lhs => rw [← one_mul (f i), h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul
      (Ideal.subset_span ⟨j, rfl⟩) (hmul i j)
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J A
    (Submodule.fg_span (Set.finite_range f)) hJ
  have h1A : (1 : V) ∈ A := by
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => A.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr := hr0 1 h1A
  rw [Algebra.smul_def, mul_one] at hr
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (J.neg_mem hr1)
  refine ⟨e, ?_⟩
  simp only [smul_eq_mul] at he
  rw [he, neg_sub, map_sub, hr, map_one, sub_zero]

theorem invres : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ K K' : AddSubgroup N, K ≤ K' → ∀ g ∈ AA.carrier, (∀ x ∈ K', ∀ k ∈ K, g (x + k) = g x) → ∃ g' ∈ invFun AA.carrier K, ∀ x ∈ K', g' x = g x := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA K K' _ g hg hinv
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨f, hf, hfree⟩, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  have hB : ∀ b ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K), b ∈ invFun AA.carrier K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q ((x + k : N) : N ⧸ K) = q (x : N ⧸ K)
    rw [QuotientAddGroup.mk_add_of_mem x hk]
  have hdec : ∀ a ∈ AA.carrier, ∃ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) ∧
      a = ∑ j, b j * f j := by
    intro a ha
    obtain ⟨b, ⟨hb, hab⟩, -⟩ := hfree a ha
    exact ⟨b, fun j => hB _ (hb j), hab⟩
  let S : Subalgebra R (N → C) := (invFun AA.carrier K).toSubalgebra ⟨AA.one_mem, fun _ _ _ => rfl⟩
    (fun x y hx hy => ⟨AA.mul_mem _ _ hx.1 hy.1, fun z k hk => by
      simp only [Pi.mul_apply, hx.2 z k hk, hy.2 z k hk]⟩)
  let A : Submodule S (N → C) := Submodule.span S (Set.range f)
  have hA : ∀ a ∈ AA.carrier, a ∈ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hdec a ha
    exact Submodule.sum_mem _ fun j _ =>
      A.smul_mem (⟨b j, hb j⟩ : S) (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb, h1⟩ := hdec 1 AA.one_mem
  obtain ⟨e, he⟩ := unimod f (fun j => (⟨b j, hb j⟩ : S)) h1
    (fun i j => hA _ (AA.mul_mem _ _ (hf j) (hf i)))
  have he' : ∀ x, ∑ j, (e j : N → C) x * b j x = 1 := by
    intro x
    have : ((∑ j, e j * (⟨b j, hb j⟩ : S) : S) : N → C) x = 1 := congrFun he x
    simpa using this
  obtain ⟨c, hc, hgc⟩ := hdec g hg
  refine ⟨((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C), (∑ j, e j * (⟨c j, hc j⟩ : S) : S).2,
    fun x hx => ?_⟩
  let ρ : (N → C) →ₗ[C] (K → C) := LinearMap.funLeft C C fun k : K => x + (k : N)
  have hρ : ∀ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) →
      ρ (∑ j, b j * f j) = ∑ j, b j x • ρ (f j) := by
    intro b hb
    funext k
    simp only [ρ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [(hb j).2 x k k.2]
  have hli : LinearIndependent C fun j => ρ (f j) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hsurj : Function.Surjective ρ :=
        LinearMap.funLeft_surjective_of_injective _ _ _
          (fun k k' h => Subtype.ext (add_left_cancel h))
      rw [← LinearMap.range_eq_top.2 hsurj, ← Submodule.map_top, ← span_top_of_isLat (C := C) AA.lat,
        Submodule.map_span_le]
      intro a ha
      obtain ⟨b', hb', rfl⟩ := hdec a ha
      rw [hρ b' hb']
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp
  have hkey : ∀ j, c j x = g x * b j x := by
    have h2 : ∑ j, (c j x - g x * b j x) • ρ (f j) = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hρ c hc, ← hρ b hb, ← hgc, ← h1]
      funext k
      simp [ρ, LinearMap.funLeft_apply, hinv x hx k k.2]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  have : ((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C) x = ∑ j, (e j : N → C) x * c j x := by
    simp
  rw [this]
  simp only [hkey]
  calc ∑ j, (e j : N → C) x * (g x * b j x) = g x * ∑ j, (e j : N → C) x * b j x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = g x := by rw [he', mul_one]

end PositivityTheory.HtPt.Rc
end
end

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
variable {N Q : Type} [AddCommGroup N] [AddCommGroup Q] [Module F N] [Module F Q]

lemma stepOrder_eq (M : Submodule R (N → C)) (ψ : N →ₗ[F] Q) (hψ : Function.Surjective ψ)
    (t : N) :
    stepOrder M (LinearMap.ker ψ) t = (M.comap (LinearMap.funLeft R C ψ)).map
      (LinearMap.funLeft R C (LinearMap.toSpanSingleton F Q (ψ t))) := by
  rw [stepOrder, invFun_eq M ψ.toAddMonoidHom hψ _ (fun x => by simp), ← Submodule.map_comp]
  congr 1
  ext g a
  simp [LinearMap.funLeft]

lemma span_inj {t : Q} (ht : t ≠ 0) :
    Function.Injective (LinearMap.toSpanSingleton F Q t) := by
  intro a b h
  exact smul_left_injective F ht (by simpa using h)

lemma flagSub_succ {n : ℕ} (b : Module.Basis (Fin n) F N) (i : Fin n) :
    flagSub b ((i : ℕ) + 1) = Submodule.span F {b i} ⊔ flagSub b i := by
  have hs : {j : Fin n | (j : ℕ) < (i : ℕ) + 1} = insert i {j : Fin n | (j : ℕ) < (i : ℕ)} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagSub
  rw [hs, Set.image_insert_eq, Submodule.span_insert]

lemma notMem_flagSub {n : ℕ} (b : Module.Basis (Fin n) F N) (i : Fin n) :
    b i ∉ flagSub b i :=
  b.linearIndependent.notMem_span_image (by simp)

variable {v : Valuation C NNReal}

lemma colen_trivial [IsAlgClosed C] [CharZero C] (hv : v.Integers R) {T : Type} [AddCommGroup T]
    [Fintype T] [DecidableEq T] [Subsingleton T] (A : HopfOrder (C := C) R T) (c : NNReal)
    (hc : HasColen R v A.carrier c) : c = 1 := by
  obtain ⟨B, hB, rfl⟩ := hc
  rw [Matrix.det_eq_elem_of_subsingleton B 0]
  have hr : Set.range (fun (j x : T) => B x j) = {fun x => B x 0} := by
    ext g
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j 0]
    · rintro rfl
      exact ⟨0, rfl⟩
  have h1 : (1 : T → C) ∈ Submodule.span R {fun x => B x 0} := by
    rw [← hr, ← hB]
    exact A.one_mem
  have hmem : (fun x => B x 0) ∈ A.carrier := by
    rw [hB, hr]
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.mem_span_singleton] at h1
  obtain ⟨r, hr1⟩ := h1
  obtain ⟨s, hs⟩ := A.le_int hmem 0
  have e1 := congrFun hr1 0
  simp only [Pi.smul_apply, Pi.one_apply, Algebra.smul_def] at e1
  have e2 := congrArg v e1
  rw [map_mul, map_one] at e2
  have hr' := hv.map_le_one r
  have hs' : v (B 0 0) ≤ 1 := by
    have h3 : (algebraMap R C) s = B 0 0 := hs
    rw [← h3]
    exact hv.map_le_one s
  refine le_antisymm hs' ?_
  by_contra hlt
  push_neg at hlt
  have h0 : (0 : NNReal) ≤ v (B 0 0) := by positivity
  have := mul_lt_one_of_nonneg_of_lt_one_right hr' h0 hlt
  rw [e2] at this
  exact lt_irrefl _ this

lemma flag_ind [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype F] [DecidableEq F]
    [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N) {n : ℕ}
    (b : Module.Basis (Fin n) F N) (cs : Fin n → NNReal)
    (hcs : ∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) :
    ∀ (d i : ℕ), i + d = n → ∀ (Q : Type) [AddCommGroup Q] [Module F Q] [Fintype Q]
      [DecidableEq Q] (ψ : N →ₗ[F] Q), Function.Surjective ψ → LinearMap.ker ψ = flagSub b i →
      ∀ c, HasColen R v (AA.carrier.comap (LinearMap.funLeft R C ψ)) c →
        c ^ Fintype.card F =
          (∏ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)), cs j) ^ Fintype.card Q := by
  classical
  intro d
  induction d with
  | zero =>
    intro i hi Q _ _ _ _ ψ hψ hker c hc
    rw [Nat.add_zero] at hi
    have htop : LinearMap.ker ψ = ⊤ := by
      rw [hker, hi]
      unfold flagSub
      have hu : {j : Fin n | (j : ℕ) < n} = Set.univ := by
        ext j
        simp [j.isLt]
      rw [hu, Set.image_univ, b.span_eq]
    haveI : Subsingleton Q := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := hψ x
      obtain ⟨y', rfl⟩ := hψ y
      have hx : x' ∈ LinearMap.ker ψ := by
        rw [htop]
        trivial
      have hy : y' ∈ LinearMap.ker ψ := by
        rw [htop]
        trivial
      rw [LinearMap.mem_ker] at hx hy
      rw [hx, hy]
    obtain ⟨AQ, hAQ⟩ := exists_quo hv AA ψ.toAddMonoidHom hψ
    have hc1 : c = 1 := colen_trivial hv AQ c (by rw [hAQ]; exact hc)
    have he : Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)) = ∅ := by
      ext j
      have := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hc1, he, Finset.prod_empty, one_pow, one_pow]
  | succ d ih =>
    intro i hi Q _ _ _ _ ψ hψ hker c hc
    have hin : i < n := by omega
    let ii : Fin n := ⟨i, hin⟩
    have hii : (ii : ℕ) = i := rfl
    have hbi : ψ (b ii) ≠ 0 := by
      intro h0
      apply notMem_flagSub b ii
      rw [hii, ← hker]
      exact h0
    let L : Submodule F Q := Submodule.span F {ψ (b ii)}
    haveI : Fintype (Q ⧸ L) := Fintype.ofFinite _
    let ψ' : N →ₗ[F] Q ⧸ L := L.mkQ.comp ψ
    have hψ' : Function.Surjective ψ' := L.mkQ_surjective.comp hψ
    have hker' : LinearMap.ker ψ' = flagSub b (i + 1) := by
      rw [LinearMap.ker_comp, L.ker_mkQ]
      have hL : L = Submodule.map ψ (Submodule.span F {b ii}) := by
        rw [Submodule.map_span, Set.image_singleton]
      rw [hL, Submodule.comap_map_eq, hker, ← hii, flagSub_succ b ii]
    obtain ⟨AQ, hAQ⟩ := exists_quo hv AA ψ.toAddMonoidHom hψ
    obtain ⟨AQ', hAQ'⟩ := exists_quo hv AA ψ'.toAddMonoidHom hψ'
    obtain ⟨cQ, hcQ⟩ := ReciprocityTheory.PGsh.Up.hasColen_of_lat v AQ'.lat
    rw [hAQ'] at hcQ
    have ih' := ih (i + 1) (by omega) (Q ⧸ L) ψ' hψ' hker' cQ hcQ
    have hst : stepOrder AA.carrier (flagSub b i) (b ii) = (AA.carrier.comap
        (LinearMap.funLeft R C ψ)).map
        (LinearMap.funLeft R C (LinearMap.toSpanSingleton F Q (ψ (b ii)))) := by
      rw [← hker]
      exact stepOrder_eq AA.carrier ψ hψ (b ii)
    have h3 : HasColen R v (stepOrder AA.carrier (flagSub b i) (b ii)) (cs ii) := hcs ii
    rw [hst] at h3
    have hrange : (LinearMap.toSpanSingleton F Q (ψ (b ii))).toAddMonoidHom.range =
        (L.mkQ.toAddMonoidHom).ker := by
      ext x
      simp [L, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    have hses := colen_ses hv AQ (LinearMap.toSpanSingleton F Q (ψ (b ii))).toAddMonoidHom
      (span_inj hbi) L.mkQ.toAddMonoidHom L.mkQ_surjective hrange c cQ (cs ii)
      (by rw [hAQ]; exact hc)
      (by
        have hcm : Submodule.comap (LinearMap.funLeft R C ⇑L.mkQ.toAddMonoidHom) AQ.carrier =
            Submodule.comap (LinearMap.funLeft R C ⇑ψ') AA.carrier := by
          rw [hAQ]
          ext h
          rfl
        rw [hcm]
        exact hcQ)
      (by rw [hAQ]; exact h3)
    have hcard : Fintype.card Q = Fintype.card (Q ⧸ L) * Fintype.card F := by
      have h1 := Submodule.card_eq_card_quotient_mul_card L
      have h2 : Nat.card L = Nat.card F :=
        Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F Q _ hbi).toEquiv.symm
      rw [h2] at h1
      simp only [Nat.card_eq_fintype_card] at h1
      rw [h1, mul_comm]
    have hprod : ∏ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)), cs j =
        cs ii * ∏ j ∈ Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ)), cs j := by
      have hs : Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)) =
          insert ii (Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, hii]
        omega
      rw [hs, Finset.prod_insert]
      simp [hii]
    rw [hses, hprod, hcard, ih']
    ring

end Gen

theorem step : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable (F := F) S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst K t ht
  classical
  haveI : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  have hne : K.mkQ t ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using ht
  have heq := stepOrder_eq AA.carrier K.mkQ hsurj t
  rw [K.ker_mkQ] at heq
  obtain ⟨AQ, hAQ⟩ := exists_quo hv AA K.mkQ.toAddMonoidHom hsurj
  obtain ⟨S, hS⟩ := exists_res hv AQ
    (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t)).toAddMonoidHom (span_inj hne)
  refine ⟨⟨S, ?_, ?_⟩, ?_⟩
  · rw [hS, hAQ, heq]
    rfl
  · rw [hS, hAQ]
    intro a h hh
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
    refine Submodule.mem_map.mpr ⟨fun x => g (a • x), ?_, ?_⟩
    · have hg' : (fun x => g (K.mkQ x)) ∈ AA.carrier := hg
      change (fun x => g (a • K.mkQ x)) ∈ AA.carrier
      simpa only [map_smul] using hst a _ hg'
    · funext x
      change g (a • LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) x) =
        g (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) (a • x))
      rw [map_smul]
  · unfold stepOrder stepOrderRes
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
      exact ⟨g, hg.1, fun a k hk => hg.2 _ _ hk⟩
    · rintro ⟨g, hg, hgh⟩
      obtain ⟨g', hg', hg'e⟩ := invres p C v R hv hp N AA K.toAddSubgroup
        (Submodule.span F {t} ⊔ K).toAddSubgroup
        (by
          intro x hx
          exact Submodule.mem_sup_right hx) g hg
        (by
          intro x hx k hk
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [add_assoc, hgh a _ (K.add_mem hz hk), hgh a z hz])
      refine Submodule.mem_map.mpr ⟨g', hg', ?_⟩
      funext a
      show g' (a • t) = h a
      rw [hg'e (a • t) (Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩))]
      simpa using hgh a 0 K.zero_mem

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst n b cs cN hcs hN
  have h0 : LinearMap.ker (LinearMap.id : N →ₗ[F] N) = flagSub b 0 := by
    rw [LinearMap.ker_id]
    unfold flagSub
    simp
  have hid : HasColen R v
      (AA.carrier.comap (LinearMap.funLeft R C (LinearMap.id : N →ₗ[F] N))) cN := by
    have he : AA.carrier.comap (LinearMap.funLeft R C (LinearMap.id : N →ₗ[F] N)) = AA.carrier := by
      ext h
      rfl
    rw [he]
    exact hN
  have key := flag_ind hv AA b cs hcs n 0 (by omega) N LinearMap.id (fun x => ⟨x, rfl⟩) h0 cN hid
  have hu : Finset.univ.filter (fun j : Fin n => 0 ≤ (j : ℕ)) = Finset.univ := by
    ext j
    simp
  rw [hu] at key
  rw [← hf]
  exact key

end PositivityTheory.HtPt.Rc
