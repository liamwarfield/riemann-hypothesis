module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.FinrankAdjoinPowLe
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.FieldGen
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.MemPw
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module

def Tw (k : Type*) (_p _c : ℕ) : Type _ := k

variable {k : Type*} [Field k]

instance (p c : ℕ) : Field (Tw k p c) := inferInstanceAs (Field k)

instance (p c : ℕ) [Fact p.Prime] [CharP k p] : Algebra k (Tw k p c) :=
  RingHom.toAlgebra (show k →+* Tw k p c from iterateFrobenius k p c)

def Pw (k B : Type*) [Field k] [CommRing B] [Algebra k B] (q : ℕ) : Subalgebra k B :=
  Algebra.adjoin k (Set.range fun b : B => b ^ q)

theorem mem_Pw {B : Type*} [CommRing B] [Algebra k B] (p c : ℕ) [Fact p.Prime] [CharP k p]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) {b : B} :
    b ∈ Pw k B (p ^ c) ↔ ∃ w : B, w ^ (p ^ c) = b := by
  unfold Pw
  constructor
  · intro hb
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact ⟨b, Subsingleton.elim _ _⟩
    have : CharP B p := charP_of_injective_algebraMap' k p
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    | algebraMap r => exact hroot r
    | add x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ + w₂, add_pow_char_pow w₁ w₂ p c⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ * w₂, mul_pow w₁ w₂ _⟩
  · rintro ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w, rfl⟩

theorem fc {B : Type*} [CommRing B] [Algebra k B] [FiniteDimensional k B] [IsReduced B]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) :
    finrank k B = finrank k (Tw k p c) * finrank k (Pw k B (p ^ c)) := by
  classical
  letI iT : Module (Tw k p c) (Pw k B (p ^ c)) := inferInstanceAs (Module k (Pw k B (p ^ c)))
  have hadd : ∀ x y : B, (x + y) ^ (p ^ c) = x ^ (p ^ c) + y ^ (p ^ c) := by
    intro x y
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact Subsingleton.elim _ _
    · haveI := charP_of_injective_algebraMap (algebraMap k B).injective p
      exact add_pow_char_pow x y p c
  have hmem : ∀ x : B, x ^ (p ^ c) ∈ Pw k B (p ^ c) := fun x =>
    Algebra.subset_adjoin ⟨x, rfl⟩
  let f : B →ₗ[k] RestrictScalars k (Tw k p c) (Pw k B (p ^ c)) :=
    { toFun := fun x => (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c))
      map_add' := fun x y => by
        apply Subtype.ext
        exact hadd x y
      map_smul' := fun a x => by
        apply Subtype.ext
        show (a • x) ^ (p ^ c) = ((algebraMap k (Tw k p c) a) • (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c)) : Pw k B (p ^ c)).1
        rw [smul_pow]
        rfl }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h0 : x ^ (p ^ c) = 0 := congrArg (fun z : Pw k B (p ^ c) => (z : B)) hx
    exact IsReduced.eq_zero x ⟨_, h0⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).1 (show (Pw k B (p ^ c)) from y).2
    exact ⟨w, Subtype.ext hw⟩
  letI : Module (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    RestrictScalars.moduleOrig k (Tw k p c) (Pw k B (p ^ c))
  haveI : Module.Free (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    show Module.Free k (Pw k B (p ^ c)) from inferInstance
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [e.finrank_eq, ← Module.finrank_mul_finrank k (Tw k p c)
    (RestrictScalars k (Tw k p c) (Pw k B (p ^ c)))]
  rfl

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.CompIterateFrobenius
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial IntermediateField

theorem fl_step {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E))
    (L : IntermediateField F E) {x : E} (hx : x ∉ L) :
    finrank L (adjoin L {x}) = p := by
  obtain ⟨a, ha⟩ := h x
  have hxp : x ^ p ∈ L := ha ▸ L.algebraMap_mem a
  set b : L := ⟨x ^ p, hxp⟩ with hb
  have hirr : Irreducible (X ^ p - C b) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro y hy
    apply hx
    have h1 : (y : E) ^ p = x ^ p := by
      have := congrArg (fun z : L => (z : E)) hy
      simpa [hb] using this
    have h2 : (y : E) = x := frobenius_inj E p (by simpa [frobenius_def] using h1)
    exact h2 ▸ y.2
  have haev : aeval x (X ^ p - C b) = 0 := by
    simp [hb]
  have hmon : (X ^ p - C b).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have hmin : X ^ p - C b = minpoly L x := minpoly.eq_of_irreducible_of_monic hirr haev hmon
  have hint : IsIntegral L x := ⟨X ^ p - C b, hmon, by simpa [aeval_def] using haev⟩
  rw [adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C _]

theorem fl_greedy {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [hp : Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∀ (N : ℕ) (L : IntermediateField F E), L.relfinrank ⊤ = N →
      ∃ n, L.relfinrank ⊤ = p ^ n ∧ ∃ α : Fin n → E, L ⊔ adjoin F (Set.range α) = ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro L hL
  by_cases hT : L = ⊤
  · subst hT
    exact ⟨0, by simp [relfinrank_self], Fin.elim0, top_sup_eq _⟩
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hT)
  set L' : IntermediateField F E := (adjoin L ({x} : Set E)).restrictScalars F with hL'
  have hsup : L' = L ⊔ adjoin F ({x} : Set E) := by rw [hL', restrictScalars_adjoin_eq_sup]
  have hle : L ≤ L' := hsup ▸ le_sup_left
  have hdeg : L.relfinrank L' = p := by
    rw [relfinrank_eq_finrank_of_le hle]
    have : extendScalars hle = adjoin L ({x} : Set E) :=
      restrictScalars_injective F (by rw [extendScalars_restrictScalars])
    rw [this, fl_step p h L hx]
  have hmul := relfinrank_mul_relfinrank hle (le_top : L' ≤ ⊤)
  have hpos : 0 < L.relfinrank ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  have hlt : L'.relfinrank ⊤ < N := by
    rw [← hL, ← hmul, hdeg]
    have h2 := hp.out.two_le
    have : 0 < L'.relfinrank ⊤ := by
      rcases Nat.eq_zero_or_pos (L'.relfinrank ⊤) with h0 | h0
      · rw [← hmul, h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    nlinarith
  obtain ⟨m, hm, β, hβ⟩ := ih _ hlt L' rfl
  refine ⟨m + 1, ?_, Fin.cons x β, ?_⟩
  · rw [← hmul, hdeg, hm, pow_succ']
  · rw [Fin.range_cons, Set.insert_eq, adjoin_union, ← sup_assoc, ← hsup, hβ]

theorem fl_main {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∃ n, finrank F E = p ^ n ∧ ∃ α : Fin n → E, adjoin F (Set.range α) = ⊤ := by
  obtain ⟨n, hn, α, hα⟩ := fl_greedy p h _ ⊥ rfl
  refine ⟨n, ?_, α, ?_⟩
  · rw [← hn, relfinrank_bot_left, finrank_top']
  · rwa [bot_sup_eq] at hα

def Pj (E : Type*) [Field E] (p : ℕ) [Fact p.Prime] [CharP E p] (j : ℕ) : Subfield E :=
  (iterateFrobenius E p j).fieldRange

section Frob

variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]

theorem mem_Pj {j : ℕ} {y : E} : y ∈ Pj E p j ↔ ∃ x : E, x ^ p ^ j = y := by
  simp [Pj, RingHom.mem_fieldRange, iterateFrobenius_def]

theorem Pj_zero : Pj E p 0 = ⊤ :=
  eq_top_iff.2 fun y _ => (mem_Pj p).2 ⟨y, by simp⟩

theorem Pj_succ_le (j : ℕ) : Pj E p (j + 1) ≤ Pj E p j := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
  exact (mem_Pj p).2 ⟨x ^ p, by rw [← pow_mul, pow_succ']⟩

theorem comp_iterateFrobenius (j : ℕ) :
    (iterateFrobenius E p j).comp (iterateFrobenius E p 1) = iterateFrobenius E p (j + 1) := by
  ext x
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]

theorem map_Pj_one (j : ℕ) : (Pj E p 1).map (iterateFrobenius E p j) = Pj E p (j + 1) := by
  rw [Pj, RingHom.map_fieldRange, comp_iterateFrobenius, Pj]

theorem map_top_Pj (j : ℕ) : (⊤ : Subfield E).map (iterateFrobenius E p j) = Pj E p j :=
  (RingHom.fieldRange_eq_map _).symm

theorem relfinrank_Pj_succ (j : ℕ) :
    (Pj E p (j + 1)).relfinrank (Pj E p j) = (Pj E p 1).relfinrank ⊤ := by
  rw [← map_Pj_one p j, ← map_top_Pj p j, Subfield.relfinrank_map_map]

theorem relfinrank_Pj (j : ℕ) :
    (Pj E p j).relfinrank ⊤ = ((Pj E p 1).relfinrank ⊤) ^ j := by
  induction j with
  | zero => rw [pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
  | succ j ih =>
    rw [← Subfield.relfinrank_mul_relfinrank (Pj_succ_le p j) le_top, relfinrank_Pj_succ, ih,
      pow_succ']

theorem closure_Pj_eq_top {S : Set E} (hS : Subfield.closure ((Pj E p 1 : Set E) ∪ S) = ⊤)
    (j : ℕ) : Subfield.closure ((Pj E p j : Set E) ∪ S) = ⊤ := by
  have key : ∀ i, Pj E p i ≤ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S) := by
    intro i
    rw [← map_top_Pj p i, ← hS, Subfield.map_le_iff_le_comap, Subfield.closure_le]
    rintro y (hy | hy)
    · change y ∈ Pj E p 1 at hy
      obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
      rw [SetLike.mem_coe, Subfield.mem_comap]
      apply Subfield.subset_closure
      left
      exact (mem_Pj p).2 ⟨x, by rw [iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]⟩
    · rw [SetLike.mem_coe, Subfield.mem_comap, iterateFrobenius_def]
      exact pow_mem (Subfield.subset_closure (Set.mem_union_right _ hy) :
        y ∈ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S)) _
  induction j with
  | zero =>
    rw [Pj_zero]
    exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  | succ j ih =>
    refine eq_top_iff.2 (ih ▸ Subfield.closure_le.2 (Set.union_subset (key j) ?_))
    exact fun y hy => Subfield.subset_closure (Or.inr hy)

theorem fl_frob (c : ℕ) (hc : 0 < c) (hfin : (Pj E p c).relfinrank ⊤ ≠ 0) :
    ∃ n, (Pj E p c).relfinrank ⊤ = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ := by
  have h1 : (Pj E p 1).relfinrank ⊤ ≠ 0 := by
    intro h0
    apply hfin
    rw [relfinrank_Pj, h0, zero_pow hc.ne']
  haveI : FiniteDimensional (Pj E p 1) E :=
    Module.finite_of_finrank_pos (by rw [← Subfield.relfinrank_top_right]; exact Nat.pos_of_ne_zero h1)
  obtain ⟨n, hn, α, hα⟩ := fl_main (F := Pj E p 1) (E := E) p
    (fun x => ⟨⟨x ^ p, (mem_Pj p).2 ⟨x, by rw [pow_one]⟩⟩, rfl⟩)
  refine ⟨n, ?_, α, closure_Pj_eq_top p ?_ c⟩
  · rw [relfinrank_Pj, Subfield.relfinrank_top_right, hn, ← pow_mul, ← pow_mul, mul_comm]
  · have := congrArg IntermediateField.toSubfield hα
    rw [adjoin_toSubfield, top_toSubfield] at this
    have hr : Set.range (algebraMap (Pj E p 1) E) = (Pj E p 1 : Set E) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rwa [hr] at this

end Frob

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem fl_deg {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [CharP E p]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    (Pj E p c).relfinrank ⊤ = finrank k (Tw k p c) := by
  set f := algebraMap k E with hf
  set Fr := iterateFrobenius E p c with hFr
  set K : Subfield E := f.fieldRange with hK
  set Kq : Subfield E := (Fr.comp f).fieldRange with hKq
  have hmapK : K.map Fr = Kq := RingHom.map_fieldRange _ _
  have hmapT : (⊤ : Subfield E).map Fr = Pj E p c := map_top_Pj p c
  have h3 : Kq.relfinrank (Pj E p c) = K.relfinrank ⊤ := by
    rw [← hmapK, ← hmapT, Subfield.relfinrank_map_map]
  have h4 : Kq ≤ K := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    exact RingHom.mem_fieldRange.2 ⟨a ^ p ^ c, by rw [RingHom.comp_apply, hFr, iterateFrobenius_def, map_pow]⟩
  have h5 : K ≤ Pj E p c := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    obtain ⟨w, hw⟩ := hroot a
    exact (mem_Pj p).2 ⟨w, hw⟩
  have hA := Subfield.relfinrank_mul_relfinrank h4 (le_top : K ≤ ⊤)
  have hB := Subfield.relfinrank_mul_relfinrank (h4.trans h5) (le_top : Pj E p c ≤ ⊤)
  have hKtop : K.relfinrank ⊤ = finrank k E := by
    have := IntermediateField.relfinrank_bot_left (⊤ : IntermediateField k E)
    rw [IntermediateField.finrank_top'] at this
    rw [← this, IntermediateField.relfinrank, IntermediateField.bot_toSubfield,
      IntermediateField.top_toSubfield]
  have hpos : 0 < K.relfinrank ⊤ := hKtop ▸ Module.finrank_pos
  have h9 : Kq.relfinrank K = finrank k (Tw k p c) := by
    rw [Subfield.relfinrank_eq_finrank_of_le h4]
    symm
    refine Algebra.finrank_eq_of_equiv_equiv (Fr.comp f).rangeRestrictFieldEquiv
      (f.rangeRestrictFieldEquiv.trans
        (RingEquiv.subfieldCongr (Subfield.extendScalars_toSubfield h4).symm)) ?_
    ext a
    show (((Fr.comp f).rangeRestrictFieldEquiv a : Kq) : E) = f (iterateFrobenius k p c a)
    rw [RingHom.rangeRestrictFieldEquiv_apply_coe, RingHom.comp_apply, hFr, iterateFrobenius_def,
      iterateFrobenius_def, map_pow]
  rw [h3] at hB
  rw [← h9]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hB, ← hA, mul_comm]

theorem fieldGen {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    ∃ n : ℕ, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Algebra.adjoin k (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have hdeg := fl_deg p c hroot
  suffices H : ∃ n, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ by
    obtain ⟨n, hn, α, hα⟩ := H
    refine ⟨n, hn, α, ?_⟩
    have hadj : IntermediateField.adjoin k
        (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
      apply IntermediateField.toSubfield_injective
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield, eq_top_iff, ← hα]
      apply Subfield.closure_mono
      apply Set.union_subset
      · intro y hy
        exact Or.inr (Or.inl ((mem_Pj p).1 hy))
      · intro y hy
        exact Or.inr (Or.inr hy)
    rw [← IntermediateField.adjoin_toSubalgebra, hadj, IntermediateField.top_toSubalgebra]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨0, ?_, Fin.elim0, ?_⟩
    · rw [← hdeg, pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
    · rw [Pj_zero]
      exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  · have hfin : (Pj E p c).relfinrank ⊤ ≠ 0 := by
      rw [hdeg]
      exact Module.finrank_pos.ne'
    obtain ⟨n, hn, α, hα⟩ := fl_frob p c hc hfin
    exact ⟨n, hdeg ▸ hn, α, hα⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

private theorem finrank_adjoin_pow_le {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (T : Subalgebra k R) (q n : ℕ) (hq : 0 < q) (L : Fin n → R)
    (hL : ∀ i, L i ^ q ∈ T) :
    finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤ q ^ n * finrank k T := by
  classical
  let G : (Fin n → ℕ) → R := fun e => ∏ i, L i ^ e i
  let Φ : ((Fin n → Fin q) → T) →ₗ[k] R :=
    ∑ e : Fin n → Fin q, (LinearMap.mulRight k (G fun i => (e i : ℕ))) ∘ₗ T.val.toLinearMap ∘ₗ
      LinearMap.proj e
  have hΦ : ∀ f, Φ f = ∑ e : Fin n → Fin q, (f e : R) * G (fun i => (e i : ℕ)) := by
    intro f; simp [Φ, LinearMap.sum_apply]
  have hsingle : ∀ t ∈ T, ∀ e : Fin n → Fin q, t * G (fun i => (e i : ℕ)) ∈ LinearMap.range Φ := by
    intro t ht e
    refine ⟨Pi.single e ⟨t, ht⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hA : ∀ t ∈ T, ∀ e : Fin n → ℕ, t * G e ∈ LinearMap.range Φ := by
    intro t ht e
    have hG : G e = (∏ i, (L i ^ q) ^ (e i / q)) *
        G (fun i => ((⟨e i % q, Nat.mod_lt _ hq⟩ : Fin q) : ℕ)) := by
      simp only [G]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hG, ← mul_assoc]
    exact hsingle _ (T.mul_mem ht (T.prod_mem fun i _ => T.pow_mem (hL i) _)) _
  have hLmul : ∀ i e, L i * G e = G (e + Pi.single i 1) := by
    intro i e
    simp only [G, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hclosed : ∀ y ∈ Algebra.adjoin k ((T : Set R) ∪ Set.range L),
      ∀ m ∈ LinearMap.range Φ, y * m ∈ LinearMap.range Φ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rintro m ⟨f, rfl⟩
      rw [hΦ, Finset.mul_sum]
      refine Submodule.sum_mem _ fun e _ => ?_
      rcases hx with hx | ⟨i, rfl⟩
      · rw [← mul_assoc]; exact hsingle _ (T.mul_mem hx (f e).2) e
      · rw [mul_left_comm, hLmul]; exact hA _ (f e).2 _
    | algebraMap a =>
      intro m hm; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hm
    | add x y _ _ hx hy =>
      intro m hm; rw [add_mul]; exact add_mem (hx m hm) (hy m hm)
    | mul x y _ _ hx hy =>
      intro m hm; rw [mul_assoc]; exact hx _ (hy m hm)
  have h1 : (1 : R) ∈ LinearMap.range Φ := by
    have := hA 1 T.one_mem 0
    simpa [G] using this
  have hle : Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤
      LinearMap.range Φ := by
    intro y hy
    simpa using hclosed y hy 1 h1
  calc finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L))
      = finrank k (Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L))) :=
        (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank k (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ finrank k ((Fin n → Fin q) → T) := LinearMap.finrank_range_le Φ
    _ = q ^ n * finrank k T := by simp [Module.finrank_pi_fintype]

theorem sectionEx {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ S : Subalgebra k R, (∀ s ∈ S, IsNilpotent s → s = 0) ∧ ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s) := by
  classical
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨⊤, fun s _ hs => by simpa using hnil s hs, fun r => ⟨r, Algebra.mem_top, by simp⟩⟩
  have hq2 : 2 ≤ p ^ c := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hc.ne' p)
  have hq0 : 0 < p ^ c := by omega
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let N := nilradical R
  let f : R →ₐ[k] R ⧸ N := Ideal.Quotient.mkₐ k N
  have hf : ∀ r, f r = Ideal.Quotient.mk N r := fun r => rfl
  have hfN : ∀ r, f r = 0 ↔ IsNilpotent r := fun r => by
    rw [hf, Ideal.Quotient.eq_zero_iff_mem]; exact mem_nilradical
  haveI : IsReduced (R ⧸ N) :=
    (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  haveI : FiniteDimensional k (R ⧸ N) :=
    Module.Finite.of_surjective f.toLinearMap Ideal.Quotient.mk_surjective
  have hrootbar : ∀ a : k, ∃ w : R ⧸ N, w ^ (p ^ c) = algebraMap k (R ⧸ N) a := fun a => by
    obtain ⟨w, hw⟩ := hroot a
    exact ⟨f w, by rw [← map_pow, hw, AlgHom.commutes]⟩

  obtain ⟨n, hn, -⟩ := fieldGen (k := k) (E := Tw k p c) p c
    (fun a => ⟨(a : k), rfl⟩)

  have hα : ∀ I : MaximalSpectrum R, ∃ α : Fin n → R ⧸ I.asIdeal,
      Algebra.adjoin k (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
    intro I
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional k (R ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    obtain ⟨n', hn', α, hα⟩ := fieldGen (k := k) (E := R ⧸ I.asIdeal) p c (fun a => by
      obtain ⟨w, hw⟩ := hroot a
      exact ⟨Ideal.Quotient.mkₐ k I.asIdeal w, by rw [← map_pow, hw, AlgHom.commutes]⟩)
    have : n' = n := Nat.pow_right_injective hq2 (hn'.symm.trans hn)
    subst this
    exact ⟨α, hα⟩
  choose α hα using hα
  let π : (R ⧸ N) ≃ₐ[k] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
    (IsArtinianRing.quotNilradicalEquivPi R).restrictScalars k
  let Lbar : Fin n → R ⧸ N := fun i => π.symm (fun I => α I i)
  let σ : ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal → R ⧸ N := fun I z => π.symm (Pi.single I z)
  have hσadd : ∀ I z w, σ I (z + w) = σ I z + σ I w := fun I z w => by
    simp only [σ, Pi.single_add, map_add (f := _)]
  have hσmul : ∀ I z w, σ I (z * w) = σ I z * σ I w := fun I z w => by
    simp only [σ, Pi.single_mul, map_mul]
  have hσpow : ∀ I z, σ I (z ^ (p ^ c)) = σ I z ^ (p ^ c) := fun I z => by
    apply π.injective
    simp only [σ, map_pow, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h, zero_pow hq0.ne']
  have hσalg : ∀ I (a : k), σ I (algebraMap k _ a) = algebraMap k (R ⧸ N) a * σ I 1 := fun I a => by
    apply π.injective
    simp only [σ, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  have hσL : ∀ I i, σ I (α I i) = σ I 1 * Lbar i := fun I i => by
    apply π.injective
    simp only [σ, Lbar, map_mul, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  let A := Algebra.adjoin k (Set.range (fun b : R ⧸ N => b ^ (p ^ c)) ∪ Set.range Lbar)
  have he : ∀ I, σ I 1 ∈ A := fun I => by
    have : σ I 1 = σ I 1 ^ (p ^ c) := by rw [← hσpow, one_pow]
    rw [this]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
  have hσA : ∀ I z, σ I z ∈ A := by
    intro I z
    have hz : z ∈ Algebra.adjoin k
        (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range (α I)) := by
      rw [hα I]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨i, rfl⟩
      · rw [hσpow]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
      · rw [hσL]; exact A.mul_mem (he I) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    | algebraMap a => rw [hσalg]; exact A.mul_mem (A.algebraMap_mem a) (he I)
    | add x y _ _ hx hy => rw [hσadd]; exact A.add_mem hx hy
    | mul x y _ _ hx hy => rw [hσmul]; exact A.mul_mem hx hy
  have hAtop : ∀ x : R ⧸ N, x ∈ A := by
    intro x
    have : x = ∑ I, σ I (π x I) := by
      apply π.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [σ, AlgEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single (π x)).symm
    rw [this]; exact A.sum_mem fun I _ => hσA I _

  choose L hL using fun i => Ideal.Quotient.mk_surjective (I := N) (Lbar i)
  let T := Pw k R (p ^ c)
  have hLq : ∀ i, L i ^ (p ^ c) ∈ T := fun i => Algebra.subset_adjoin ⟨L i, rfl⟩
  let S := Algebra.adjoin k ((T : Set R) ∪ Set.range L)
  have hAS : A ≤ S.map f := Algebra.adjoin_le (by
    rintro _ (⟨b, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨r ^ (p ^ c), Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin ⟨r, rfl⟩)),
        by rw [map_pow]; rfl⟩
    · exact ⟨L i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩), hL i⟩)
  have hlift : ∀ r : R, ∃ s ∈ S, f s = f r := fun r => hAS (hAtop (f r))

  let g : S →ₗ[k] R ⧸ N := f.toLinearMap ∘ₗ S.val.toLinearMap
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, hfs⟩ := hlift r
    exact ⟨⟨s, hs⟩, hfs⟩
  have hS : finrank k S ≤ (p ^ c) ^ n * finrank k T :=
    finrank_adjoin_pow_le T (p ^ c) n hq0 L hLq
  have hTmem : ∀ t : T, f t ∈ Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) := by
    intro t
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    show f t ∈ Pw k (R ⧸ N) (p ^ c)
    rw [← hw, map_pow]
    exact Algebra.subset_adjoin ⟨f w, rfl⟩
  let h : T →ₗ[k] Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) :=
    LinearMap.codRestrict _ (f.toLinearMap ∘ₗ T.val.toLinearMap) hTmem
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : f t = 0 := congrArg Subtype.val ht
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    obtain ⟨m, hm⟩ := (hfN _).mp h0
    have hwn : IsNilpotent w := ⟨p ^ c * m, by rw [pow_mul, hw, hm]⟩
    exact Subtype.ext (by rw [← hw, hnil w hwn]; rfl)
  have hT : finrank k T ≤ finrank k (Pw k (R ⧸ N) (p ^ c)) := by
    rw [← Subalgebra.finrank_toSubmodule (Pw k (R ⧸ N) (p ^ c))]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hfc := fc (B := R ⧸ N) p c hrootbar
  rw [hn] at hfc
  have hbar : finrank k (R ⧸ N) ≤ finrank k S := by
    rw [← finrank_top k (R ⧸ N), ← LinearMap.range_eq_top.mpr hg]
    exact LinearMap.finrank_range_le g
  have heq : finrank k S = finrank k (R ⧸ N) := by
    refine le_antisymm ?_ hbar
    calc finrank k S ≤ (p ^ c) ^ n * finrank k T := hS
      _ ≤ (p ^ c) ^ n * finrank k (Pw k (R ⧸ N) (p ^ c)) := Nat.mul_le_mul_left _ hT
      _ = finrank k (R ⧸ N) := hfc.symm
  have hginj : Function.Injective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hg
  refine ⟨S, fun s hs hsn => ?_, fun r => ?_⟩
  · have : g ⟨s, hs⟩ = g 0 := by
      rw [map_zero]; exact (hfN s).mpr hsn
    exact congrArg Subtype.val (hginj this)
  · obtain ⟨s, hs, hfs⟩ := hlift r
    refine ⟨s, hs, (hfN _).mp ?_⟩
    rw [map_sub, hfs, sub_self]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.SEps
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem idem {k S : Type*} [Field k] [CommRing S] [Algebra k S] [FiniteDimensional k S] [IsReduced S] :
    ∃ (m : ℕ) (e : Fin m → S), (∀ t, IsIdempotentElem (e t)) ∧ ∑ t, e t = 1 ∧
      (∀ t t', t ≠ t' → e t * e t' = 0) ∧ ∀ t s, s * e t = 0 ∨ ∃ w, s * e t * w = e t := by
  classical
  have : IsArtinianRing S := IsArtinianRing.of_finite k S
  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set φ := IsArtinianRing.equivPi S with hφ
  let σ := (Fintype.equivFin (MaximalSpectrum S)).symm
  refine ⟨Fintype.card (MaximalSpectrum S), fun t => φ.symm (Pi.single (σ t) 1), ?_, ?_, ?_, ?_⟩
  · intro t
    show _ * _ = _
    rw [← map_mul]
    congr 1
    ext M
    by_cases h : M = σ t
    · subst h; simp
    · simp [h]
  · apply φ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [AlgEquiv.apply_symm_apply]
    rw [Equiv.sum_comp σ (fun M => (Pi.single M 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal))]
    exact Finset.univ_sum_single (1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal)
  · intro t t' htt
    rw [← map_mul]
    have hne : σ t ≠ σ t' := fun h => htt (σ.injective h)
    have : (Pi.single (σ t) 1 * Pi.single (σ t') 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal) = 0 := by
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [hne.symm]
      · simp [h1]
    rw [this, map_zero]
  · intro t s
    have := (σ t).isMaximal
    by_cases ha : φ s (σ t) = 0
    · left
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [ha]
      · simp [h1]
    · right
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
      refine ⟨φ.symm (Pi.single (σ t) b), ?_⟩
      apply φ.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp only [Pi.mul_apply, Pi.single_eq_same, mul_one]; exact hb
      · simp [h1]

theorem sEps {k R : Type*} [Field k] [CommRing R] [Algebra k R] [IsPrincipalIdealRing R] (S : Subalgebra k R)
    (hS : ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s)) (q : ℕ) (hnil : ∀ r : R, IsNilpotent r → r ^ q = 0) :
    ∃ ε : R, IsNilpotent ε ∧ ∀ r : R, ∃ σ : Fin q → R, (∀ l, σ l ∈ S) ∧ r = ∑ l, σ l * ε ^ (l : ℕ) := by
  classical
  set ε := Submodule.IsPrincipal.generator (nilradical R) with hε
  have hspan : Ideal.span {ε} = nilradical R := Ideal.span_singleton_generator _
  have hεn : IsNilpotent ε := mem_nilradical.mp (Submodule.IsPrincipal.generator_mem _)
  refine ⟨ε, hεn, fun r => ?_⟩
  have key : ∀ n : ℕ, ∃ σ : Fin n → R, (∀ l, σ l ∈ S) ∧
      ∃ u : R, r = ∑ l, σ l * ε ^ (l : ℕ) + ε ^ n * u := by
    intro n
    induction n with
    | zero => exact ⟨Fin.elim0, fun l => l.elim0, r, by simp⟩
    | succ n ih =>
      obtain ⟨σ, hσ, u, hu⟩ := ih
      obtain ⟨s, hs, hn⟩ := hS u
      have hm : u - s ∈ Ideal.span {ε} := by rw [hspan]; exact mem_nilradical.mpr hn
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Fin.snoc σ s, fun l => ?_, v, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using hs
        · simpa using hσ i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [hu]
        have : u = s + v * ε := by rw [hv]; ring
        rw [this]
        ring
  obtain ⟨σ, hσ, u, hu⟩ := key q
  refine ⟨σ, hσ, ?_⟩
  rw [hu, hnil ε hεn, zero_mul, add_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem rdata {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsPrincipalIdealRing R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ (r : ℕ) (s : Fin r → R) (c' : Fin r → Fin r → Fin r → k) (u : Fin r → k) (ε : R) (m : ℕ)
      (κ : Fin m → Fin r → k),
      (∀ j j', s j * s j' = ∑ t, c' j j' t • s t) ∧ ∑ j, u j • s j = 1 ∧ ε ^ (p ^ c) = 0 ∧
      (∀ y : R, ∃ γ : Fin (p ^ c) → Fin r → k, y = ∑ l, ∑ j, γ l j • (s j * ε ^ (l : ℕ))) ∧
      (∀ t, IsIdempotentElem (∑ j, κ t j • s j)) ∧ (∑ t, ∑ j, κ t j • s j) = 1 ∧
      (∀ t t', t ≠ t' → (∑ j, κ t j • s j) * (∑ j, κ t' j • s j) = 0) ∧
      ∀ t (v : Fin r → k), (∑ j, v j • s j) * (∑ j, κ t j • s j) = 0 ∨
        ∃ w : R, (∑ j, v j • s j) * (∑ j, κ t j • s j) * w = ∑ j, κ t j • s j := by
  classical
  obtain ⟨S, hSred, hSlift⟩ := sectionEx p c hnil hroot
  have : IsReduced S := ⟨fun x hx => Subtype.ext (hSred x x.2 (hx.map S.val))⟩
  have : FiniteDimensional k S := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
  obtain ⟨m, e, he1, he2, he3, he4⟩ := idem (k := k) (S := S)
  obtain ⟨ε, hεn, hε⟩ := sEps S hSlift (p ^ c) hnil
  let b := Module.finBasis k S
  have hsum : ∀ x : S, ∑ j, b.repr x j • ((b j : S) : R) = (x : R) := by
    intro x
    have h := congrArg S.val (b.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simpa using h
  refine ⟨finrank k S, fun j => (b j : R), fun j j' t => b.repr (b j * b j') t, fun j => b.repr 1 j, ε, m,
    fun t j => b.repr (e t) j, ?_, ?_, hnil ε hεn, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j'
    rw [hsum]; rfl
  · rw [hsum]; rfl
  · intro y
    obtain ⟨σ, hσ, hy⟩ := hε y
    refine ⟨fun l j => b.repr ⟨σ l, hσ l⟩ j, ?_⟩
    rw [hy]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [hsum]
  · intro t
    simp only [hsum]
    exact congrArg Subtype.val (he1 t)
  · simp only [hsum]
    have h := congrArg S.val he2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h
    simpa using h
  · intro t t' htt
    simp only [hsum]
    exact congrArg Subtype.val (he3 t t' htt)
  · intro t v
    simp only [hsum]
    have hx : ∑ j, v j • ((b j : S) : R) = ((∑ j, v j • b j : S) : R) := by
      simp
    rw [hx]
    rcases he4 t (∑ j, v j • b j) with h0 | ⟨w, hw⟩
    · left; exact congrArg Subtype.val h0
    · right; exact ⟨w, congrArg Subtype.val hw⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
