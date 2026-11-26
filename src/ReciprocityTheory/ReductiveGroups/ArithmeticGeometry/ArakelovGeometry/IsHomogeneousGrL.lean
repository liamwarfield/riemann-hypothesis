module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h

theorem isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩

end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem exists_colon_prime (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  let e := Fintype.equivFin K
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
    (isHomogeneous_lex_iff e J).2 hJ

  have hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)),
      f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) d →
      (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by
    intro f d hf i g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]
    exact hJh (i + d) hg

  let S : Set (Ideal (MRing ι)) := {P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}
  have hne : S.Nonempty := by
    refine ⟨J.colon {1}, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩
  obtain ⟨P, hP, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne
  obtain ⟨f, c, hf, hfJ, rfl⟩ := hP
  have hfm := mem_lex_of_isMultiHomog e hf
  have hPh := hcolh f _ hfm
  refine ⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩
  apply Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh
  · intro h
    apply hfJ
    have h1 : (1 : MRing ι) ∈ J.colon {f} := by rw [h]; exact Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    by_cases hxP : x ∈ J.colon {f}
    · exact Or.inl hxP
    right
    have hxf := SetLike.GradedMul.mul_mem hx hfm
    have hxfJ : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP
    have hmem : J.colon {x * f} ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩
    have hle : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
      rw [← mul_assoc, mul_comm g x, mul_assoc]
      exact J.mul_mem_left x hg
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hmem (lt_of_le_of_ne hle hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
    rw [← mul_assoc, mul_comm y x]
    exact hxy

theorem isMultiHomogIdeal_sup_span {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩
  rintro g (hg | hg)
  · exact hS g hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact ⟨c, hf⟩

theorem exists_primeFiltration_of_isMultiHomogIdeal (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j

end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)

theorem lexDeg_add (a b : K → ℕ) : lexDeg (a + b) = lexDeg a + lexDeg b := rfl


variable (ι) in
abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))

theorem mem_grL_iff (f : MRing ι) (a : K → ℕ) : f ∈ grL ι (lexDeg a) ↔ IsMultiHomog f a := by
  constructor
  · intro h
    have := isMultiHomog_of_mem_lex _ h
    convert this using 1
    funext k
    simp [lexDeg]
  · exact mem_lex_of_isMultiHomog _

theorem mHom_eq (a : K → ℕ) : mHom ι a = grL ι (lexDeg a) := by
  rw [mHom]
  have : {s : MRing ι | IsMultiHomog s a} = (grL ι (lexDeg a) : Set (MRing ι)) := by
    ext s
    exact (mem_grL_iff s a).symm
  rw [this, Submodule.span_eq]

theorem mem_mHom_iff (f : MRing ι) (a : K → ℕ) : f ∈ mHom ι a ↔ IsMultiHomog f a := by
  rw [mHom_eq, mem_grL_iff]

theorem isHomogeneous_grL {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    J.IsHomogeneous (grL ι) := (isHomogeneous_lex_iff _ J).mpr hJ

def pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) : mHom ι a →ₗ[ℤ] MRing ι ⧸ J :=
  (Ideal.Quotient.mkₐ ℤ J).toLinearMap ∘ₗ (mHom ι a).subtype

theorem range_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) :
    LinearMap.range (pieceMap J a) = mPiece J a := by
  rw [pieceMap, LinearMap.range_comp, Submodule.range_subtype]
  rfl

theorem mem_ker_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) (x : mHom ι a) :
    x ∈ LinearMap.ker (pieceMap J a) ↔ (x : MRing ι) ∈ J := by
  simp [pieceMap, Ideal.Quotient.eq_zero_iff_mem]

theorem card_mPiece_eq (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by
  rw [← range_pieceMap]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem card_quot_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (B.map A.mkQ)
  have e1 : Nat.card ((V ⧸ A) ⧸ B.map A.mkQ) = Nat.card (V ⧸ B) :=
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient A B h).toEquiv
  let φ : B →ₗ[R] V ⧸ A := A.mkQ ∘ₗ B.subtype
  have hr : LinearMap.range φ = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker φ = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e2 : Nat.card (B.map A.mkQ) = Nat.card (B ⧸ A.comap B.subtype) := by
    rw [← hr, ← hk]
    exact Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv.symm
  rw [h1, e1, e2]
  ring

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  rw [← mem_grL_iff] at hf hg ⊢
  rw [lexDeg_add]
  exact SetLike.GradedMul.mul_mem hf hg

theorem card_mPiece_step {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    Nat.card (mPiece J a) = Nat.card (mPiece (J ⊔ Ideal.span {f}) a) * Nat.card (mPiece q (a - c)) := by
  classical
  set J' := J ⊔ Ideal.span {f}
  have hJJ' : J ≤ J' := le_sup_left
  set A := LinearMap.ker (pieceMap J a)
  set B := LinearMap.ker (pieceMap J' a)
  have hAB : A ≤ B := fun x hx => by
    rw [mem_ker_pieceMap] at hx ⊢
    exact hJJ' hx
  rw [card_mPiece_eq, card_mPiece_eq, card_mPiece_eq, card_quot_chain A B hAB]
  congr 1
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ mHom ι a := fun g => by
    rw [mem_mHom_iff]
    have := isMultiHomog_mul ((mem_mHom_iff _ _).mp g.2) hf
    rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨⟨(g : MRing ι) * f, hmul g⟩, by
        rw [mem_ker_pieceMap]
        exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨⟨x, hxa⟩, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hxJ' : x ∈ J' := (mem_ker_pieceMap J' a ⟨x, hxa⟩).mp hxB
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ J := isHomogeneous_grL hJ _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨⟨x, hxa⟩, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype, mem_ker_pieceMap]
    have : (((χ' ⟨g, hg⟩ - ⟨⟨x, hxa⟩, hxB⟩ : B) : mHom ι a) : MRing ι) = g * f - x := rfl
    rw [this, hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact J.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      mem_ker_pieceMap]
    rfl
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
