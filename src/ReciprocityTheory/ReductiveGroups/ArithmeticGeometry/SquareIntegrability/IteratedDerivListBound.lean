module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OwnerNoneIff
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivDeterminantPolyTensor
namespace ReciprocityTheory.ChartRestriction.G.I2

open MvPolynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}

section Expand
variable (bs : Fin nb → Block E n dim)

abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)

abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i

def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)

def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)

theorem block_poly_expand (B : Block E n dim) :
    B.poly = ∑ p : Fin B.c → Equiv.Perm (Fin B.i),
      (∏ r, ((Equiv.Perm.sign (p r) : ℤ) : MvPolynomial (Letter n dim) ℂ)) *
        ∏ r, ∏ b, X (B.col b, ⟨B.τ, Fin.castLE B.hi (p r b)⟩) := by
  rw [Block.poly, Matrix.det_apply', ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem determinantPoly_expand :
    P1 bs = ∑ T : Choice bs, sgnT bs T • ∏ t : Slot bs, X (letter bs T t) := by
  rw [P1]
  simp only [block_poly_expand]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul]
  congr 1
  · simp only [sgnT, map_prod, map_intCast]
  · rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.prod_prod_type]
    rfl

end Expand

section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)


open Classical in
def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  by
    classical
    exact (Multiset.map (letter bs T) Finset.univ.val).toList.map
      (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))

theorem prod_X_letter (T : Choice bs) :
    (∏ t : Slot bs, MvPolynomial.X (letter bs T t) : MvPolynomial (Letter n X.dim) ℂ) =
      monomial (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) 1 := by
  rw [MvPolynomial.monomial_sum_one]
  rfl

theorem toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [Finset.sum_eq_multiset_sum]
  have h : ∀ (s : Multiset (Slot bs)),
      (s.map fun t => ({letter bs T t} : Multiset (Letter n X.dim))).sum = s.map (letter bs T) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  exact h _

theorem polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by
  rw [determinantPoly_expand, jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [polyDeriv_smul, prod_X_letter, polyDeriv_monomial_one, pdTerm_eq_itD, toMultiset_letters]
  congr 1
  have hl : (Multiset.map (letter bs T) Finset.univ.val).toList.map dir =
      (lst X bs T).map (fun p => Pi.single p.1 p.2) := by
    rw [lst, List.map_map]
    rfl
  rw [hl]
  have hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s k (fun _ => z)) := fun k =>
    (hs k).comp (contDiff_pi.2 fun _ => contDiff_id)
  have h1 := itD_prod hg (lst X bs T) 0
  rw [show tens X s = fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k) from rfl, h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.zero_apply, itD_col (hs k)]
  rfl


end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Cols
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

def colB (p : Σ j : Fin nb, Fin (bs j).i) : Fin n := (bs p.1).col p.2

variable {bs}

theorem colB_inj (hD : Disj bs) : Function.Injective (colB bs) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  by_cases hj : j = j'
  · subst hj
    have ha : a = a' := (bs j).col_inj h
    subst ha
    rfl
  · exact absurd h (hD j j' hj a a')

variable (bs)


open Classical in
def owner (k : Fin n) : Option (Σ j : Fin nb, Fin (bs j).i) :=
  if h : ∃ p, colB bs p = k then some h.choose else none

variable {bs}

theorem owner_colB (hD : Disj bs) (p : Σ j : Fin nb, Fin (bs j).i) : owner bs (colB bs p) = some p := by
  have h' : ∃ q, colB bs q = colB bs p := ⟨p, rfl⟩
  rw [owner, dite_eq_left h']
  exact congrArg some (colB_inj hD h'.choose_spec)

theorem colB_of_owner {k : Fin n} {p : Σ j : Fin nb, Fin (bs j).i} (h : owner bs k = some p) :
    colB bs p = k := by
  by_cases h' : ∃ q, colB bs q = k
  · rw [owner, dite_eq_left h'] at h
    obtain rfl := Option.some_injective _ h
    exact h'.choose_spec
  · rw [owner, dite_eq_right h'] at h
    cases h

theorem owner_eq_none {k : Fin n} (h : ∀ p, colB bs p ≠ k) : owner bs k = none := by
  rw [owner, dite_eq_right (show ¬∃ q, colB bs q = k from fun ⟨q, hq⟩ => h q hq)]

theorem owner_none_iff (hD : Disj bs) (k : Fin n) : owner bs k = none ↔ ∀ p, colB bs p ≠ k := by
  refine ⟨fun h p hp => ?_, owner_eq_none⟩
  subst hp
  rw [owner_colB hD] at h
  cases h

theorem prod_cols {M : Type*} [CommMonoid M] (hD : Disj bs) (f : Fin n → M) :
    ∏ k, f k = (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), f k) * ∏ p, f (colB bs p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
  congr 1
  rw [← Finset.prod_image (s := Finset.univ) (g := colB bs) (by
    intro a _ b _ h
    exact colB_inj hD h)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, owner_none_iff hD,
    not_forall, ne_eq, not_not]

end Cols

section Letters
variable (X : PT E) {bs : Fin nb → Block E n X.dim}

theorem filter_positions (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    (Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = colB bs p) =
      Multiset.map (fun r : Fin (bs p.1).c => letter bs T ⟨p.1, (r, p.2)⟩) Finset.univ.val := by
  obtain ⟨j0, a0⟩ := p
  rw [Multiset.filter_map]
  calc _ = Multiset.map (letter bs T)
        (Multiset.map (fun r : Fin (bs j0).c => (⟨j0, (r, a0)⟩ : Slot bs)) Finset.univ.val) := by
        congr 1
        refine (Multiset.Nodup.ext (Finset.univ.nodup.filter _)
          (Finset.univ.nodup.map (fun r r' h => by simpa using h))).2 ?_
        rintro ⟨j, r, a⟩
        simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp,
          Multiset.mem_map]
        constructor
        · intro h
          have hja : (⟨j, a⟩ : Σ j : Fin nb, Fin (bs j).i) = ⟨j0, a0⟩ := colB_inj hD h
          cases hja
          exact ⟨r, rfl⟩
        · rintro ⟨r', h⟩
          cases h
          rfl
    _ = _ := by rw [Multiset.map_map]; rfl

open Classical in
theorem colL_block (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    ((colL (lst X bs T) (colB bs p) : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      Multiset.map (fun r : Fin (bs p.1).c => EuclideanSpace.single
        (⟨(bs p.1).τ, Fin.castLE (bs p.1).hi (T p.1 r p.2)⟩ : Idx X.dim) (1 : ℂ)) Finset.univ.val := by
  have hc : ∀ (L : List (Fin n × Vsp X.dim)) (k : Fin n),
      ((colL L k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
        Multiset.map Prod.snd (Multiset.filter (fun x => x.1 = k) (L : Multiset _)) := by
    intro L k
    simp [colL]
  rw [hc, lst, ← Multiset.map_coe, Multiset.coe_toList, Multiset.filter_map, Multiset.map_map]
  have h2 := congrArg (Multiset.map (fun l : Letter n X.dim => EuclideanSpace.single l.2 (1 : ℂ)))
    (filter_positions X hD T p)
  rw [Multiset.map_map] at h2
  convert h2 using 2
  all_goals first
    | rfl
    | exact Multiset.filter_congr fun _ _ => Iff.rfl

theorem colL_empty (hD : Disj bs) (T : Choice bs) {k : Fin n} (hk : owner bs k = none) :
    colL (lst X bs T) k = [] := by
  rw [owner_none_iff hD] at hk
  unfold colL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  unfold lst at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toList.1 hl)
  intro h
  exact hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)

end Letters

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Col
variable {dim : (E →+* ℂ) → ℕ}

theorem iteratedDeriv_list_bound (s : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (μ : ℂ) (y : Vsp dim) (ε : ℝ)
    (σ : E →+* ℂ)
    (hbd : ∀ xs : Fin c → Vsp dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
      ‖d1 s c xs - μ * ∏ k, Hf (xs k) y‖ ≤ ε)
    (l : List (Vsp dim)) (g : Fin c → Vsp dim)
    (hl : (l : Multiset (Vsp dim)) = Multiset.map g Finset.univ.val)
    (hg : ∀ r, InPart σ (g r) ∧ ‖g r‖ = 1) :
    ‖d1 s l.length (fun j => l.get j) - μ * ∏ r, Hf (g r) y‖ ≤ ε := by
  have hlen : l.length = c := by
    have := congrArg Multiset.card hl
    simpa using this
  subst hlen
  have hmem : ∀ j : Fin l.length, InPart σ (l.get j) ∧ ‖l.get j‖ = 1 := by
    intro j
    have : l.get j ∈ Multiset.map g Finset.univ.val := by
      rw [← hl]; exact Multiset.mem_coe.2 (List.get_mem l j)
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 this
    rw [← hr]; exact hg r
  have hm : Finset.univ.val.map (fun j : Fin l.length => l.get j) = (l : Multiset (Vsp dim)) := by
    rw [Fin.univ_val_map]
    congr 1
    first
    | exact List.ofFn_get l
    | exact List.ofFn_getElem l
    | simp
  have hprod : ∏ j : Fin l.length, Hf (l.get j) y = ∏ r, Hf (g r) y := by
    calc ∏ j : Fin l.length, Hf (l.get j) y
        = ((Finset.univ.val.map (fun j : Fin l.length => l.get j)).map (fun x => Hf x y)).prod := by
          rw [Multiset.map_map]; rfl
      _ = ∏ r, Hf (g r) y := by
          rw [hm, hl, Multiset.map_map]; rfl
  have := hbd (fun j => l.get j) hmem
  rw [hprod] at this
  exact this

theorem d1_zero (s : (Fin 1 → Vsp dim) → ℂ) (v : Fin 0 → Vsp dim) : d1 s 0 v = s 0 := by
  unfold d1
  exact iteratedFDeriv_zero_apply _

end Col

section Main
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

open Classical in
def eU (j : Fin nb) (a : Fin (bs j).i) : Vsp dim := by
  classical
  exact EuclideanSpace.single (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx dim) (1 : ℂ)

def idealA (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ) (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim)
    (ee : Fin n → ℂ) (T : Choice bs) (k : Fin n) : ℂ :=
  match owner bs k with
  | some p => μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)
  | none => ee k

def blockM (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (j : Fin nb) :
    Matrix (Fin (bs j).i) (Fin (bs j).i) ℂ :=
  Matrix.of fun a b => Hf (eU bs j a) (y ⟨j, b⟩)

theorem main_term (hD : Disj bs) (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ)
    (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (ee : Fin n → ℂ) :
    ∑ T : Choice bs, sgnT bs T * ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
        ∏ j, (blockM bs y j).det ^ (bs j).c := by
  have hinj : Function.Injective (colB bs) := by
    rintro ⟨j, a⟩ ⟨j', a'⟩ h
    simp only [colB] at h
    by_cases hj : j = j'
    · subst hj
      have := (bs j).col_inj h
      subst this
      rfl
    · exact absurd h (hD j j' hj a a')
  have hown : ∀ p, owner bs (colB bs p) = some p := by
    intro p
    have hex : ∃ p', colB bs p' = colB bs p := ⟨p, rfl⟩
    unfold owner
    rw [dite_eq_left hex]
    exact congrArg some (hinj hex.choose_spec)
  have hnone : ∀ k, owner bs k = none ↔ k ∉ Finset.univ.image (colB bs) := by
    intro k
    constructor
    · intro h hk
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hk
      rw [hown] at h
      exact Option.some_ne_none _ h
    · intro h
      unfold owner
      rw [dite_eq_right]
      rintro ⟨p, rfl⟩
      exact h (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  have hT : ∀ T : Choice bs, ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
        ∏ p, (μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
    intro T
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h := (Finset.mem_filter.mp hk).2
      simp only [idealA, h]
    · have hset : Finset.univ.filter (fun k => ¬ owner bs k = none) = Finset.univ.image (colB bs) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnone]
        exact not_not
      rw [hset, Finset.prod_image (fun p _ q _ h => hinj h)]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [idealA, hown]
  have hdet : ∀ j, (blockM bs y j).det ^ (bs j).c =
      ∏ r : Fin (bs j).c, ∑ σ : Equiv.Perm (Fin (bs j).i),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ b, Hf (eU bs j (σ b)) (y ⟨j, b⟩) := by
    intro j
    rw [Fin.prod_const, Matrix.det_apply]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  have hsum : ∑ T : Choice bs, sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p) =
      ∏ j, (blockM bs y j).det ^ (bs j).c := by
    simp_rw [hdet]
    first
    | simp_rw [Fintype.prod_sum]
    | simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib, sgnT]
    congr 1
    first
    | rw [Fintype.prod_sigma]
    | rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    first
    | rw [Finset.prod_comm]
    | exact Finset.prod_comm.symm
  calc ∑ T, sgnT bs T * ∏ k, idealA bs μ y ee T k
      = ∑ T : Choice bs, ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * ∏ p, μ p) *
          (sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [hT, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Main

end

end ReciprocityTheory.ChartRestriction.G.I2
