module

public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
public import Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCDeg
section -- merged from Formalism.LocalToGlobal.CharacterGerms.IsWHLetterMinorK
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCInv
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem rowShift_C (σ : T) (i i' : Fin (r σ)) (t z : C) :
    rowShift r n C σ i i' t (MvPolynomial.C z) = MvPolynomial.C z := (rowShift r n C σ i i' t).commutes z

variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)

theorem shift_same (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (t : C)
    (ρ : Fin N) (c : Fin N') (h : ¬ (σ = σ0 ∧ c.val = i.val)) :
    rowShift r n C σ i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, rowShift_C, rowShift_X, hlt, if_neg]
  intro e
  apply h
  exact ⟨(congrArg (fun x : T × ℕ × Fin n => x.1) e).symm, congrArg (fun x : T × ℕ × Fin n => x.2.1) e⟩

theorem shift_add (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (i i' : Fin (r σ0)) (t : C)
    (ρ : Fin N) (c c' : Fin N') (hc : c.val = i.val) (hc' : c'.val = i'.val) :
    rowShift r n C σ0 i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) + MvPolynomial.C t * Φ (X (ρ, c')) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, hΦ, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 : (lt (ρ, c) q).2.2 = colf ρ q := congrArg (fun x : T × ℕ × Fin n => x.2.2) (hlt ρ c q)
  have h1 : keyL (lt (ρ, c) q) = (σ0, i.val, (lt (ρ, c) q).2.2) := by rw [hlt, hc, h2]
  rw [map_mul, rowShift_C, rowShift_X, if_pos h1]
  have h3 : (⟨σ0, i', (lt (ρ, c) q).2.2⟩ : Letter T r n) = lt (ρ, c') q := by
    apply keyL_inj
    rw [hlt, hc', h2]
    rfl
  rw [h3]
  ring

theorem rowShift_minor_lin (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (Φ (minorK C N N' k)) = Φ (minorK C N N' k) := by
  unfold minorK
  split_ifs with h
  · set A : Matrix (Fin k) (Fin k) (MvPolynomial (Letter T r n) C) :=
      Matrix.of fun b c => Φ (X (Fin.castLE h.1 b, Fin.castLE h.2 c)) with hA
    have e1 : Φ (Matrix.of fun b c : Fin k =>
        (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det = A.det := by
      rw [AlgHom.map_det]
      congr 1
    rw [e1, AlgHom.map_det]
    by_cases hc : σ = σ0 ∧ i.val < k
    · obtain ⟨rfl, hik⟩ := hc
      have hi' : i'.val < i.val := hi
      let ci : Fin k := ⟨i.val, hik⟩
      let ci' : Fin k := ⟨i'.val, lt_trans hi' hik⟩
      have hne : ci ≠ ci' := by
        intro e
        have h3 : ci.val = ci'.val := congrArg Fin.val e
        have h4 : i.val = i'.val := h3
        omega
      have e2 : (rowShift r n C σ i i' t).mapMatrix A =
          A.updateCol ci (fun b => A b ci + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b ci') := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        simp only [hA, Matrix.of_apply]
        by_cases hcc : c = ci
        · subst hcc
          rw [if_pos rfl, smul_eq_mul]
          exact shift_add Φ σ w lt colf hΦ hlt i i' t _ _ _ rfl rfl
        · rw [if_neg hcc]
          refine shift_same Φ σ w lt colf hΦ hlt σ i i' t _ _ ?_
          rintro ⟨_, e⟩
          exact hcc (Fin.ext e)
      rw [e2, Matrix.det_updateCol_add_smul_self A hne]
    · have e2 : (rowShift r n C σ i i' t).mapMatrix A = A := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
        simp only [hA, Matrix.of_apply]
        refine shift_same Φ σ0 w lt colf hΦ hlt σ i i' t _ _ ?_
        rintro ⟨e0, e⟩
        apply hc
        refine ⟨e0, ?_⟩
        have : c.val = i.val := e
        omega
      rw [e2]
  · simp

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def trueT (g : Fin 2) (s : ZMod 2) : ZMod 2 := if g = 0 then s else s + 1

theorem SelfConjugatePlaceSetting.en_fst (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2)
    (q : Fin ((X o).rkF g s)) : ((F o).en g s q).1 = trueT g s := by
  have h1 := (F o).en_ty g s q
  rw [H.hty o g] at h1
  unfold trueT
  generalize ((F o).en g s q).1 = u at h1 ⊢
  split_ifs at h1 ⊢ with hg
  · exact h1
  · subst h1
    have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [add_assoc, h2, add_zero]


variable (r tau gm) in
def PsiS (o : Orb) {M : ℕ} (col : Fin M → Fin N) :
    MvPolynomial (Fin M × WV fun _ => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  (subG r tau gm plc).comp (rename fun x : Fin M × WV fun _ => IIs r tau o =>
    ((col x.1, (⟨o, x.2⟩ : WVO fun o (_ : Fin 2) => IIs r tau o))))

theorem SelfConjugatePlaceSetting.inv_minor (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by
  refine rowShift_minor_lin ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (tau o (trueT g s))
    (fun _ q => gm o (trueT g s) q g)
    (fun x q => ⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩) (fun ρ q => plc (col ρ, q)) ?_ ?_
    σ i i' hi t k
  · intro x
    rw [AlgHom.comp_apply, rename_X]
    unfold PsiS
    rw [AlgHom.comp_apply, rename_X]
    unfold subG
    rw [aeval_X]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e2 : gm o ((F o).en g s x.2).1 q g = gm o (trueT g s) q g := by rw [H.en_fst]
    exact congrArg (fun z : C => MvPolynomial.C z * MvPolynomial.X
      (⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩ : Letter T r n)) e2
  · intro ρ c q
    show (tau o ((F o).en g s c).1, ((F o).en g s c).2.val, plc (col ρ, q)) = _
    simp only [Prod.mk.injEq]
    exact ⟨congrArg (tau o) (H.en_fst o g s c), H.std o g s c, trivial⟩

theorem SelfConjugatePlaceSetting.inv_mon (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e)) := by
  unfold monP
  simp only [map_prod, map_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_bi (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2)) =
      PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_mul, map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t, H.inv_minor plc o g' s' col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_ch (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1)) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1) := by
  rw [map_pow, map_pow, H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_monAll (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ZMod 2 → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s)))) =
      PsiS r tau gm plc o col (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s))) := by
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun s _ => H.inv_mon plc o g s col (e s) σ i i' hi t

theorem SelfConjugatePlaceSetting.inv_poly (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (b : GlobalTheory 2) (col : Fin (b.what₂ (X o).n) → Fin N)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (b.poly (X o) (F o))) = PsiS r tau gm plc o col (b.poly (X o) (F o)) := by
  cases b with
  | bi g s e y => exact H.inv_bi plc o g (1 - g) s (s + (e : ZMod 2)) col (X o).n _ _ σ i i' hi t
  | ch g s u => exact H.inv_ch plc o g s col (X o).n u σ i i' hi t
  | mon g e M => exact H.inv_monAll plc o g col e σ i i' hi t

theorem subG_blkProd :
    subG r tau gm plc (blkProd X F N L pl) =
      ∏ o, ∏ i, PsiS r tau gm plc o (fun ρ => plAt N pl o ⟨i, ρ⟩) ((blkAt L o i).poly (X o) (F o)) := by
  unfold blkProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  unfold toAll prodAll
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rename_rename]
  rfl

end Fam

theorem isotropic_to_standard_substitution_invariant : IsotropicToStdSubstLineInvariant := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc σ i i' hi t
  rw [subG_blkProd, map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => H.inv_poly plc o _ _ σ i i' hi t

end Formalism.L2.FormalSeriesBounds.RF
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousLetters

open WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_aeval {σ τ : Type} {w : τ → ℕ} {w' : σ → ℕ} (f : σ → MvPolynomial τ R)
    (hf : ∀ x, IsWeightedHomogeneous w (f x) (w' x)) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w (aeval f p) D := by
  rw [aeval_def, eval₂_eq]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have h1 : IsWeightedHomogeneous w (∏ i ∈ m.support, f i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hf i).pow (m i)
  have h2 : (∑ i ∈ m.support, m i • w' i) = D := by
    rw [← hp (mem_support_iff.1 hm), Finsupp.weight_apply]
    rfl
  have h3 := (isWeightedHomogeneous_C w (AddMonoidAlgebra.coeff p m)).mul h1
  rw [zero_add, h2] at h3
  exact h3

theorem isWH_add {σ : Type} {w1 w2 : σ → ℕ} {p : MvPolynomial σ R} {D1 D2 : ℕ}
    (h1 : IsWeightedHomogeneous w1 p D1) (h2 : IsWeightedHomogeneous w2 p D2) :
    IsWeightedHomogeneous (fun x => w1 x + w2 x) p (D1 + D2) := by
  intro m hm
  have e1 := h1 hm
  have e2 := h2 hm
  simp only [Finsupp.weight_apply, Finsupp.sum] at e1 e2 ⊢
  rw [← e1, ← e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_add _ _ _

end WH

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)

def wRowG {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (x : Fin N × WV I) : ℕ :=
  if x.2.1 = g0 ∧ (X.G x.2.1).ty (Sum.inl x.2.2) = t0 ∧ idx x.2.1 x.2.2 = c0 then 1 else 0

include std in
theorem wRowG_letter {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d)
    (x : Fin N × Fin (X.rkF g t)) :
    wRowG X idx g0 t0 c0 (F.letter g t x) = if (g = g0 ∧ t = t0) ∧ (x.2 : ℕ) = c0 then 1 else 0 := by
  simp only [wRowG, Flag.letter, F.en_ty, std, and_assoc]

include std in
theorem isWH_letter_minorK {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRowG X idx (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) :=
  isWH_rename _ (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x)

theorem num_ch (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g = g0 ∧ t = t0
  · obtain ⟨rfl, rfl⟩ := hg
    simp only [le_refl, true_and, and_true, Finset.sum_ite_eq', Finset.mem_Icc]
    split_ifs <;> first | omega | simp
  · rw [if_neg (fun h => hg h.2.2.1), smul_zero, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hg ⟨h1.symm, h2.symm⟩

theorem num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g0 = g
  · subst hg
    rw [Fintype.sum_eq_single t0]
    · simp only [eq_self_iff_true, true_and, and_true, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro t ht
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    all_goals first
      | (intro k _; rw [if_neg (fun h => hg h.1)])
      | (intro t _; exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hg h.2.2.1.1.symm), smul_zero])


include std in
theorem blockPoly_isWeightedHomogeneous' (b : GlobalTheory d) (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) :
    IsWeightedHomogeneous (wRowG X idx g0 t0 c0) (b.poly X F)
      (∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), b.wt X g0 t0 k) := by
  cases b with
  | ch g t u =>
    exact isWH_deg ((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow u) (num_ch X g0 t0 c0 g t u)
  | bi g t i y =>
    refine isWH_deg (((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow (V.l ^ i * y)).mul
      ((isWH_letter_minorK X F idx std g0 t0 c0 (1 - g) (t + (i : ZMod d))).pow y)) ?_
    simp only [GlobalTheory.wt]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (num_ch X g0 t0 c0 g t _) (num_ch X g0 t0 c0 (1 - g) (t + (i : ZMod d)) y)
  | mon g e N =>
    refine isWH_deg (IsWeightedHomogeneous.prod _ _ _ fun t _ => isWH_rename _
      (IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x).pow (e t k))) ?_
    simp only [GlobalTheory.wt]
    exact num_mon X g0 t0 c0 g e N

end Block

end WeightHomogeneousLetters

end Formalism.L2.FormalSeriesBounds.RF
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem trueT_iff (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by
  unfold trueT
  revert g t' s
  decide

theorem trueT_one : ∀ t : ZMod 2, trueT 1 (t + 1) = t := by
  unfold trueT
  decide

theorem SelfConjugatePlaceSetting.rkF_eq {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) :
    (X o).rkF g s = r (tau o (trueT g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

open WeightHomogeneousMinors WeightHomogeneousLetters in
theorem isotropic_to_std_subst_degree : IsotropicToStdSubstLineDegree := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc m hm σ c0
  rw [← weight_wLet]
  suffices hWH : IsWeightedHomogeneous (wLet r n σ c0) (subG r tau gm plc (blkProd X F N L pl)) (a σ c0) from
    hWH (MvPolynomial.mem_support_iff.1 hm)
  unfold subG
  refine isWH_aeval (w' := fun x => if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) _
    (fun x => ?_) ?_
  · apply IsWeightedHomogeneous.sum
    intro col _
    have h := (isWeightedHomogeneous_C (wLet r n σ c0) (gm x.2.1 x.2.2.2.1 col x.2.2.1)).mul
      (isWeightedHomogeneous_X (R := C) (wLet r n σ c0)
        (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n))
    rw [zero_add, wLet_mk] at h
    exact h
  · by_cases hσ : ∃ o t, tau o t = σ
    · obtain ⟨o0, t0, rfl⟩ := hσ
      have keyEq : ∀ o t (c : Fin (r (tau o t))),
          ((⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨tau o0 t0, c0⟩) ↔ (o = o0 ∧ t = t0 ∧ (c : ℕ) = c0) := by
        intro o t c
        constructor
        · intro h
          have h1 : tau o t = tau o0 t0 := congrArg Sigma.fst h
          have h2 := H.inj (a₁ := (o, t)) (a₂ := (o0, t0)) h1
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨rfl, rfl, ?_⟩
          rw [eq_of_heq (Sigma.mk.inj h).2]
        · rintro ⟨rfl, rfl, hc⟩
          rw [Fin.ext hc]
      have hT1 : trueT 1 (t0 + 1) = t0 := trueT_one t0
      have hR0 : (X o0).rkF 0 t0 = r (tau o0 t0) := H.rkF_eq o0 0 t0
      have hR1 : (X o0).rkF 1 (t0 + 1) = r (tau o0 t0) := by rw [H.rkF_eq o0 1 (t0 + 1), hT1]
      have hD : a (tau o0 t0) c0 = ∑ o, (if o = o0 then ∑ i : Fin (L o).length,
          ((∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 0 t0), (blkAt L o i).wt (X o) 0 t0 k) +
            ∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 1 (t0 + 1)), (blkAt L o i).wt (X o) 1 (t0 + 1) k) else 0) := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hR0, hR1, H.tie.1 o0 t0 c0 c0.2]
        simp only [← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← H.wt o0 t0 k, ← Fin.sum_univ_fun_getElem]
        rfl
      rw [hD]
      unfold blkProd
      refine IsWeightedHomogeneous.prod _ _ _ fun o _ => ?_
      by_cases ho : o = o0
      · subst ho
        rw [if_pos rfl]
        unfold toAll
        apply isWH_rename
        unfold prodAll
        refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
        apply isWH_rename
        refine isWH_congr ?_ (isWH_add
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 0 t0 (c0 : ℕ))
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 1 (t0 + 1) (c0 : ℕ)))
        rintro ⟨ρ, gg, tt, cc'⟩
        simp only [Function.comp_apply, keyEq, wRowG, true_and, H.hty]
        fin_cases gg <;> simp
      · rw [if_neg ho]
        unfold toAll
        apply isWH_rename
        refine isWH_of_zero (fun x => ?_) _
        obtain ⟨ρ, gg, tt, cc'⟩ := x
        simp only [Function.comp_apply, keyEq]
        rw [if_neg]
        exact fun hh => ho hh.1
    · push Not at hσ
      rw [H.tie.2 σ hσ c0 c0.2]
      refine isWH_of_zero (fun x => ?_) _
      obtain ⟨ρ, o, g, t, c⟩ := x
      show (if (⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) = 0
      rw [if_neg]
      exact fun hh => hσ o t (congrArg Sigma.fst hh)

end Formalism.L2.FormalSeriesBounds.RF
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjCharts
section -- merged from Formalism.LocalToGlobal.CharacterGerms.GramMatrixMulRight
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

abbrev AA (r : T → ℕ) (tau : Orb → ZMod 2 → T) (N : ℕ) : Type := Fin N × Σ o, IIs r tau o

def eW (N : ℕ) : (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ≃ AA r tau N × Fin 2 where
  toFun y := ((y.1, ⟨y.2.1, y.2.2.2⟩), y.2.2.1)
  invFun z := (z.1.1, ⟨z.1.2.1, ⟨z.2, z.1.2.2⟩⟩)
  left_inv := by rintro ⟨ρ, ⟨o, ⟨g, c⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨ρ, ⟨o, c⟩⟩, g⟩; rfl

def lam (z : AA r tau N × Fin 2) : Letter T r n := ⟨tau z.1.2.1 z.1.2.2.1, z.1.2.2.2, plc (z.1.1, z.2)⟩

variable {r tau}

theorem lam_inj (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h
  simp only [lam, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := inj (a₁ := (o, t)) (a₂ := (o', t')) h1
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, h5⟩ := h4
  have h6 := plc.injective h5
  simp only [Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rfl

variable (r tau)

def Gm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 α.2.2.1 col g

def Mm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 (α.2.2.1 + 1) col (1 - g)

variable {r tau gm}

theorem gram_matrix_mul_right (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  have h := gm_hyp α.2.1 α.2.2.1 (1 - g') g
  unfold Mm Gm
  rw [h]
  clear h
  fin_cases g <;> fin_cases g' <;> simp

theorem gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

variable (r tau gm)

def coS (ℓ : Letter T r n) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) : C :=
  ∑ col, if ℓ = lam r tau plc ((eW r tau N y).1, col) then Mm r tau gm (eW r tau N y).1 col (eW r tau N y).2 else 0

variable {r tau gm}

theorem coS_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm r tau gm α col g else 0 := by
  unfold coS
  rw [Equiv.apply_symm_apply]
  simp only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]
  by_cases h : α = α'
  · subst h
    simp
  · simp [h]

theorem sum_coS (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  rw [← Equiv.sum_comp (eW r tau N).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single α]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [coS_lam plc inj, if_pos rfl]
  · intro α' _ hne
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [coS_lam plc inj, if_neg (Ne.symm hne), h0]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem subG_X (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl

theorem back_subG (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have h : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS r tau gm plc ℓ x) *
      (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))).comp (subG r tau gm plc) =
      AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, subG_X, map_sum, AlgHom.id_apply]
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, (∑ x, MvPolynomial.C (coS r tau gm plc (lam r tau plc ((eW r tau N y).1, col)) x) *
        (MvPolynomial.X x : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C)) =
        ∑ g, MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :=
      fun col => sum_coS plc inj (eW r tau N y).1 col (fun c x => MvPolynomial.C c * MvPolynomial.X x) (by simp)
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ g, (∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
        (MvPolynomial.C (Mm r tau gm (eW r tau N y).1 col g) *
          (MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) :
            MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C))) =
        MvPolynomial.C (if g = (eW r tau N y).2 then 1 else 0) * MvPolynomial.X ((eW r tau N).symm ((eW r tau N y).1, g)) := by
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← gram_matrix_mul_right gm_hyp (eW r tau N y).1 (eW r tau N y).2 g, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [map_mul]; ring
    simp only [h2]
    rw [Finset.sum_eq_single (eW r tau N y).2]
    · simp
    · intro g _ hg; simp [hg]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact congrArg (fun φ => φ Q) h

end Formalism.L2.FormalSeriesBounds.RF
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem mem_vars_subG {Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ℓ ∈ (subG r tau gm plc Q).vars) : ∃ z, ℓ = lam r tau plc z := by
  unfold subG at h
  rw [MvPolynomial.aeval_eq_bind₁] at h
  obtain ⟨y, _, hy⟩ := MvPolynomial.mem_vars_bind₁ _ _ h
  have h1 := MvPolynomial.vars_sum_subset _ _ hy
  rw [Finset.mem_biUnion] at h1
  obtain ⟨col, _, h2⟩ := h1
  have h3 := MvPolynomial.vars_mul _ _ h2
  rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X, Finset.mem_singleton] at h3
  exact ⟨((eW r tau N y).1, col), h3⟩

theorem coS_off (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α : AA r tau N) (col : Fin 2)
    (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) (h : y.1 ≠ α.1) :
    coS r tau gm plc (lam r tau plc (α, col)) y = 0 := by
  have e : y = (eW r tau N).symm ((eW r tau N y).1, (eW r tau N y).2) := by
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [e, coS_lam plc inj, if_neg]
  intro h2
  apply h
  rw [h2]
  rfl

theorem isImgS_subG {dd : ℕ} (X : ∀ o, RawChart C 2 (fun _ => IIs r tau o) (Fin 2 × Fin dd))
    (uv : Letter T r n → Fin dd → C) (e : ∀ o, IIs r tau o → Fin dd → C)
    (hu : ∀ o g (c : IIs r tau o) x, (X o).u g c x = gm o c.1 x.1 g * e o c x.2)
    (huv : ∀ o (c : IIs r tau o) b, uv ⟨tau o c.1, c.2, b⟩ = e o c)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    IsImgS X plc (fun ℓ : Letter T r n => ℓ.2.2) uv (subG r tau gm plc Q) Q := by
  refine ⟨coS r tau gm plc, ?_, (back_subG plc inj gm_hyp Q).symm⟩
  intro ℓ hℓ
  obtain ⟨⟨α, col⟩, rfl⟩ := mem_vars_subG plc hℓ
  refine ⟨α.1, col, rfl, fun ρ' w h => coS_off plc inj α col (ρ', w) h, ?_⟩
  have h1 : (∑ w : (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) (α.1, w) •
      (X w.1).u w.2.1 w.2.2) =
      ∑ y : Fin N × (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) y •
        (X y.2.1).u y.2.2.1 y.2.2.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single α.1]
    · intro ρ' _ hne
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [coS_off plc inj α col (ρ', w) hne, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, sum_coS plc inj α col (fun c y => c • (X y.2.1).u y.2.2.1 y.2.2.2) (fun y => zero_smul _ _)]
  funext x
  rw [Finset.sum_apply]
  have h2 : ∀ g, (Mm r tau gm α col g • (X ((eW r tau N).symm (α, g)).2.1).u ((eW r tau N).symm (α, g)).2.2.1
      ((eW r tau N).symm (α, g)).2.2.2) x = (Gm r tau gm α x.1 g * Mm r tau gm α col g) * e α.2.1 α.2.2 x.2 := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul]
    show Mm r tau gm α col g * (X α.2.1).u g α.2.2 x = _
    rw [hu]
    unfold Gm
    ring
  simp only [h2]
  rw [← Finset.sum_mul, gram_matrix_mul_left gm_hyp α col x.1]
  have h3 : uv (lam r tau plc (α, col)) = e α.2.1 α.2.2 := huv α.2.1 α.2.2 _
  rw [h3]
  split_ifs <;> simp

end Gen

theorem BlockMembershipSelfConjugate.mono {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod 2 → ℕ → ℕ}
    (h : BlockMembershipSelfConjugate X n F FF gaC) (hs : FF ⊆ FF') : BlockMembershipSelfConjugate X n F FF' gaC :=
  fun L h1 h2 pl hpl => hs (h L h1 h2 pl hpl)

section Chart

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem hd_eq_one {ι : T.Fr →+* C} {lab : LabS E C Orb 2} (ha : LabSArith V io ι lab) : lab.hd = 1 := by
  have h := ha.hd_ne
  generalize lab.hd = x at h
  revert x
  decide

theorem gm_mem {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) (t : ZMod 2) (q s : Fin 2) :
    lab.gm o t q s ∈ V.RR := by
  obtain ⟨M, hM⟩ := ha.gm_lim o 0
  have h1 : V.Ge 0 (lab.gm o t q s - emA3 io ι (lab.tau o t) (M q s)) := by simpa using hM t q s
  have h2 := h1.add (hg.em_int o t (M q s))
  rwa [sub_add_cancel] at h2

theorem first_family_subset_image {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by
  intro Po hPo
  refine ⟨subG Dw.mult lab.tau lab.gm plc (∏ o, toAll o (Po o)), hPo, ?_⟩
  exact isImgS_subG plc (fun o => Y.rawSelf (selfOfLab ha hg o))
    (fun (ℓ : LtN Dw n) i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)) (fun o => selfLieBasisVector C3 ι lab o) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) ha.inj (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) _

theorem block_membership_self_conj_charts (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieC Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    BlockMembershipSelfConjugate (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC :=
  (block_membership_self_conj_first Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc h1 h2 h3 first_chern_integral
    (fun o => rdS Y (selfOfLab ha hg) Hy o) F gaC ha.inj (fun o t => by rw [ha.conj o t, hd_eq_one ha])
    (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) (gm_mem ha hg)
    (fun o g x => by
      show (if g = 0 then x.1 else x.1 + lab.hd) = _
      rw [hd_eq_one ha])
    std alt (fun _ => hj) supp tie).mono (first_family_subset_image ha hg a plc)

end Chart

end Formalism.L2.FormalSeriesBounds.RF
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.algHom_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have key : ∀ y, S (pderiv y (p * X i)) = (if i = y then S p else 0) + S (X i) * S (pderiv y p) := by
      intro y
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = y
      · subst h
        simp
      · simp [Pi.single_apply, h]
    conv_lhs => rw [map_mul S p (X i), Derivation.leibniz, hp]
    simp only [key, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    try ring

theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]

private theorem lam_injective_of_tau_injective (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (z z' : AA r tau N × Fin 2) (h : lam r tau plc z = lam r tau plc z') : z = z' := by
  obtain ⟨⟨n1, o1, s1, i1⟩, c1⟩ := z
  obtain ⟨⟨n2, o2, s2, i2⟩, c2⟩ := z'
  injection h with h0 h3
  have h1 : tau o1 s1 = tau o2 s2 := h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (@inj (o1, s1) (o2, s2) h1)
  have h4 : (i1, plc (n1, c1)) = (i2, plc (n2, c2)) := eq_of_heq h3
  obtain ⟨rfl, h5⟩ := Prod.mk.inj h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h5)
  rfl

private theorem pderiv_lam_subG_X_eq_ite (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (α0 : AA r tau N) (col0 : Fin 2) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col0 y.2.2.1) else 0 := by
  unfold subG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_X, map_sum]
  have key : ∀ col : Fin 2, pderiv (lam r tau plc (α0, col0))
      (MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) *
        MvPolynomial.X (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n)) =
      if ((eW r tau N y).1, col) = (α0, col0) then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) else 0 := by
    intro col
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have e1 : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) =
        lam r tau plc ((eW r tau N y).1, col) := rfl
    rw [e1, Pi.single_apply]
    by_cases hz : ((eW r tau N y).1, col) = (α0, col0)
    · rw [if_pos (congrArg (lam r tau plc) hz), if_pos hz, smul_eq_mul, mul_one]
    · rw [if_neg (fun h' => hz (lam_injective_of_tau_injective plc inj _ _ h')), if_neg hz, smul_zero]
  simp only [key]
  by_cases ha : (eW r tau N y).1 = α0
  · simp [ha]
  · simp [ha]

theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval, ← (eW r tau N).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single α0]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_pos rfl] | skip
    exact mul_comm _ _
  · intro α _ hα
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_neg hα] | simp [hα]
    first | exact mul_zero _ | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Chain

end Formalism.L2.FormalSeriesBounds.RF
