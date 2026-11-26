module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.LowerTriangularOverField
open MvPolynomial

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  suffices key : ∀ (k : ℕ) (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 from
    fun a s has => key s.val s rfl a has
  intro k
  induction k with
  | zero =>
    intro s hs a ha
    omega
  | succ k ih =>
    intro s hs a ha
    have hk : k < n := by have := s.isLt; omega
    have h1 := h ⟨k, hk⟩ s (by simpa using hs) a
    have h2 : (∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b < a := (Finset.mem_filter.mp hb).2
      have hba' : b.val < a.val := hba
      exact ih ⟨k, hk⟩ rfl b (by show b.val < k; omega)
    rw [h2, zero_add] at h1
    have h3 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
      Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩)
    omega

theorem lower_triangular_over_field : LowerTriK := by
  intro O K _ _ _ _ _ r n ν Q hQ
  have hlead : ∀ f ∈ dualWeyl K r n ν, f ≠ 0 → LowerTri ((colLex r n).degree f) := fun f hf hf0 =>
    lowerTri_of_interlaced (leadInterlaced K r n ν f hf hf0)
  refine ⟨?_, ?_⟩
  · suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl K r n ν,
        (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → AddMonoidAlgebra.coeff f e ∈ Set.range (algebraMap O K)) →
        (colLex r n).toSyn ((colLex r n).degree f) = d → f ∈ (dualWeyl O r n ν).map (toK O K) by
      intro h
      exact key _ Q hQ h rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hco hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      set m := (colLex r n).degree f with hm
      have hint : Interlaced m := leadInterlaced K r n ν f hf hf0
      have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
        colSums K r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨N, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
      obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant K r n N sz hsz I hmono
      have hbO : bideterminant O sz hsz I ∈ dualWeyl O r n ν := by
        have := bidetMem O r n N sz hsz I
        rw [hshape] at this
        exact this
      have hbK : bideterminant K sz hsz I ∈ dualWeyl K r n ν := by
        have := bidetMem K r n N sz hsz I
        rw [hshape] at this
        exact this
      have hmap : toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I :=
        ldlat_map_bidet (algebraMap O K) sz hsz I
      obtain ⟨c, hc⟩ := hco m (lowerTri_of_interlaced hint)
      have hc' : (colLex r n).leadingCoeff f = algebraMap O K c := hc.symm
      have hcb : (colLex r n).leadingCoeff f • bideterminant K sz hsz I = toK O K (c • bideterminant O sz hsz I) := by
        rw [map_smul, hmap, hc', algebraMap_smul]
      have hcbmem : (colLex r n).leadingCoeff f • bideterminant K sz hsz I ∈ (dualWeyl O r n ν).map (toK O K) := by
        rw [hcb]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ hbO)
      set f' := f - (colLex r n).leadingCoeff f • bideterminant K sz hsz I with hf'
      have hf'mem : f' ∈ dualWeyl K r n ν :=
        Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbK)
      have hdecomp : f = f' + (colLex r n).leadingCoeff f • bideterminant K sz hsz I := by
        rw [hf']; abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ hcbmem
      by_cases h0 : f' = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant K sz hsz I) (hbdeg.trans hexp) hblc h0
      refine ih _ (hd ▸ hlt) f' hf'mem ?_ rfl
      intro e he
      obtain ⟨x, hx⟩ := hco e he
      refine ⟨x - AddMonoidAlgebra.coeff (c • bideterminant O sz hsz I) e, ?_⟩
      have hce : AddMonoidAlgebra.coeff (toK O K (c • bideterminant O sz hsz I)) e = algebraMap O K (AddMonoidAlgebra.coeff (c • bideterminant O sz hsz I) e) :=
        coeff_map (algebraMap O K) _ e
      rw [hf', coeff_sub, hcb, map_sub, hx, hce]
  · intro h
    by_contra hQ0
    exact ((colLex r n).coeff_degree_ne_zero_iff).mpr hQ0 (h _ (hlead Q hQ hQ0))

end Formalism.L2.G.Model.TS
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingDividedAdjoint
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

lemma adj_fockR_of_subset {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ))
    (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring

lemma adj_fockR_add_left {σ R : Type*} [CommRing R] (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [adj_fockR_of_subset _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    adj_fockR_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    adj_fockR_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_add]
  ring

lemma adj_fockR_smul_left {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR (a • f) g = a * fockR f g := by
  rw [adj_fockR_of_subset _ _ f.support MvPolynomial.support_smul, fockR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma adj_fockR_symm {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) :
    fockR f g = fockR g f := by
  classical
  rw [adj_fockR_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    adj_fockR_of_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma adj_fockR_add_right {σ R : Type*} [CommRing R] (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [adj_fockR_symm, adj_fockR_add_left, adj_fockR_symm g, adj_fockR_symm g']

lemma adj_fockR_smul_right {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]

lemma adj_fockR_map {σ R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [adj_fockR_of_subset _ _ f.support (MvPolynomial.support_map_subset _ _), fockR, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp [MvPolynomial.coeff_map]

lemma adj_fockR_rat {σ : Type*} (f g : MvPolynomial σ ℚ) : fockR f g = fockQ f g := rfl

lemma adj_rowDiv_int {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℤ) :
    fockR (rowDiv ℤ a b k f) g = fockR f (rowDiv ℤ b a k g) := by
  apply Int.cast_injective (α := ℚ)
  have e1 := adj_fockR_map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) g
  have e2 := adj_fockR_map (Int.castRingHom ℚ) f (rowDiv ℤ b a k g)
  simp only [eq_intCast] at e1 e2
  rw [← e1, ← e2, ← lclosedeq_rowDiv_map, ← lclosedeq_rowDiv_map, adj_fockR_rat, adj_fockR_rat]
  exact fockQRowDivAdj r n a b k _ _

lemma adj_monomial_eq {σ R : Type*} [CommRing R] (m : σ →₀ ℕ) (c : R) :
    (monomial m c : MvPolynomial σ R) = c • map (Int.castRingHom R) (monomial m (1 : ℤ)) := by
  rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem fock_pairing_divided_adjoint : FockRRowDivAdj := by
  intro R _ r n a b k f g
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m' c' =>
      rw [adj_monomial_eq m c, adj_monomial_eq m' c', rowDiv_smul, rowDiv_smul,
        lclosedeq_rowDiv_map, lclosedeq_rowDiv_map]
      rw [adj_fockR_smul_left, adj_fockR_smul_right, adj_fockR_smul_left, adj_fockR_smul_right,
        adj_fockR_map, adj_fockR_map, adj_rowDiv_int]
    | add g1 g2 h1 h2 =>
      rw [rowDiv_add, adj_fockR_add_right, adj_fockR_add_right, h1, h2]
  | add f1 f2 h1 h2 =>
    rw [rowDiv_add, adj_fockR_add_left, adj_fockR_add_left, h1, h2]

lemma adj_applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) F = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w F) := by
  rfl

lemma adj_applyWord_append {R : Type*} [CommRing R] {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (l1 ++ l2) F = applyWord R l1 (applyWord R l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

lemma adj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

theorem fock_pairing_word_adjoint : FockRWordAdj := by
  intro R _ r n w
  induction w with
  | nil =>
    intro F G
    rfl
  | cons x w ih =>
    intro F G
    rw [adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons,
      adj_applyWord_append]
    rfl

end Formalism.L2.G.Model.TS
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingHighestWeightProof
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

theorem hw_dom {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r)
    (f : MvPolynomial (Fin r × Fin n) B) (hf : f ∈ dualWeyl B r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  rw [standardMonomialSpanDomain B r n ν] at hf
  have key : ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
      intro m hm k
      have h := (bidetDominance B r n K sz hsz I m hm).1 k
      rw [hshape] at h
      exact h
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm
      rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hx m h
      · exact hy m h
    | smul c x _ hx =>
      intro m hm
      exact hx m (support_smul hm)
  intro m hm k
  rw [rowNu_partial_sum ν hnr k]
  exact key m hm k

theorem hw_kill {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) B) (hG : G ∈ dualWeyl B r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv B a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift B (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable B r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := hw_dom ν hn _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

theorem eval_idFrame_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow]
  have h := eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega)
  change eval (idPoint R r n) _ ^ _ = 1
  rw [h, one_pow]

theorem fock_pairing_highest_weight_proof : FockPairingHighestWeight := by
  intro K _ _ r n hn ν hν F hF
  classical
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F with hGdef
  have hG : G ∈ dualWeyl K r n ν := dualWeylRowGraded K r n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG
    (fun a b hab k hk => hw_kill hn ν G hG hGh a b hab k hk)
  have hHW := hwRowWeight K r n hn ν hν
  have h1 : fockR (hw K hn ν) F = fockR (hw K hn ν) G := by
    unfold fockR
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hm))]
  have h2 : fockR (hw K hn ν) G = c * fockR (hw K hn ν) (hw K hn ν) := by
    rw [hc]
    unfold fockR
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]
    ring
  have hcolF : IsWeightedHomogeneous (colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  have hcolH : IsWeightedHomogeneous (colW r n) (hw K hn ν) ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp (hwMem K r n hn ν hν)).1
  have hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idFrame K r n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  have eF := lhwline_diag hn ν F hcolF (idFrame K r n) hD
  have eH := lhwline_diag hn ν (hw K hn ν) hcolH (idFrame K r n) hD
  have hev1 := eval_idFrame_hw K hn ν
  have hDmem : lhwline_mnu hn ν ∈ (hw K hn ν).support := by
    rw [mem_support_iff]
    intro h0
    rw [h0, zero_mul, hev1] at eH
    exact one_ne_zero eH
  have hcoef : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = c * AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) := by
    have e : AddMonoidAlgebra.coeff F (lhwline_mnu hn ν) = AddMonoidAlgebra.coeff G (lhwline_mnu hn ν) := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos (hHW (mem_support_iff.mp hDmem))]
    rw [e, hc, coeff_smul, smul_eq_mul]
  have hevF : eval (idFrame K r n) F = c := by
    rw [eF, hcoef, mul_assoc, ← eH, hev1, mul_one]
  rw [h1, h2, hevF]

end Formalism.L2.G.Model.TS
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

lemma tsact_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  refine Finset.sum_subset h fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

lemma tsact_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [tsact_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    tsact_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma tsact_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [tsact_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    tsact_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tsact_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

lemma tsact_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  rw [tsact_eq_sum (c • f) g f.support MvPolynomial.support_smul]
  unfold fockR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

lemma tsact_zero_left (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 := by
  unfold fockR
  simp

lemma tsact_sum_left {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, F i) g = ∑ i ∈ s, fockR (F i) g := by
  classical
  refine Finset.induction_on s (by simp [tsact_zero_left]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, tsact_add_left, ih]

lemma tsact_sum_right {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR g (∑ i ∈ s, F i) = ∑ i ∈ s, fockR g (F i) := by
  rw [tsact_symm, tsact_sum_left]
  exact Finset.sum_congr rfl fun i _ => tsact_symm _ _

lemma tsact_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [tsact_symm, tsact_smul_left, tsact_symm]

lemma tsact_monomial_left (m : σ →₀ ℕ) (a : R) (h : MvPolynomial σ R) :
    fockR (monomial m a) h = a * h.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp [tsact_zero_left]
  · unfold fockR
    rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

lemma tsact_fact_eq (m : σ →₀ ℕ) (s : Finset σ) (h : m.support ⊆ s) :
    ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ s, (m k).factorial := by
  refine Finset.prod_subset h fun k _ hk => ?_
  have h0 : m k = 0 := by simpa using hk
  rw [h0, Nat.factorial_zero]

lemma tsact_fact_succ (m : σ →₀ ℕ) (v : σ) :
    ∏ k ∈ (m + Finsupp.single v 1).support, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial
      = (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  classical
  have h1 : (m + Finsupp.single v 1).support ⊆ insert v m.support := by
    intro k hk
    rw [Finset.mem_insert]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right
      simpa [Finsupp.mem_support_iff, Finsupp.single_apply, Ne.symm hkv] using hk
  rw [tsact_fact_eq _ _ h1, tsact_fact_eq m (insert v m.support) (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v m.support)]
  have h2 : ∏ k ∈ (insert v m.support).erase v, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v m.support).erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_erase] at hk
    simp [Finsupp.single_apply, Ne.symm hk.1]
  rw [h2]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

lemma tsact_X_mul (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) := by
  classical
  rw [tsact_eq_sum (f * X v) h _ (MvPolynomial.support_mul_X v f).le, Finset.sum_map]
  unfold fockR
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_pderiv, tsact_fact_succ]
  push_cast
  ring

end general

section what₂

variable {R : Type*} [CommRing R] {r n : ℕ}

lemma tsact_rowAct_X (G : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R G (X v) = ∑ b : Fin r, C (G v.1 b) * X (b, v.2) := by
  simp [rowAct]

lemma tsact_coeff_zero (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    AddMonoidAlgebra.coeff (rowAct R G h) 0 = AddMonoidAlgebra.coeff h 0 := by
  show MvPolynomial.constantCoeff (rowAct R G h) = MvPolynomial.constantCoeff h
  induction h using MvPolynomial.induction_on
  next a => simp [rowAct]
  next p q hp hq => simp only [map_add (f := _), hp, hq]
  next p v hp => simp [hp, rowAct]

lemma tsact_chain (G : Matrix (Fin r) (Fin r) R) (b : Fin r) (s : Fin n) (h : MvPolynomial (Fin r × Fin n) R) :
    pderiv (b, s) (rowAct R G h) = ∑ a : Fin r, G a b • rowAct R G (pderiv (a, s) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨c, t⟩ := v
    have hL : pderiv (b, s) (∑ d : Fin r, C (G c d) * X (d, t) : MvPolynomial (Fin r × Fin n) R)
        = if t = s then C (G c b) else 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · simp [hts]
    have hR : ∑ a : Fin r, G a b • (rowAct R G p * rowAct R G (pderiv (a, s) (X (c, t))))
        = rowAct R G p * (if t = s then C (G c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · simp [hts]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), tsact_rowAct_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

end what₂

theorem fock_pairing_row_action : FockRRowAct := by
  intro R _ r n g P
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : rowAct R g (C a : MvPolynomial (Fin r × Fin n) R) = C a := by simp [rowAct]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, tsact_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add (f := _), tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, tsact_rowAct_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, tsact_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : rowAct R g p * (C (g v.1 b) * X (b, v.2)) = g v.1 b • (rowAct R g p * X (b, v.2)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

end Formalism.L2.G.Model.TS
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

lemma fockR_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

lemma fockR_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [fockR_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    fockR_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma fockR_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [fockR_eq_sum _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    fockR_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockR_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_add]; ring

lemma fockR_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  classical
  rw [fockR_eq_sum _ _ f.support (MvPolynomial.support_smul), fockR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_smul, smul_eq_mul]; ring

lemma fockR_add_right (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [fockR_symm, fockR_add_left, fockR_symm g, fockR_symm g']

lemma fockR_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [fockR_symm, fockR_smul_left, fockR_symm g]

lemma fockR_zero_left (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  simp [fockR]

lemma fockR_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ t, f i) g = ∑ i ∈ t, fockR (f i) g := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]

lemma fockR_sum_right {ι : Type*} (t : Finset ι) (f : MvPolynomial σ R) (g : ι → MvPolynomial σ R) :
    fockR f (∑ i ∈ t, g i) = ∑ i ∈ t, fockR f (g i) := by
  rw [fockR_symm, fockR_sum_left]
  exact Finset.sum_congr rfl fun i _ => fockR_symm _ _

lemma fockR_monomial [DecidableEq (σ →₀ ℕ)] (m m' : σ →₀ ℕ) (a b : R) :
    fockR (monomial m a) (monomial m' b) =
      if m = m' then a * b * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) else 0 := by
  classical
  rw [fockR_eq_sum _ _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : m = m'
  · subst h; simp
  · have h' : ¬ m' = m := fun e => h e.symm
    simp [h, h']

lemma fockR_map {S : Type*} [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockR_eq_sum _ _ f.support (support_map_subset φ f), fockR, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_map, map_mul, map_natCast]

end general

section block

variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}

lemma prod_monomial_eq {ι τ : Type*} (t : Finset ι) (e : ι → τ →₀ ℕ) (a : ι → K) :
    ∏ i ∈ t, monomial (e i) (a i) = monomial (∑ i ∈ t, e i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]

def glue (p : S → (Fin k × Fin n →₀ ℕ)) : S × (Fin k × Fin n) →₀ ℕ :=
  ∑ t, (p t).mapDomain (Prod.mk t)

lemma glue_apply (p : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    glue p (s, v) = p s v := by
  classical
  unfold glue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective s) _ _
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hts (congrArg Prod.fst hw)
  · simp

lemma glue_injective : Function.Injective (glue (S := S) (k := k) (n := n)) := fun p q h =>
  funext fun s => Finsupp.ext fun v => by rw [← glue_apply p, h, glue_apply]

lemma fact_univ {τ : Type*} [Fintype τ] (m : τ →₀ ℕ) :
    ∏ x ∈ m.support, (m x).factorial = ∏ x, (m x).factorial := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro x _ hx
  simp [Finsupp.notMem_support_iff.mp hx]

lemma glue_fact (p : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ x ∈ (glue p).support, (glue p x).factorial = ∏ s, ∏ v ∈ (p s).support, (p s v).factorial := by
  rw [fact_univ, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [fact_univ]
  exact Finset.prod_congr rfl fun v _ => by rw [glue_apply]

lemma prod_blockEmb_monomial (p : S → (Fin k × Fin n →₀ ℕ)) (a : S → K) :
    ∏ s, blockEmb K s (monomial (p s) (a s)) = monomial (glue p) (∏ s, a s) := by
  simp only [blockEmb, rename_monomial]
  exact prod_monomial_eq _ _ _

lemma prod_blockEmb_expand [DecidableEq S] (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
      monomial (glue p) (∏ s, AddMonoidAlgebra.coeff (F s) (p s)) := by
  calc ∏ s, blockEmb K s (F s)
      = ∏ s, ∑ m ∈ (F s).support, blockEmb K s (monomial m (AddMonoidAlgebra.coeff (F s) m)) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        conv_lhs => rw [(F s).as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
          ∏ s, blockEmb K s (monomial (p s) (AddMonoidAlgebra.coeff (F s) (p s))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => prod_blockEmb_monomial _ _

lemma fockR_expand {τ : Type*} (f g : MvPolynomial τ K) :
    fockR f g = ∑ m ∈ f.support, ∑ m' ∈ g.support,
      fockR (monomial m (AddMonoidAlgebra.coeff f m)) (monomial m' (AddMonoidAlgebra.coeff g m')) := by
  conv_lhs => rw [f.as_sum, g.as_sum]
  rw [fockR_sum_left]
  exact Finset.sum_congr rfl fun m _ => fockR_sum_right _ _ _

theorem fockR_block (F G : S → MvPolynomial (Fin k × Fin n) K) :
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s) := by
  classical
  rw [prod_blockEmb_expand F, prod_blockEmb_expand G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, glue_fact, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : glue p ≠ glue q := fun e => h (glue_injective e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm

end block

lemma fockR_int_self_pos {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) : 0 < fockR f f := by
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; exact hf (MvPolynomial.support_eq_empty.mp h)
  unfold fockR
  refine Finset.sum_pos (fun m hm => ?_) hne
  have h1 : 0 < f.coeff m * f.coeff m := mul_self_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
  have h2 : (0 : ℤ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℤ) := by
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  exact mul_pos h1 h2

theorem fockR_hw_norm (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) : ∃ N : ℕ, 0 < N ∧
    ∀ (R : Type) [CommRing R], fockR (hw R hn ν) (hw R hn ν) = (N : R) := by
  have pos : 0 < fockR (hw ℤ hn ν) (hw ℤ hn ν) := fockR_int_self_pos _ (hwNe ℤ r n hn ν)
  refine ⟨(fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat, by omega, fun R _ => ?_⟩
  rw [← lclosedeq_hw_map (Int.castRingHom R) hn ν, fockR_map]
  have e : (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) = fockR (hw ℤ hn ν) (hw ℤ hn ν) :=
    Int.toNat_of_nonneg pos.le
  calc (Int.castRingHom R) (fockR (hw ℤ hn ν) (hw ℤ hn ν))
      = (Int.castRingHom R) (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) := by rw [e]
    _ = _ := by rw [eq_intCast, Int.cast_natCast]

theorem fock_pairing_bilinear : FockRBilin := fun _ _ _ f f' g a =>
  ⟨fockR_add_left f f' g, fockR_smul_left a f g, fockR_symm f g⟩

theorem fock_pairing_map : FockRMap := fun _ _ _ _ _ φ f g => fockR_map φ f g

theorem fock_pairing_block : FockRBlock := fun _ _ _ _ _ _ F G => fockR_block F G

theorem highest_weight_norm : HWNorm := fockR_hw_norm

end Formalism.L2.G.Model.TS
end
end
