module

public import Development.EtaleCohomology.DivisorCycles.FinStruct
public import Development.EtaleCohomology.DivisorCycles.FinKey
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid

@[expose] public section

section -- merged from Development.EtaleCohomology.DivisorCycles.FinFinDense
section -- merged from Development.EtaleCohomology.DivisorCycles.FinDensePf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.OpenCosetPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb
end

namespace LateralTheory.Fin.FinDense
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_open_coset_condition_holds_assembled : LateralTheory.DivDb.OpenCoset := by
  apply LateralTheory.DivDb.OpenCoset_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_finite_image_dense_holds_assembled : LateralTheory.DivDb.FinDense := by
  apply LateralTheory.DivDb.FinDense_of <;> first | exact etale_frobenius_charpoly_separable | exact etale_open_coset_condition_holds_assembled
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinDense := etale_finite_image_dense_holds_assembled
end LateralTheory.Fin.FinDense
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinFinPoly
section -- merged from Development.EtaleCohomology.DivisorCycles.FinPolyPf
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinPolyPf

variable {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}

omit [IsAlgClosed K] in
theorem root_sub (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hP : P ≠ 0) (hx : aeval x P = 0) :
    x.charpoly.roots ⊆ P.roots := by
  intro a ha
  rw [Polynomial.mem_roots (Matrix.charpoly_monic x).ne_zero] at ha
  rw [Polynomial.mem_roots hP]
  cases n with
  | zero => simp [Matrix.charpoly, Matrix.det_fin_zero] at ha
  | succ m =>
    have hs : a ∈ spectrum K x := Matrix.mem_spectrum_of_isRoot_charpoly ha
    have h2 := spectrum.subset_polynomial_aeval x P ⟨a, hs, rfl⟩
    rw [hx, spectrum.zero_eq] at h2
    simpa using h2

theorem card_roots_eq (P : K[X]) : Multiset.card P.roots = P.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

theorem cp_card (x : Matrix (Fin n) (Fin n) K) : Multiset.card x.charpoly.roots = n := by
  rw [card_roots_eq, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem eq_of_roots (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hm : P.Monic)
    (h : x.charpoly.roots = P.roots) : x.charpoly = P := by
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic x) (card_roots_eq _),
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (card_roots_eq _), h]

theorem FinPoly_of : FinPoly := by
  intro K _ _ n x P hm hd hx
  have hsub := root_sub x P hm.ne_zero hx
  have hPc : Multiset.card P.roots = n := by rw [card_roots_eq, hd]
  refine ⟨fun hsep => ?_, fun hpg hdet => ?_⟩
  · apply eq_of_roots x P hm
    have hle : x.charpoly.roots ≤ P.roots :=
      (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).2 hsub
    exact Multiset.eq_of_le_of_card_le hle (by rw [hPc, cp_card])
  · apply eq_of_roots x P hm
    by_contra hne
    refine hpg.2 _ (fun a ha => hsub ha) (cp_card x) hne ?_
    rw [← Matrix.det_eq_prod_roots_charpoly, hdet,
      (IsAlgClosed.splits P).coeff_zero_eq_prod_roots_of_monic hm, hd, ← mul_assoc, ← pow_add,
      Even.neg_one_pow ⟨n, rfl⟩, one_mul]

end LateralTheory.DivDb.FinPolyPf
end

namespace LateralTheory.Fin.FinPoly
theorem charpoly_eq_of_annihilating_poly_etale_instance : LateralTheory.DivDb.FinPoly := by
  apply LateralTheory.DivDb.FinPolyPf.FinPoly_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinPoly := charpoly_eq_of_annihilating_poly_etale_instance
end LateralTheory.Fin.FinPoly
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinDegAll
section -- merged from Development.EtaleCohomology.DivisorCycles.EntriesCont
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DegAll₂
open LateralTheory.DivDb

theorem entries_cont {Γ K : Type} [TopologicalSpace Γ] [TopologicalSpace K] {N : ℕ}
    {φ : Γ → Mat K N} (hφ : Continuous φ) :
    Continuous (fun g => fun p : Fin N × Fin N => φ g p.1 p.2) :=
  continuous_pi fun p => (hφ.matrix_elem p.1 p.2)

theorem poly_cont {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {N : ℕ} {φ : Γ → Mat K N} (hφ : Continuous φ) (f : MP K N) :
    Continuous (fun g => MvPolynomial.aeval (fun p : Fin N × Fin N => φ g p.1 p.2) f) := by
  refine ((MvPolynomial.continuous_eval f).comp (entries_cont hφ)).congr ?_
  intro g
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

end LateralTheory.DivDb.DegAll₂

namespace LateralTheory.DivDb

theorem DegAll_of (hP : DegPoly) : DegAll := by
  intro Γ K _ _ _ _ _ _ N n ρ hρ S hS hSd g
  obtain ⟨𝓕, h𝓕⟩ := hP K N n
  rw [h𝓕 K]
  intro f hf
  have key := Continuous.ext_on hS (DegAll₂.poly_cont hρ f) continuous_const
    (fun s hs => ((h𝓕 K _).1 (hSd s hs)) f hf)
  exact congrFun key g

end LateralTheory.DivDb
end

namespace LateralTheory.Fin.DegAll
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_rep_image_degree_bound_all_holds_assembled : LateralTheory.DivDb.DegAll := by
  apply LateralTheory.DivDb.DegAll_of <;> first | exact etale_degree_polynomial_bound
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DegAll := etale_rep_image_degree_bound_all_holds_assembled
end LateralTheory.Fin.DegAll
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinBigCorner
section -- merged from Development.EtaleCohomology.DivisorCycles.BigCorner2
open Matrix

namespace LateralTheory.DivDb.BigCorner₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N n : ℕ}

def gens (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x | ∃ a ∈ A, ∃ g, x = a * (ρ g : Mat C N)}

lemma rmul (ρ : Γ →* GL (Fin N) C) (g h : Γ) : (ρ (g * h) : Mat C N) = ρ g * ρ h := by simp

lemma rone (ρ : Γ →* GL (Fin N) C) : (ρ 1 : Mat C N) = 1 := by simp

lemma rinv (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g : Mat C N) * ρ g⁻¹ = 1 := by
  rw [← rmul, mul_inv_cancel, rone]

lemma rinv' (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g⁻¹ : Mat C N) * ρ g = 1 := by
  rw [← rmul, inv_mul_cancel, rone]

lemma span_mul (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A)
    (x y : Mat C N) (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) :=
  _root_.UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul ρ A hN x y hx hy

lemma one_mem_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) :
    (1 : Mat C N) ∈ Submodule.span C (gens ρ A) :=
  Submodule.subset_span ⟨1, A.one_mem, 1, by rw [rone, one_mul]⟩

noncomputable def RR (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) :
    Subalgebra C (Mat C N) :=
  (Submodule.span C (gens ρ A)).toSubalgebra (one_mem_span ρ A) (span_mul ρ A hN)

lemma mem_RR {ρ : Γ →* GL (Fin N) C} {A : Subalgebra C (Mat C N)} {hN : Normd ρ A} {x : Mat C N} :
    x ∈ RR ρ A hN ↔ x ∈ Submodule.span C (gens ρ A) := Iff.rfl

lemma corner_gen (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ gens ρ A) : ∃ c : C, p i * x * p i = c • p i := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  by_cases h : p i * a * (ρ g : Mat C N) * p i = 0
  · exact ⟨0, by rw [zero_smul, ← mul_assoc, h]⟩
  · obtain ⟨w, hw, hpw⟩ := hyp g i ⟨a, ha, h⟩
    have ha' : (ρ g⁻¹ : Mat C N) * a * ρ g ∈ A := by simpa using hN g⁻¹ a ha
    have e1 : a * (ρ g : Mat C N) = ρ g * ((ρ g⁻¹ : Mat C N) * a * ρ g) := by
      simp only [← mul_assoc, rinv, one_mul]
    obtain ⟨c, hc⟩ := hC.2 _ (A.mul_mem hw ha') i
    refine ⟨c, ?_⟩
    rw [e1, ← mul_assoc, ← mul_assoc, hpw, ← hc]; simp only [mul_assoc]

lemma corner_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∃ c : C, p i * x * p i = c • p i := by
  induction hx using Submodule.span_induction with
  | mem x hx' => exact corner_gen ρ A p hC hN hyp i hx'
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨c, hc⟩ := hu; obtain ⟨d, hd⟩ := hv
    exact ⟨c + d, by rw [mul_add, add_mul, hc, hd, add_smul]⟩
  | smul c u _ hu =>
    obtain ⟨d, hd⟩ := hu
    exact ⟨c * d, by rw [mul_smul_comm, smul_mul_assoc, hd, smul_smul]⟩

lemma normd_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) (g : Γ)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) :
    (ρ g : Mat C N) * x * (ρ g⁻¹ : Mat C N) ∈ Submodule.span C (gens ρ A) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, h, rfl⟩ := hx'
    refine Submodule.subset_span ⟨(ρ g : Mat C N) * a * ρ g⁻¹, hN g a ha, g * h * g⁻¹, ?_⟩
    have key : (ρ g⁻¹ : Mat C N) * (ρ g * (ρ h * ρ g⁻¹)) = ρ h * ρ g⁻¹ := by
      rw [← mul_assoc, rinv', one_mul]
    rw [rmul, rmul]; simp only [mul_assoc, key]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hu

lemma keeps_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hK : Keeps ρ A)
    (W : Submodule C (Fin N → C)) (hW : ∀ g, ∀ v ∈ W, (ρ g : Mat C N) *ᵥ v ∈ W)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∀ v ∈ W, x *ᵥ v ∈ W := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, g, rfl⟩ := hx'
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    exact hK W hW a ha _ (hW g v hv)
  | zero => intro v _; simp
  | add u v _ _ hu hv => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hu w hw) (hv w hw)
  | smul c u _ hu => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hu w hw)

end LateralTheory.DivDb.BigCorner₂

open LateralTheory.DivDb.BigCorner₂ in
theorem LateralTheory.DivDb.BigCorner₂.BigCorner_of : LateralTheory.DivDb.BigCorner := by
  intro Γ C _ _ N n ρ A p hC hN hK hyp
  refine ⟨RR ρ A hN, fun g => ?_, ⟨fun i => ?_, fun a ha i => ?_⟩, fun g a ha => ?_, fun W hW a ha => ?_⟩
  · exact mem_RR.2 (Submodule.subset_span ⟨1, A.one_mem, g, (one_mul _).symm⟩)
  · exact mem_RR.2 (Submodule.subset_span ⟨p i, hC.1 i, 1, by rw [rone, mul_one]⟩)
  · exact corner_span ρ A p hC hN hyp i (mem_RR.1 ha)
  · exact mem_RR.2 (normd_span ρ A hN g (mem_RR.1 ha))
  · exact keeps_span ρ A hK W hW (mem_RR.1 ha)
end

namespace LateralTheory.Fin.BigCorner
theorem etale_big_corner_statement_holds_assembled : LateralTheory.DivDb.BigCorner := by
  apply LateralTheory.DivDb.BigCorner₂.BigCorner_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.BigCorner := etale_big_corner_statement_holds_assembled
end LateralTheory.Fin.BigCorner
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinRep
section -- merged from Development.EtaleCohomology.DivisorCycles.MinCongr
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.RepPf

variable {C : Type} [Field C] {N n : ℕ}

section
variable (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N)

noncomputable def coef (a : Mat C N) (i j : Fin n) : C := by
  classical
  exact if h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j then h.choose else 0

lemma coef_zero {a : Mat C N} {i j : Fin n} (h : E i j = 0) : coef p E a i j = 0 := by
  unfold coef
  rw [dite_eq_right]
  rintro ⟨c, hc, -⟩
  exact hc h

variable {p E}

lemma coef_spec {R : Subalgebra C (Mat C N)} (hM : MUnits R p E) {a : Mat C N} (ha : a ∈ R)
    (i j : Fin n) : p i * a * p j = coef p E a i j • E i j := by
  obtain ⟨c, hc⟩ := hM.2.2.2.2.2 a ha i j
  by_cases hE : E i j = 0
  · rw [hc, hE, smul_zero, smul_zero]
  · have h : ∃ c : C, E i j ≠ 0 ∧ p i * a * p j = c • E i j := ⟨c, hE, hc⟩
    unfold coef
    rw [dite_eq_left h]
    exact h.choose_spec.2

lemma E_left {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    p i * E i j = E i j := by
  calc p i * E i j = p i * (p i * E i j * p j) := by rw [hM.2.2.1 i j]
    _ = (p i * p i) * E i j * p j := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem i).eq, hM.2.2.1 i j]

lemma E_right {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    E i j * p j = E i j := by
  calc E i j * p j = (p i * E i j * p j) * p j := by rw [hM.2.2.1 i j]
    _ = p i * E i j * (p j * p j) := by simp only [mul_assoc]
    _ = E i j := by rw [(hp.1.idem j).eq, hM.2.2.1 i j]

lemma expand (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, (p i * a * p j) * (p j * b * p k) := by
  have h : ∀ j, (p i * a * p j) * (p j * b * p k) = p i * a * p j * b * p k := by
    intro j
    calc (p i * a * p j) * (p j * b * p k) = p i * a * (p j * p j) * b * p k := by
          simp only [mul_assoc]
      _ = _ := by rw [(hp.1.idem j).eq]
  simp only [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hp.1.complete, mul_one]
  simp only [mul_assoc]

lemma coef_mul {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a b : Mat C N}
    (ha : a ∈ R) (hb : b ∈ R) (i k : Fin n) :
    coef p E (a * b) i k = ∑ j, coef p E a i j * coef p E b j k := by
  by_cases hik : E i k = 0
  · rw [coef_zero p E hik]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : E i j = 0
    · rw [coef_zero p E hij, zero_mul]
    by_cases hjk : E j k = 0
    · rw [coef_zero p E hjk, mul_zero]
    exact absurd hik (hM.2.2.2.2.1 i j k hij hjk).2
  · apply smul_left_injective C hik
    simp only
    rw [← coef_spec hM (R.mul_mem ha hb), expand hp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coef_spec hM ha, coef_spec hM hb, smul_mul_smul_comm]
    by_cases hij : E i j = 0
    · simp [hij, coef_zero p E hij]
    by_cases hjk : E j k = 0
    · simp [hjk, coef_zero p E hjk]
    rw [(hM.2.2.2.2.1 i j k hij hjk).1]

lemma coef_one {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (i j : Fin n) :
    coef p E 1 i j = (1 : Matrix (Fin n) (Fin n) C) i j := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    have hE : E i i ≠ 0 := by rw [hM.2.1 i]; exact hp.2 i
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, one_smul, mul_one, (hp.1.idem i).eq, hM.2.1 i]
  · rw [Matrix.one_apply_ne hij]
    by_cases hE : E i j = 0
    · exact coef_zero p E hE
    apply smul_left_injective C hE
    simp only
    rw [← coef_spec hM R.one_mem, zero_smul, mul_one, hp.1.ortho hij]

end

section
variable {p : Fin n → Mat C N} {E : Fin n → Fin n → Mat C N}


variable (E) in
noncomputable def blk (j : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => E i j ≠ 0


variable (E) in
noncomputable def bb (j : Fin n) : Fin n :=
  if h : (blk E j).Nonempty then (blk E j).min' h else j

lemma mem_blk {i j : Fin n} : i ∈ blk E j ↔ E i j ≠ 0 := by
  classical
  unfold blk
  simp

lemma min'_congr {s t : Finset (Fin n)} (h : s.Nonempty) (h' : t.Nonempty) (e : s = t) :
    s.min' h = t.min' h' := by
  subst e; rfl

lemma bb_spec {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    (blk E j).Nonempty ∧ E (bb E j) j ≠ 0 := by
  have hne : (blk E j).Nonempty := ⟨j, mem_blk.2 (by rw [hM.2.1 j]; exact hp.2 j)⟩
  refine ⟨hne, ?_⟩
  unfold bb
  rw [dite_eq_left hne]
  exact mem_blk.1 (Finset.min'_mem _ hne)

lemma bb_ne {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) (j : Fin n) :
    E j (bb E j) ≠ 0 := hM.2.2.2.1 _ _ (bb_spec hp hM j).2

lemma bb_congr {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {i j : Fin n}
    (hij : E i j ≠ 0) : bb E i = bb E j := by
  have e : blk E i = blk E j := by
    ext k
    rw [mem_blk, mem_blk]
    constructor
    · intro hki; exact (hM.2.2.2.2.1 k i j hki hij).2
    · intro hkj; exact (hM.2.2.2.2.1 k j i hkj (hM.2.2.2.1 i j hij)).2
  unfold bb
  rw [dite_eq_left (bb_spec hp hM i).1, dite_eq_left (bb_spec hp hM j).1]
  exact min'_congr _ _ e

lemma mul_E {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (j : Fin n) : a * E j (bb E j) = ∑ i, coef p E a i j • E i (bb E i) := by
  have h1 : a * E j (bb E j) = ∑ i, (p i * a * p j) * E j (bb E j) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hp.1.complete, one_mul, mul_assoc,
      E_left hp hM]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coef_spec hM ha, smul_mul_assoc]
  by_cases hij : E i j = 0
  · simp [hij, coef_zero p E hij]
  rw [(hM.2.2.2.2.1 i j (bb E j) hij (bb_ne hp hM j)).1, bb_congr hp hM hij]


variable (E) in
noncomputable def T (w : Fin N → C) : Matrix (Fin N) (Fin n) C := Matrix.of fun x j => (E j (bb E j) *ᵥ w) x

lemma mul_T (M : Mat C N) (w : Fin N → C) (x : Fin N) (j : Fin n) :
    (M * T E w) x j = ((M * E j (bb E j)) *ᵥ w) x := by
  rw [← Matrix.mulVec_mulVec]
  simp [T, Matrix.mul_apply, Matrix.mulVec, dotProduct]


variable (p E) in
noncomputable def rmat (a : Mat C N) : Matrix (Fin n) (Fin n) C := Matrix.of fun i j => coef p E a i j

lemma T_mul (w : Fin N → C) (a : Mat C N) (x : Fin N) (j : Fin n) :
    (T E w * rmat p E a) x j = ((∑ i, coef p E a i j • E i (bb E i)) *ᵥ w) x := by
  simp [T, rmat, Matrix.mul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, mul_comm]

lemma intertw {R : Subalgebra C (Mat C N)} (hp : Sys p) (hM : MUnits R p E) {a : Mat C N}
    (ha : a ∈ R) (w : Fin N → C) : a * T E w = T E w * rmat p E a := by
  ext x j
  rw [mul_T, T_mul, mul_E hp hM ha]

end

theorem Rep_of : Rep := by
  classical
  intro Γ C _ _ N n ρ R p E hp hM hρ
  let f : Γ →* Matrix (Fin n) (Fin n) C :=
    { toFun := fun g => rmat p E (ρ g : Mat C N)
      map_one' := by
        ext i j
        simp only [map_one, Units.val_one]
        exact coef_one hp hM i j
      map_mul' := by
        intro g h
        ext i k
        simp only [map_mul, Units.val_mul]
        rw [Matrix.mul_apply]
        exact coef_mul hp hM (hρ g) (hρ h) i k }
  let r : Γ →* GL (Fin n) C := f.toHomUnits
  have hcol : ∀ k, ∃ v : Fin N → C, p k *ᵥ v = v ∧ v ≠ 0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    apply hp.2 k
    ext x c
    have h1 := hcon (p k *ᵥ Pi.single c 1) (by rw [Matrix.mulVec_mulVec, (hp.1.idem k).eq])
    have h2 := congrFun h1 x
    simpa [Matrix.mulVec_single_one] using h2
  choose v hv using hcol
  let w0 := ∑ k, v k
  have hw : ∀ k, p k *ᵥ w0 = v k := by
    intro k
    simp only [w0, Matrix.mulVec_sum]
    rw [Finset.sum_eq_single k]
    · exact (hv k).1
    · intro m _ hmk
      rw [← (hv m).1, Matrix.mulVec_mulVec, hp.1.ortho (Ne.symm hmk), Matrix.zero_mulVec]
    · simp
  have hu : ∀ k, ∃ u : Fin N → C, u ⬝ᵥ v k = 1 := by
    intro k
    obtain ⟨x, hx⟩ := Function.ne_iff.1 (hv k).2
    have hx' : v k x ≠ 0 := hx
    exact ⟨Pi.single x (v k x)⁻¹, by simp [hx']⟩
  choose u hu using hu
  let A := T E w0
  let B : Matrix (Fin n) (Fin N) C := Matrix.of fun j x => (u (bb E j) ᵥ* E (bb E j) j) x
  refine ⟨r, A, B, ?_, ?_, ?_⟩
  · ext j k
    have hprod : E (bb E j) j * E k (bb E k) = if j = k then p (bb E j) else 0 := by
      split_ifs with h
      · subst h
        rw [(hM.2.2.2.2.1 _ j _ (bb_spec hp hM j).2 (bb_ne hp hM j)).1, hM.2.1]
      · rw [← E_right hp hM (bb E j) j, ← E_left hp hM k (bb E k)]
        calc E (bb E j) j * p j * (p k * E k (bb E k))
            = E (bb E j) j * (p j * p k) * E k (bb E k) := by simp only [mul_assoc]
          _ = 0 := by rw [hp.1.ortho h, mul_zero, zero_mul]
    have hBA : (B * A) j k = (u (bb E j) ᵥ* E (bb E j) j) ⬝ᵥ (E k (bb E k) *ᵥ w0) := rfl
    rw [hBA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hprod]
    split_ifs with h
    · rw [hw, hu, h, Matrix.one_apply_eq]
    · rw [Matrix.zero_mulVec, dotProduct_zero, Matrix.one_apply_ne h]
  · intro g
    exact intertw hp hM (hρ g) w0
  · intro Z hZ
    have hZE : ∀ j, Z * E j (bb E j) = 0 := by
      intro j
      rw [Matrix.ext_iff_mulVec]
      intro w
      have h1 := hZ (T E w) (fun g => intertw hp hM (hρ g) w)
      ext x
      have h2 := congrFun (congrFun h1 x) j
      rw [mul_T] at h2
      simpa using h2
    have hZp : ∀ j, Z * p j = 0 := by
      intro j
      have h3 : E j (bb E j) * E (bb E j) j = p j := by
        rw [(hM.2.2.2.2.1 j (bb E j) j (bb_ne hp hM j) (bb_spec hp hM j).2).1, hM.2.1 j]
      rw [← h3, ← mul_assoc, hZE j, zero_mul]
    calc Z = Z * ∑ j, p j := by rw [hp.1.complete, mul_one]
      _ = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun j _ => hZp j

end LateralTheory.DivDb.RepPf
end

namespace LateralTheory.Fin.Rep
theorem etale_representation_realization_instance : LateralTheory.DivDb.Rep := by
  apply LateralTheory.DivDb.RepPf.Rep_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Rep := etale_representation_realization_instance
end LateralTheory.Fin.Rep
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinSemis
namespace LateralTheory.Fin.Semis
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Semis := etale_semisimplicity_instance
end LateralTheory.Fin.Semis
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinMatUnits
namespace LateralTheory.Fin.MatrixUnits₂
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.MatrixUnits₂ := etale_matrix_units_system_of_key
end LateralTheory.Fin.MatrixUnits₂
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinDenseAlg
section -- merged from Development.EtaleCohomology.DivisorCycles.DenseAlg2
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.DenseAlg₂
open LateralTheory.DivDb

variable {C : Type} [Field C]

theorem pow_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) : ∀ k : ℕ, y ^ k * T = T * z ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, pow_intertwine y z T h k,
      Matrix.mul_assoc]

theorem aeval_intertwine {N n : ℕ} (y : Mat C N) (z : Mat C n) (T : Matrix (Fin N) (Fin n) C)
    (h : y * T = T * z) (q : C[X]) : aeval y q * T = T * aeval z q := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, pow_intertwine y z T h k]

theorem sep_of_roots {n : ℕ} (q : C[X]) (hm : q.Monic) (hd : q.natDegree = n) (l : Fin n → C)
    (hl : Function.Injective l) (hr : ∀ j, q.IsRoot (l j)) : q.Separable := by
  classical
  have hq0 : q ≠ 0 := hm.ne_zero
  have hnd : ((Finset.univ : Finset (Fin n)).val.map l).Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : (Finset.univ : Finset (Fin n)).val.map l ≤ q.roots := (Multiset.le_iff_subset hnd).2 fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hr j)
  have hcs : Multiset.card ((Finset.univ : Finset (Fin n)).val.map l) = n := by simp
  have heq : (Finset.univ : Finset (Fin n)).val.map l = q.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcs, ← hd]; exact card_roots' q)
  have hcard : Multiset.card q.roots = q.natDegree := by rw [← heq, hcs, hd]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
  rw [← heq, Multiset.map_map] at hprod
  have e : (∏ j, (X - Polynomial.C (l j))) = q := by rw [← hprod, Finset.prod_eq_multiset_prod]; rfl
  exact e ▸ separable_prod_X_sub_C_iff.2 hl

theorem isRoot_of_aeval {N : ℕ} (y : Mat C N) (q : C[X]) (hq : aeval y q = 0) (l : C)
    (hl : y.charpoly.IsRoot l) : q.IsRoot l := by
  have h1 : l ∈ spectrum C y := Matrix.mem_spectrum_of_isRoot_charpoly hl
  have h2 := spectrum.subset_polynomial_aeval y q ⟨l, h1, rfl⟩
  rw [hq, spectrum.mem_iff, sub_zero] at h2
  by_contra hne
  exact h2 ((IsUnit.mk0 (q.eval l) hne).map (algebraMap C (Mat C N)))

theorem DenseAlg_of (hCh : Chain) (hSP : SepPoly) : DenseAlg := by
  intro Γ C _ _ _ N n ρ r A B hSub U g m hm hE
  obtain ⟨hBA, hint, hspan⟩ := hSub
  have hr : ∀ h : Γ, B * (ρ h : Mat C N) * A = (r h : Mat C n) := fun h => by
    rw [Matrix.mul_assoc, hint h, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hgu : ∀ u : Γ, (ρ g : Mat C N) * (ρ u : Mat C N) = (ρ (g * u) : Mat C N) := fun u => by
    rw [map_mul, Units.val_mul]
  by_contra hno
  push Not at hno
  obtain ⟨f, hf⟩ := hSP C n
  let φ : Mat C N →ₗ[C] Mat C n :=
    { toFun := fun x => B * (ρ g : Mat C N) * x * A
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  obtain ⟨f', hf', -⟩ := hCh C N n φ f
  have hz : ¬ (φ m).charpoly.Separable := by
    rw [hf, not_not, ← hf']
    refine hm f' fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
    rw [hf']
    have hφu : φ (((Units.coeHom (Mat C N)).comp ρ) u) = (r (g * u) : Mat C n) := by
      show B * (ρ g : Mat C N) * (ρ u : Mat C N) * A = _
      rw [Matrix.mul_assoc B, hgu, hr]
    rw [hφu]
    by_contra h
    exact hno u hu ((hf _).2 h)
  have hyT : ∀ T : Matrix (Fin N) (Fin n) C, (∀ h, (ρ h : Mat C N) * T = T * (r h : Mat C n)) →
      ((ρ g : Mat C N) * m) * T = T * φ m := by
    intro T hT
    let ψ : Mat C N →ₗ[C] Mat C N :=
      { toFun := fun x => ((ρ g : Mat C N) * x * T - T * (B * (ρ g : Mat C N) * x * A)) * B
        map_add' := fun x y => by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]; abel
        map_smul' := fun c x => by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, RingHom.id_apply, smul_sub] }
    have hψ : ψ m = 0 := by
      ext i j
      obtain ⟨f2, hf2, -⟩ := hCh C N N ψ (MvPolynomial.X (i, j))
      have h0 : ev m f2 = 0 := by
        refine hm f2 fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.1 hx
        rw [hf2]
        have hψu : ψ (((Units.coeHom (Mat C N)).comp ρ) u) = 0 := by
          show (((ρ g : Mat C N) * (ρ u : Mat C N) * T -
            T * (B * (ρ g : Mat C N) * (ρ u : Mat C N) * A)) * B) = 0
          rw [Matrix.mul_assoc B, hgu, hr, hT, sub_self, Matrix.zero_mul]
        rw [hψu]; simp [ev]
      rw [hf2] at h0
      simpa [ev] using h0
    have h2 : ((ρ g : Mat C N) * m * T - T * φ m) * B * A = 0 := by
      have e : ψ m = ((ρ g : Mat C N) * m * T - T * φ m) * B := rfl
      rw [← e, hψ, Matrix.zero_mul]
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one] at h2
    exact sub_eq_zero.1 h2
  have hqy : aeval ((ρ g : Mat C N) * m) (φ m).charpoly = 0 := by
    apply hspan
    intro T hT
    rw [aeval_intertwine _ _ T (hyT T hT), Matrix.aeval_self_charpoly, Matrix.mul_zero]
  obtain ⟨l, hl, hlr⟩ := hE
  exact hz (sep_of_roots _ (Matrix.charpoly_monic _) (by simp [Matrix.charpoly_natDegree_eq_dim]) l hl
    fun j => isRoot_of_aeval _ _ hqy (l j) (hlr j))

end LateralTheory.DivDb.DenseAlg₂
end

namespace LateralTheory.Fin.DenseAlg
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_rep_dense_algebraic_hull_holds_assembled : LateralTheory.DivDb.DenseAlg := by
  apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DenseAlg := etale_rep_dense_algebraic_hull_holds_assembled
end LateralTheory.Fin.DenseAlg
end

section -- merged from Development.EtaleCohomology.DivisorCycles.Imports
section -- merged from Development.EtaleCohomology.DivisorCycles.DivPlus
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb


open Polynomial in
def DivPlus : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (N n : ℕ) (ρ : Γ →* GL (Fin N) K),
      Continuous (fun g : Γ => (ρ g : Matrix (Fin N) (Fin N) K)) → IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic ∧ (P s).natDegree = n) →
      (∀ s ∈ S, aeval (ρ s : Matrix (Fin N) (Fin N) K) (P s) = 0) →
    ∀ (X : Matrix (Fin N) (Fin N) K'), InLieZar ρ X →
      (∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)) →
    ∀ (ψ : Γ →* Kˣ), Continuous (fun g : Γ => ((ψ g : Kˣ) : K)) →
      (∀ s ∈ S, ((ψ s : Kˣ) : K) = (-1) ^ n * (P s).coeff 0) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∃ A : Matrix (Fin N) (Fin n) K, A.rank = n ∧
        ∀ g : Γ, (ρ g : Matrix (Fin N) (Fin N) K) * A = A * (r g : Matrix (Fin n) (Fin n) K)) ∧
      (∀ g : Γ, aeval (ρ g : Matrix (Fin N) (Fin N) K) (r g : Matrix (Fin n) (Fin n) K).charpoly = 0) ∧
      (∀ s ∈ S, aeval (r s : Matrix (Fin n) (Fin n) K) (P s) = 0) ∧
      (∀ g : Γ, ((r g : Matrix (Fin n) (Fin n) K).det) = ((ψ g : Kˣ) : K)) ∧
      IsOpen {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      Dense {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      (∀ s ∈ S, ProdGen n (P s) → (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
        (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧
        (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧ ∑ j, T' j * T j = 1

theorem plus_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivPlus := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨e, -, hL, hr⟩ := he
  obtain ⟨X₀, e₀, hX₀, hL₀, hr₀⟩ := hSpec Γ K K' N n ρ X e hX hL hr
  have hd : ∀ g, Deg n (ρ g : Mat K N) := hDeg Γ K N n ρ hρ S hS fun s hs =>
    ⟨P s, (hP s hs).1.ne_zero, (hP s hs).2.le, hk s hs⟩
  obtain ⟨p, hG⟩ := hStruct Γ K N n ρ X₀ e₀ hss hd hX₀ hL₀ hr₀
  have key := hKey Γ K N n ρ e₀ p hd hL₀ hG
  obtain ⟨hsys, -, hC, -, hN, hK, -⟩ := hG
  obtain ⟨R, hR, hRC, hRN, hRK⟩ := hBig Γ K N n ρ (env ρ) p hC hN hK
    fun g => (key ⊤ inferInstance inferInstance g).2
  obtain ⟨E, hE⟩ := hMU K N n R p hsys hRC (hSemis Γ K N ρ R hss hRN hRK)
  obtain ⟨r, A, B, hsub⟩ := hRep Γ K N n ρ R p E hsys hE hR
  obtain ⟨h1, h2, h3, h4⟩ := hSub Γ K N n ρ r A B hsub hss
  have hc : Continuous (fun g => (r g : Mat K n)) := by
    simp only [h3]
    exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const
  obtain ⟨ho, hD⟩ := hFD Γ K n r hc fun U hU hf g => by
    obtain ⟨m, hm, hE⟩ := (key U hU hf g).1
    exact hDA Γ K N n ρ r A B hsub U g m hm hE
  have hkr : ∀ s ∈ S, Polynomial.aeval (r s : Mat K n) (P s) = 0 := fun s hs => (h4 s _).1 (hk s hs)
  have hsep : ∀ s ∈ S, (r s : Mat K n).charpoly.Separable → (r s : Mat K n).charpoly = P s := fun s hs =>
    (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).1
  have hdet : ∀ g, (r g : Mat K n).det = ((ψ g : Kˣ) : K) := by
    have := Continuous.ext_on (hS.inter_of_isOpen_right hD ho) hc.matrix_det hψ (fun s hs => by
      show (r s : Mat K n).det = _
      rw [hψS s hs.1, Matrix.det_eq_sign_charpoly_coeff, hsep s hs.1 hs.2, Fintype.card_fin])
    exact fun g => congrFun this g
  refine ⟨r, hc, h1, ⟨A, h2, hsub.2.1⟩, fun g => (h4 g _).2 (Matrix.aeval_self_charpoly _), hkr, hdet, ho, hD,
    hsep, fun s hs hg => (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).2 hg ?_, hEm Γ K N n ρ r A B hsub hss h1⟩
  rw [hdet, hψS s hs]

end LateralTheory.DivDb
end

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivWCoreLac := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, k, T, T', hT, -, hs⟩ :=
    plus_of hSpec hDeg hStruct hKey hBig hSemis hMU hRep hDA hSub hFD hFP hEm
      Γ K K' N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  refine ⟨r, h1, h2, h3, ⟨k, Matrix.of fun q a => T q.2 q.1 a, ?_, fun g => ?_⟩, h4, h5, h6, h7, h8, h9, h10⟩
  · have hC : (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1) *
        (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a) = 1 := by
      rw [← hs]; ext a b
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Fintype.sum_prod_type_right]
    refine le_antisymm ((Matrix.rank_le_card_width _).trans (by simp)) ?_
    have := Matrix.rank_mul_le_right (Matrix.of fun a (q : Fin n × Fin k) => T' q.2 a q.1)
      (Matrix.of fun (q : Fin n × Fin k) a => T q.2 q.1 a)
    rw [hC] at this
    simpa using this
  · ext ⟨i, j⟩ a
    have := congrFun (congrFun (hT j g) i) a
    simp only [Matrix.mul_apply] at this
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, this]

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinSpecLie
section -- merged from Development.EtaleCohomology.DivisorCycles.SpecLiePf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.SpecLiePf
open LateralTheory.DivDb

theorem SpecLie_of (hS : SpecPt) : SpecLie := by
  intro Γ K K' _ _ _ _ _ N n ρ X e hX hL hR
  classical
  let x : (Fin N × Fin N) ⊕ Fin n → K' := Sum.elim (fun p => X p.1 p.2) e
  let gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := fun A B =>
    MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) -
      MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)
  let G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
    {g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}
  have hGf : G.Finite :=
    (Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset
      (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)
  have haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g ⟨A, B, hA, hB, hAB, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]
    exact sub_ne_zero.mpr (hL A B hA hB hAB)
  obtain ⟨y, hy, hyG⟩ := hS K K' _ x G hGf haG
  refine ⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩
  · change ∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0
    intro f hf
    have hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0 :=
      fun g => hf _ ⟨g, trivial, rfl⟩
    have h0 := hX f hf'
    let L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := ∑ p : Fin N × Fin N,
      MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2)
        (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)
    have hxL : MvPolynomial.aeval x L = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl] using h0
    have h1 := hy L hxL
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply] using h1
  · intro A B hA hB hAB
    have h1 := hyG _ ⟨A, B, hA, hB, hAB, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    exact sub_ne_zero.mp h1
  · intro i
    let M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
      Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))
    have hx : MvPolynomial.aeval x M.det = 0 := by
      have e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det := by
        rw [← RingHom.map_det]; rfl
      have e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X := by
        ext a b
        by_cases h : a = b
        · subst h; simp [M, x]
        · simp [M, x, h]
      rw [e1, e2, ← Matrix.eval_charpoly]; exact hR i
    have h1 := hy _ hx
    have e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det := by
      rw [← RingHom.map_det]
    have e2 : (MvPolynomial.eval y).mapMatrix M =
        Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b))) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [M]
      · simp [M, h]
    rw [e1, e2] at h1
    change Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0
    rw [Matrix.eval_charpoly]; exact h1

end LateralTheory.DivDb.SpecLiePf
end

namespace LateralTheory.Fin.SpecLie
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
end

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

theorem goal_holds : DivWCoreLac :=
  goal_of LateralTheory.Fin.SpecLie.intersectionNumber_baseChange LateralTheory.Fin.DegAll.intersectionNumber_baseChange LateralTheory.Fin.Struct.intersectionNumber_baseChange LateralTheory.Fin.Key.intersectionNumber_baseChange LateralTheory.Fin.BigCorner.intersectionNumber_baseChange LateralTheory.Fin.Semis.intersectionNumber_baseChange LateralTheory.Fin.MatrixUnits₂.intersectionNumber_baseChange LateralTheory.Fin.Rep.intersectionNumber_baseChange LateralTheory.Fin.DenseAlg.intersectionNumber_baseChange LateralTheory.Fin.FinSub.intersectionNumber_baseChange LateralTheory.Fin.FinDense.intersectionNumber_baseChange LateralTheory.Fin.FinPoly.intersectionNumber_baseChange LateralTheory.Fin.FinEmbed.intersectionNumber_baseChange

end LateralTheory.DivDb
