module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMonicSquarefreeUnitConstPolysGe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMonicSquarefreeUnitConstPolysGe
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.SqCount

theorem sq_mul_unique {k : Type} [Field k] {a b c d : k[X]} (ha : a.Monic) (hc : c.Monic)
    (hb : Squarefree b) (hd : Squarefree d) (h : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  obtain ⟨a1, c1, e, hco, rfl, rfl⟩ : ∃ a1 c1 e : k[X], IsCoprime a1 c1 ∧ a = e * a1 ∧ c = e * c1 := by
    obtain ⟨a1, c1, h1, h2, h3⟩ := extract_gcd a c
    exact ⟨a1, c1, GCDMonoid.gcd a c, (gcd_isUnit_iff _ _).1 h3, h1, h2⟩
  have he : e ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have h' : a1 ^ 2 * b = c1 ^ 2 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 2 he)
    linear_combination h
  have u1 : IsUnit a1 := by
    apply hd
    rw [← sq]
    exact (hco.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨b, h'.symm⟩
  have u2 : IsUnit c1 := by
    apply hb
    rw [← sq]
    exact (hco.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨d, h'⟩
  have hac : e * a1 = e * c1 :=
    eq_of_monic_of_associated ha hc ((associated_mul_unit_left e a1 u1).trans (associated_mul_unit_left e c1 u2).symm)
  refine ⟨hac, ?_⟩
  rw [hac] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hc.ne_zero) h

theorem exists_sq_mul {k : Type} [Field k] {f : k[X]} (hf : f.Monic) :
    ∃ a b : k[X], a.Monic ∧ b.Monic ∧ Squarefree b ∧ f = a ^ 2 * b := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hs : Squarefree f
  · exact ⟨1, f, monic_one, hf, hs, by simp⟩
  obtain ⟨x, hx, hu⟩ : ∃ x, x * x ∣ f ∧ ¬ IsUnit x := by
    by_contra hc
    exact hs fun x hx => by_contra fun hu => hc ⟨x, hx, hu⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hx)
  have hy : (normalize x).Monic := monic_normalize hx0
  have hass : Associated (normalize x) x := normalize_associated x
  obtain ⟨h, rfl⟩ := (hass.mul_mul hass).dvd.trans hx
  have hh : h.Monic := (hy.mul hy).of_mul_monic_left hf
  have hpos : 0 < (normalize x).natDegree :=
    natDegree_pos_of_not_isUnit_of_dvd_monic hy (fun hu' => hu (hass.isUnit hu')) dvd_rfl
  rw [(hy.mul hy).natDegree_mul hh, hy.natDegree_mul hy] at hn
  obtain ⟨a, b, ha, hb, hsq, rfl⟩ := ih h.natDegree (by omega) hh rfl
  exact ⟨normalize x * a, b, hy.mul ha, hb, hsq, by ring⟩

variable (g : ℕ) [Fact g.Prime]

noncomputable def monicSet (N : ℕ) : Finset (ZMod g)[X] :=
  Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])

variable {g}

theorem mem_monicSet {N : ℕ} {f : (ZMod g)[X]} : f ∈ monicSet g N ↔ f.Monic ∧ f.natDegree = N := by
  unfold monicSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    have hlt : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < (N : WithBot ℕ) := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hlt, ?_⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [hm.as_sum]
    rw [Finset.sum_range fun i => C (f.coeff i) * X ^ i]

theorem card_monicSet (N : ℕ) : (monicSet g N).card = g ^ N := by
  unfold monicSet
  rw [Finset.card_image_of_injective]
  · simp [ZMod.card]
  · intro c d h
    have h' := add_left_cancel h
    funext i
    have := congrArg (fun p : (ZMod g)[X] => p.coeff i) h'
    simpa [Polynomial.finsetSum_coeff, coeff_X_pow, Fin.val_inj] using this

theorem monic_divX {k : Type} [Field k] {a : k[X]} (ha : a.Monic) (hd : 1 ≤ a.natDegree) : a.divX.Monic := by
  rw [Monic, leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, coeff_divX, Nat.sub_add_cancel hd]
  exact ha

theorem card_zero_const (n : ℕ) : ((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0).card ≤ g ^ n := by
  rw [← card_monicSet]
  refine Finset.card_le_card_of_injOn divX ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_monicSet, Finset.mem_coe] at hf ⊢
    refine ⟨monic_divX hf.1.1 (by omega), ?_⟩
    rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  · intro f hf f' hf' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_monicSet] at hf hf'
    rw [← divX_mul_X_add f, ← divX_mul_X_add f', h, hf.2, hf'.2]

theorem card_not_squarefree (n : ℕ) : ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f).card ≤ g ^ n := by
  rcases n with _ | n
  · rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro f hf
      rw [mem_monicSet] at hf
      rw [not_not]
      exact (irreducible_of_degree_eq_one (by rw [degree_eq_natDegree hf.1.ne_zero, hf.2]; rfl)).squarefree
  have hc : ((Finset.univ : Finset (ZMod g)) ×ˢ monicSet g n).card = g ^ (n + 1) := by
    rw [Finset.card_product, card_monicSet, Finset.card_univ, ZMod.card, pow_succ']
  rw [← hc]
  refine Finset.card_le_card_of_forall_subsingleton
    (fun f p => ∃ a b : (ZMod g)[X], a.Monic ∧ Squarefree b ∧ p.2 = a ^ 2 * b ∧ f = (a * X + C p.1) ^ 2 * b) ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, mem_monicSet] at hf
    obtain ⟨⟨hm, hd⟩, hs⟩ := hf
    obtain ⟨a, b, ha, hb, hsq, rfl⟩ := exists_sq_mul hm
    have h1 : 1 ≤ a.natDegree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [ha.natDegree_eq_zero] at h0
      subst h0
      exact hs (by simpa using hsq)
    have ha' := monic_divX ha h1
    refine ⟨(a.coeff 0, a.divX ^ 2 * b), ?_, a.divX, b, ha', hsq, rfl, by rw [divX_mul_X_add]⟩
    rw [Finset.mem_product, mem_monicSet]
    refine ⟨Finset.mem_univ _, (ha'.pow 2).mul hb, ?_⟩
    rw [(ha.pow 2).natDegree_mul hb, ha.natDegree_pow] at hd
    show (a.divX ^ 2 * b).natDegree = n
    rw [(ha'.pow 2).natDegree_mul hb, ha'.natDegree_pow, natDegree_divX_eq_natDegree_tsub_one]
    omega
  · rintro p - f ⟨-, a, b, ha, hb, h1, rfl⟩ f' ⟨-, c, d, hc, hd, h2, rfl⟩
    obtain ⟨rfl, rfl⟩ := sq_mul_unique ha hc hb hd (h1.symm.trans h2)
    rfl

end GlobalTheory.BadShare.SqCount

open GlobalTheory.BadShare.SqCount in
theorem GlobalTheory.BadShare.card_sqSet_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N →
    (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  intro g _ N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsub : monicSet g (n + 1) ⊆ sqSet g (n + 1) ∪ (((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0) ∪
      ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f)) := by
    intro f hf
    simp only [Finset.mem_union, Finset.mem_filter, mem_sqSet]
    have := mem_monicSet.1 hf
    tauto
  have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_zero_const n) (card_not_squarefree n))) _))
  rw [card_monicSet] at h1
  have h2 : ((g : ℝ)) ^ (n + 1) ≤ ((sqSet g (n + 1)).card : ℝ) + ((g : ℝ) ^ n + (g : ℝ) ^ n) := by exact_mod_cast h1
  rw [Nat.add_sub_cancel]
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMonicSquarefreeUnitConstPolysGeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  first | exact @GlobalTheory.BadShare.card_sqSet_ge | exact GlobalTheory.BadShare.card_sqSet_ge | (intros; apply GlobalTheory.BadShare.card_sqSet_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem one_sub_two_div_le_mass_true :
    ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  intro g hg N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg.out.pos
  have hpow : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hterm : ∀ f ∈ sqSet g N, ((g : ℝ) ^ N)⁻¹ ≤ ((torusCard g f : ℝ))⁻¹ := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf
    have h1' : (0 : ℝ) < (torusCard g f : ℝ) := by exact_mod_cast h1
    have h2' : (torusCard g f : ℝ) ≤ (g : ℝ) ^ N := by exact_mod_cast h2
    exact inv_anti₀ h1' h2'
  have hsum : ((sqSet g N).card : ℝ) * ((g : ℝ) ^ N)⁻¹ ≤ mass g N fun _ => True := by
    have h := Finset.card_nsmul_le_sum (sqSet g N) (fun f => ((torusCard g f : ℝ))⁻¹) _ hterm
    rw [nsmul_eq_mul] at h
    unfold mass
    simpa only [Finset.filter_true] using h
  refine le_trans ?_ hsum
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : (ZMod g)[X]) ∈ sqSet g 0 :=
      (GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree g 0 1).2 ⟨monic_one, natDegree_one, squarefree_one, by simp⟩
    have hc : (1 : ℝ) ≤ ((sqSet g 0).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨_, h1⟩
    have : (0 : ℝ) ≤ 2 / (g : ℝ) := by positivity
    simp only [pow_zero, inv_one, mul_one]
    linarith
  · have hc := GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge g N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hc
    have he : 1 - 2 / (g : ℝ) = ((g : ℝ) ^ (M + 1) - 2 * (g : ℝ) ^ M) * ((g : ℝ) ^ (M + 1))⁻¹ := by
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hpow.le)

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMassStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  first | exact @GlobalTheory.BadShare.one_sub_two_div_le_mass_true | exact GlobalTheory.BadShare.one_sub_two_div_le_mass_true | (intros; apply GlobalTheory.BadShare.one_sub_two_div_le_mass_true <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.PolAct

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def homF (A : Submodule R M) (w : ℕ) : Submodule R ((Fin 2 → R) → M) where
  carrier := {b | ∃ c : Fin (w + 1) → M, (∀ i, c i ∈ A) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
  zero_mem' := ⟨0, fun _ => A.zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c + d, fun i => A.add_mem (hc i) (hd i), fun u => by
      simp [ha, hb, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro r b ⟨c, hc, hb⟩
    exact ⟨r • c, fun i => A.smul_mem r (hc i), fun u => by
      simp only [Pi.smul_apply, hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩

private lemma const_mem_homF_zero {A : Submodule R M} {x : M} (hx : x ∈ A) :
    (fun _ : Fin 2 → R => x) ∈ _root_.GlobalTheory.KZ.PolAct.homF A 0 :=
  ⟨fun _ => x, fun _ => hx, fun u => by simp⟩

private lemma coord_zero_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 0 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨Fin.cons 0 c, fun i => ?_, fun u => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [A.zero_mem]
    · simp [hc]
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, Fin.val_succ,
      Nat.add_sub_add_right, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

private lemma coord_one_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 1 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨fun j => if h : (j : ℕ) < n + 1 then c ⟨j, h⟩ else 0, fun j => ?_, fun u => ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact A.zero_mem
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_self_iff_false,
      dif_neg, not_false_eq_true, smul_zero, add_zero, Fin.eta, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : n + 1 - (i : ℕ) = n - (i : ℕ) + 1 := Nat.sub_add_comm (Nat.lt_succ_iff.mp i.isLt)
    rw [hi, pow_succ]
    congr 1
    ring

private lemma linear_form_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    (fun u => (α * u 0 + β * u 1) • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  have h := (_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).add_mem
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem α
      (coord_zero_smul_mem_homF_succ hb))
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem β
      (coord_one_smul_mem_homF_succ hb))
  convert h using 1
  funext u
  simp [add_smul, mul_smul]

private lemma linear_form_pow_smul_mem_homF_add {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    ∀ k : ℕ, (fun u => (α * u 0 + β * u 1) ^ k • b u) ∈
      _root_.GlobalTheory.KZ.PolAct.homF A (n + k) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := linear_form_smul_mem_homF_succ ih α β
    show _ ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + k + 1)
    convert h using 1
    funext u
    rw [pow_succ, mul_comm]
    exact (smul_smul (α * u 0 + β * u 1)
      ((α * u 0 + β * u 1) ^ k) (b u)).symm

theorem _root_.GlobalTheory.KZ.PolAct.subst_mem {A : Submodule R M} {w : ℕ} (φ : M →ₗ[R] M)
    (hφ : ∀ a ∈ A, φ a ∈ A)
    (m : Matrix (Fin 2) (Fin 2) R) {b : (Fin 2 → R) → M}
    (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A w) :
    (fun u => φ (b (m *ᵥ u))) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
  obtain ⟨c, hc, hbu⟩ := hb
  have hterm : ∀ i : Fin (w + 1), (fun u : Fin 2 → R =>
      ((m 0 0 * u 0 + m 0 1 * u 1) ^ (i : ℕ) * (m 1 0 * u 0 + m 1 1 * u 1) ^ (w - (i : ℕ))) •
        φ (c i)) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
    intro i
    have h0 := const_mem_homF_zero (hφ _ (hc i))
    have h1 := linear_form_pow_smul_mem_homF_add h0 (m 1 0) (m 1 1) (w - i)
    have h2 := linear_form_pow_smul_mem_homF_add h1 (m 0 0) (m 0 1) i
    have hdeg : 0 + (w - (i : ℕ)) + i = w := by
      have := i.isLt
      omega
    rw [hdeg] at h2
    convert h2 using 1
    funext u
    rw [mul_smul]
  have hsum := Submodule.sum_mem (_root_.GlobalTheory.KZ.PolAct.homF A w)
    (t := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  funext u
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hbu, map_sum, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_apply]

theorem _root_.GlobalTheory.KZ.PolAct.act_mem_pol {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l w : ℕ) [Fact l.Prime]
    (m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ a ∈ X.A l, X.kmap l
      (X.sl (_root_.GlobalTheory.KZ.toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w,
      X.act l m b ∈
        X.Pol l w := by
  intro b hb
  exact _root_.GlobalTheory.KZ.PolAct.subst_mem (A := X.A l) (w := w) _ h _ hb

end GlobalTheory.KZ.PolAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ), (∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := by
  first | exact @GlobalTheory.KZ.PolAct.act_mem_pol | exact GlobalTheory.KZ.PolAct.act_mem_pol | (intros; apply GlobalTheory.KZ.PolAct.act_mem_pol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.GalCont

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  X.exp.toRingHom.injective

theorem gal_eq_of_coeff (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K)
    (h : ∀ r, s ((X.exp f).coeff r) = (X.exp f).coeff r) : X.gal s f = f := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  exact h r

theorem coeff_alg (c : Ω) (r : ℚ) :
    ((algebraMap Ω (HahnSeries ℚ Ω)) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  simp [PowerSeries.algebraMap_apply, HahnSeries.coeff_single, eq_comm]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) (hc : s c = c) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K c := by
  apply gal_eq_of_coeff
  intro r
  rw [AlgHom.commutes, coeff_alg]
  split_ifs
  · exact hc
  · exact map_zero s

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply gal_eq_of_coeff
  intro r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

def fixSet (X : Tower Ω ε) : Set X.K :=
  {f | ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f}

def fixField (X : Tower Ω ε) : IntermediateField Ω X.K where
  carrier := fixSet X
  mul_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_mul, hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  add_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_add (f := _), hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  algebraMap_mem' c := ⟨{c}, fun s hs => gal_algebraMap X s c (hs c (Finset.mem_singleton_self c))⟩
  inv_mem' := by
    rintro a ⟨E, hE⟩
    exact ⟨E, fun s hs => by rw [map_inv₀, hE s hs]⟩

theorem adjoin_le_fix (X : Tower Ω ε) : IntermediateField.adjoin Ω {X.jK} ≤ fixField X := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact ⟨∅, fun s _ => gal_j X s⟩

theorem fix_fin (X : Tower Ω ε) (f : X.K) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨q, hq⟩ : ∃ q : Polynomial X.K, q = p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K) := ⟨_, rfl⟩
  have hq0 : q ≠ 0 := hq ▸ (Polynomial.map_ne_zero_iff (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K).injective).2 hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map_algebraMap]; exact hpf
  have hcoef : ∀ i, ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.gal s (q.coeff i) = q.coeff i := by
    intro i
    rw [hq, Polynomial.coeff_map]
    exact adjoin_le_fix X (p.coeff i).2
  choose Ec hEc using hcoef
  have hex : ∀ g : X.K, g ≠ f → ∃ r, (X.exp g).coeff r ≠ (X.exp f).coeff r := by
    intro g hg
    by_contra h
    push_neg at h
    exact hg (exp_inj X (HahnSeries.ext (funext h)))
  choose rr hrr using hex
  let E1 : Finset Ω := q.support.biUnion Ec
  let E2 : Finset Ω := q.roots.toFinset.image
    (fun g => if h : g = f then 0 else (X.exp f).coeff (rr g h))
  refine ⟨E1 ∪ E2, fun s hs => ?_⟩
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ q.support
    · exact hEc i s (fun x hx => hs x (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, hi, hx⟩)))
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
  have hroot : X.gal s f ∈ q.roots := by
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot.def]
    have := Polynomial.eval₂_hom (X.gal s).toRingHom f (p := q)
    rw [← Polynomial.eval_map, hmap] at this
    simpa [hqf] using this
  by_contra hne
  have hmem : (X.exp f).coeff (rr _ hne) ∈ E2 :=
    Finset.mem_image.2 ⟨X.gal s f, Multiset.mem_toFinset.2 hroot, by rw [dite_eq_right hne]⟩
  apply hrr _ hne
  rw [X.gal_exp]
  exact hs _ (Finset.mem_union_right _ hmem)

theorem kmap_sub_mem_of_ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (ha : a ∈ X.ASet l)
    (n : ℕ) : ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) a - a ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  obtain ⟨f, -, hf⟩ := ha n
  obtain ⟨E, hE⟩ := fix_fin X (f : X.K)
  refine ⟨E, fun s hs => ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ a).val n = a.val n
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, hf]
  rw [Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  have hu : Units.map (X.gal s).toMonoidHom f = f := Units.ext (hE s hs)
  congr 2

theorem cyc_sub_one_mem [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - 1) ∈ (idl l) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, fun _ _ => by simp⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  refine ⟨{ζ}, fun s hs => ?_⟩
  have h1 := cyclotomicCharacter.spec l (n := n) s.toRingEquiv ζ hζ.pow_eq_one
  have hsz : s.toRingEquiv ζ = ζ := hs ζ (Finset.mem_singleton_self ζ)
  rw [hsz] at h1
  set v := (cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n with hv
  have h2 : v = 1 := by
    have hlt : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
    have hval : v.val = 1 := hζ.pow_inj (ZMod.val_lt v) hlt (by rw [pow_one]; exact h1.symm)
    rw [← ZMod.natCast_zmod_val v, hval, Nat.cast_one]
  rw [idl, Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, ← hv, h2,
    map_one, sub_self]

theorem kmap_sub_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Khat l) (hc : c ∈ X.A l) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) c - c ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  induction hc using Submodule.span_induction with
  | mem a ha => exact kmap_sub_mem_of_ASet X l a ha n
  | zero => exact ⟨∅, fun s _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs => ?_⟩
    have := Submodule.add_mem _ (hE s fun x hx => hs x (Finset.mem_union_left _ hx))
      (hF s fun x hx => hs x (Finset.mem_union_right _ hx))
    rw [map_add (f := _)]
    convert this using 1
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs => ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ r (hE s hs)

theorem galB_sub_mem_of_Pol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l)
    (hb : b ∈ X.Pol l w) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ∀ u, (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  obtain ⟨c, hcA, hbc⟩ := hb
  choose Ec hEc using fun i => kmap_sub_mem_A X l (c i) (hcA i) n
  obtain ⟨Ez, hEz⟩ := cyc_sub_one_mem (Ω := Ω) l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s (fun x hx => hs x (Finset.mem_union_left _ hx))
  have hk : ∀ i, X.kmap l (X.gal s) (c i) - c i ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
    fun i => hEc i s (fun x hx => hs x (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
  set χ := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχdef
  have hgal : X.galB l s b u = X.kmap l (X.gal s) (b ![u 0, χ * u 1]) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Pi.sub_apply, hgal, hbc, hbc, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  simp only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpow : χ ^ (w - (i : ℕ)) - 1 ∈ (idl l) ^ n := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow χ 1 (w - (i : ℕ))
    rw [one_pow] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ hχ
  have heq : (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i) -
      (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i =
      (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • (X.kmap l (X.gal s) (c i) - c i) +
      ((u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) * (χ ^ (w - (i : ℕ)) - 1)) • c i := by
    rw [mul_pow]
    module
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hk i))
    (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpow) Submodule.mem_top)

theorem galB_cont : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.B N l w, ∀ n : ℕ,
    ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → ∀ u,
      (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ _ _ _ b hb n
  classical
  induction hb using Submodule.span_induction with
  | mem b hb => exact galB_sub_mem_of_Pol X l w b hb.1 n
  | zero => exact ⟨∅, fun s _ u => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs u => ?_⟩
    have := Submodule.add_mem _ (hE s (fun x hx => hs x (Finset.mem_union_left _ hx)) u)
      (hF s (fun x hx => hs x (Finset.mem_union_right _ hx)) u)
    rw [map_add (f := _)]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.add_apply, Pi.sub_apply]
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs u => ?_⟩
    have := Submodule.smul_mem _ r (hE s hs u)
    rw [map_smul]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub]

end GlobalTheory.KZ.GalCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem mono_sub_mem_of_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u v : Fin 2 → R)
    (h : ∀ i, u i - v i ∈ I) (a b : ℕ) : u 0 ^ a * u 1 ^ b - v 0 ^ a * v 1 ^ b ∈ I := by
  have h0 := Ideal.Quotient.eq.2 (h 0)
  have h1 := Ideal.Quotient.eq.2 (h 1)
  rw [← Ideal.Quotient.eq]
  simp only [map_mul, map_pow, h0, h1]

theorem Tower.B_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) (u v : Fin 2 → ℤ_[l])
    (huv : ∀ i, u i - v i ∈ (idl l) ^ n) :
    b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, hc⟩ := hx.1
    rw [hc u, hc v, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← sub_smul]
    exact Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simp only [Pi.add_apply]
    convert this using 1
    abel
  | smul r x _ hx =>
    simp only [Pi.smul_apply, ← smul_sub]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongrStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.Tower.B_sub_mem | exact GlobalTheory.KZ.Tower.B_sub_mem | (intros; apply GlobalTheory.KZ.Tower.B_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExteriorTensorProductConvolutionCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExteriorTensorProductConvolutionCalculus
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_tens {ι G : Type} [Fintype ι] [Group G] [Fintype G] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem conv_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ring

theorem tens_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  intro ι G G' _ _ _ _ _
  refine ⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_,
    fun a a' b b' => ⟨?_, ?_⟩⟩
  · rw [conv_tens]
    congr 1
    funext v
    exact (h v).1
  · simp only [tens, map_prod]
    exact Finset.prod_congr rfl fun v _ => (h v).2 (x v)
  · rw [conv_tens2, ha.1, hb.1]
  · simp only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]
  · funext ⟨x, y⟩
    simp only [tens2, dirac, Prod.mk_eq_one]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]
  · funext x
    simp only [tens2, Pi.sub_apply, sub_mul]
  · funext x
    simp only [tens2, Pi.sub_apply, mul_sub]

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExteriorTensorProductConvolutionCalculusStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorTensorProduct_convolution_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  first | exact @GlobalTheory.BadShare.tens_calculus | exact GlobalTheory.BadShare.tens_calculus | (intros; apply GlobalTheory.BadShare.tens_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInv
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInv
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory

theorem hahn_pow_neg_one_lead {R : Type} [CommRing R] (x : HahnSeries ℚ R)
    (h1 : x.coeff (-1) = 1) (hlt : ∀ r : ℚ, r < -1 → x.coeff r = 0) :
    ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  intro m
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun r _ => Subsingleton.elim _ _⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hxo : x.order = -1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_
    by_contra hc
    push_neg at hc
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlt _ hc))
  have hxl : x.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hxo, h1]
  have key : ∀ n : ℕ, (x ^ n).order = -(n : ℚ) ∧ (x ^ n).leadingCoeff = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
        rw [ih.2, hxl, one_mul]; exact one_ne_zero
      rw [pow_succ, HahnSeries.order_mul_of_ne_zero hne, HahnSeries.leadingCoeff_mul_of_ne_zero hne,
        ih.1, ih.2, hxo, hxl]
      constructor
      · push_cast; ring
      · simp
  obtain ⟨ho, hl⟩ := key m
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← ho, ← HahnSeries.leadingCoeff_eq, hl]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [ho]; exact hr)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInvStatement
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_pow_of_leading_qInv : ∀ {R : Type} [CommRing R] (x : HahnSeries ℚ R), x.coeff (-1) = 1 → (∀ r : ℚ, r < -1 → x.coeff r = 0) → ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  first | exact @GlobalTheory.hahn_pow_neg_one_lead | exact GlobalTheory.hahn_pow_neg_one_lead | (intros; apply GlobalTheory.hahn_pow_neg_one_lead <;> assumption)
end
end
