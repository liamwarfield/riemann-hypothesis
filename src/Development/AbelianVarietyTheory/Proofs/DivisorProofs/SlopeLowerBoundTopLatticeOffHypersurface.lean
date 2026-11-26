module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeGeHeightPolynomialVectorsDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortColumnsDetNeZeroHilbertSamuelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamComplexTensorNormColumnUnitSpheresLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRationalSectionsEqPowProductLinearForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLattice
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.CoeffInt

theorem word_col {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (g : Fin t → Fin n) :
    word mul (fun i => w.col (g i)) =
      ∑ e : Fin t → Fin N, (∏ i, w (e i) (g i)) • word mul (fun i => Pi.single (e i) 1) := by
  let Φ := (MultilinearMap.mkPiAlgebraFin K t (Module.End K A)).compLinearMap (fun _ => mul)
  have hΦ : ∀ u : Fin t → Fin N → K, word mul u = Φ u := by
    intro u; simp [Φ, word, MultilinearMap.mkPiAlgebraFin_apply]
  have hcol : ∀ i, w.col (g i) = ∑ j, w j (g i) • (Pi.single j 1 : Fin N → K) := by
    intro i; funext k; simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hΦ]
  simp_rw [hcol]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MultilinearMap.map_smul_univ, hΦ]
  rfl

theorem linSubst_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (c : A →ₗ[K] K)
    (β : Fin t → Fin B) (x : A) :
    linSubst w (coordP mul c β x) =
      ∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K) := by
  rw [show (∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) =
      ∑ g : Fin t → Fin n, ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) x)) *
        ((∏ i, C (w (e i) (g i))) * ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) from ?_]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [linSubst, coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, algebraMap_eq]
    simp_rw [Fintype.prod_sum, Finset.mul_sum, ← Finset.prod_mul_distrib]
    exact Finset.sum_comm
  · refine Finset.sum_congr rfl fun g _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [word_col, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, ← map_prod, map_mul]
    ring

theorem prod_X_monomial {σ K : Type} [Field K] {t : ℕ} (f : Fin t → σ) :
    ∃ s, (∏ i, (X (f i) : MvPolynomial σ K)) = monomial s 1 := by
  refine Finset.prod_induction _ (fun q => ∃ s, q = monomial s 1) ?_ ?_ ?_
  · rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩; exact ⟨s + s', by rw [monomial_mul, one_mul]⟩
  · exact ⟨0, by simp⟩
  · intro i _; exact ⟨_, rfl⟩

end GlobalTheory.HSShort.CoeffInt


open GlobalTheory.HSShort.CoeffInt in
theorem GlobalTheory.HSShort.colCoeff_mem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m • b i ∈ S.M S.T := by
  intro F A _ _ _ _ _ _ S hS d b c hco κ hx m
  obtain ⟨-, hM⟩ := GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS κ.j κ.t (le_of_eq κ.add)
  have tr : ∀ j', j' = S.T → ∀ y' ∈ S.M j', ∃ y ∈ S.M S.T, (y : A) = (y' : A) := by
    rintro j' rfl y' hy'; exact ⟨y', hy', rfl⟩
  have key : ∀ g : Fin κ.t → Fin S.n, ∃ y ∈ S.M S.T,
      (y : A) = word S.mul (fun i => S.w.col (g i)) (κ.x : A) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hM g κ.x hx
    obtain ⟨z, hz, hzeq⟩ := tr _ κ.add y hy
    exact ⟨z, hz, hzeq.trans hyeq⟩
  choose Y hY hYeq using key
  have hex : ∀ g : Fin κ.t → Fin S.n, ∃ s,
      (∏ i, (X (κ.β i, g i) : MvPolynomial (Fin _ × Fin S.n) F)) = monomial s 1 := by
    intro g
    exact GlobalTheory.HSShort.CoeffInt.prod_X_monomial (K := F) (fun i => (κ.β i, g i))
  choose s hs using hex
  have hcoef : ∀ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m =
      ∑ g, b.repr (Y g) i * (if s g = m then 1 else 0) := by
    intro i
    rw [GlobalTheory.HSShort.CoeffInt.linSubst_coordP, coeff_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_C_mul, hs g, coeff_monomial, ← hYeq g, hco]
  simp_rw [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun g _ => ?_
  have hsum : ∑ i, (b.repr (Y g) i * (if s g = m then (1 : F) else 0)) • b i =
      (if s g = m then (1 : F) else 0) • Y g := by
    conv_rhs => rw [← b.sum_repr (Y g), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  split_ifs
  · rw [one_smul]; exact hY g
  · rw [zero_smul]; exact zero_mem _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLatticeStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m • b i ∈ S.M S.T := by
  first | exact @GlobalTheory.HSShort.colCoeff_mem | exact GlobalTheory.HSShort.colCoeff_mem | (intros; apply GlobalTheory.HSShort.colCoeff_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClaimSOfNumbers
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShortEnd

theorem claimS_of_numbers : ∀ (T D δ d y e : ℕ) (n Λ β Λ₀ ΛD ΛT Hf H' dg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ Λ₀ → 1 ≤ ΛD → 1 ≤ ΛT → (T - 1).choose D * δ + y ≤ d → ∀ b : ℕ, (D + 1) * b = (T - 1).choose D * (T + D * (D + 1)) → b * ((D + 1) * δ) + e = (T - 1).choose D * δ * T + y * (T - D) → -(cst n Λ * ((D + 1) * δ)) ≤ Hf → -(cst n Λ * e) ≤ H' → b * Hf + H' - (((T - 1).choose D * δ : ℕ) * Real.log (Real.sqrt β ^ T * Λ₀) + y * Real.log (Real.sqrt β ^ (T - D) * ΛD) + (d - (T - 1).choose D * δ - y : ℕ) * Real.log ΛT) ≤ dg → 0 < d ∧ ClaimS T D n Λ β Λ₀ ΛD ΛT δ (Hf / (((D : ℝ) + 1) * δ)) d dg := by
  intro T D δ d y e n Λ β Λ₀ ΛD ΛT Hf H' dg hD hDT hδ hn hΛ hβ hΛ₀ hΛD hΛT hd b hb he hHf hH' hdg
  have hDT' : D ≤ T - 1 := by omega
  have hR : 1 ≤ (T - 1).choose D := Nat.choose_pos hDT'
  set R := (T - 1).choose D with hRdef
  have hRδ : 1 ≤ R * δ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdpos : 0 < d := by omega
  refine ⟨hdpos, ?_⟩

  have hc : 0 ≤ cst n Λ := by
    unfold cst
    have h1 : 0 ≤ Real.log (n * Λ) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log n := Real.log_nonneg hn
    positivity
  set c := cst n Λ with hcdef

  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDTR : (D : ℝ) + 1 ≤ T := by exact_mod_cast hDT
  have hdR' : (R : ℝ) * δ + y ≤ d := by exact_mod_cast hd
  have hbR : ((D : ℝ) + 1) * b = R * (T + D * (D + 1)) := by exact_mod_cast hb
  have hTD : D ≤ T := by omega
  have heR : (b : ℝ) * ((D + 1) * δ) + e = R * δ * T + y * ((T : ℝ) - D) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) he
    push_cast [Nat.cast_sub hTD] at this
    linarith
  have hsub : ((d - R * δ - y : ℕ) : ℝ) = d - R * δ - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsubTD : ((T - D : ℕ) : ℝ) = T - D := by rw [Nat.cast_sub hTD]

  have hβ0 : 0 < β := by linarith
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hlb : Real.log (Real.sqrt β) = Real.log β / 2 := Real.log_sqrt hβ0.le
  have hL0 : Real.log (Real.sqrt β ^ T * Λ₀) = T * (Real.log β / 2) + Real.log Λ₀ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb]
  have hLD : Real.log (Real.sqrt β ^ (T - D) * ΛD) = ((T : ℝ) - D) * (Real.log β / 2) + Real.log ΛD := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hlb, hsubTD]
  have lβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have lD : 0 ≤ Real.log ΛD := Real.log_nonneg hΛD
  have lT : 0 ≤ Real.log ΛT := Real.log_nonneg hΛT
  have l0 : 0 ≤ Real.log Λ₀ := Real.log_nonneg hΛ₀
  rw [hL0, hLD, hsub] at hdg
  push_cast at hdg

  set h := Hf / (((D : ℝ) + 1) * δ) with hhdef
  have hpos : (0 : ℝ) < ((D : ℝ) + 1) * δ := by positivity
  have hHfh : Hf = ((D : ℝ) + 1) * δ * h := by rw [hhdef]; field_simp
  have hh : -c ≤ h := by
    rw [hhdef, le_div_iff₀ hpos]; linarith
  have hbHf : (b : ℝ) * Hf = R * δ * (T + D * (D + 1)) * h := by
    rw [hHfh]
    calc (b : ℝ) * (((D : ℝ) + 1) * δ * h) = (((D : ℝ) + 1) * b) * δ * h := by ring
      _ = _ := by rw [hbR]; ring

  have he2 : (e : ℝ) = y * ((T : ℝ) - D) - R * δ * (D * (D + 1)) := by
    have : (b : ℝ) * ((D + 1) * δ) = R * δ * (T + D * (D + 1)) := by
      calc (b : ℝ) * ((D + 1) * δ) = (((D : ℝ) + 1) * b) * δ := by ring
        _ = _ := by rw [hbR]; ring
    linarith
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hRδ0 : (0 : ℝ) ≤ R * δ := by positivity
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDD : (0 : ℝ) ≤ D * (D + 1) := by positivity
  have heT : (e : ℝ) ≤ T * (d - R * δ) := by
    rw [he2]
    linarith [mul_nonneg hRδ0 hDD, mul_nonneg hy0 hD0, mul_nonneg (sub_nonneg.mpr hdR') hT0]
  have hce : c * e ≤ c * (T * (d - R * δ)) := mul_le_mul_of_nonneg_left heT hc
  have hch : R * δ * (D * (D + 1)) * (-c) ≤ R * δ * (D * (D + 1)) * h :=
    mul_le_mul_of_nonneg_left hh (mul_nonneg hRδ0 hDD)
  have hX : 0 ≤ (d - R * δ - y) * (T * (Real.log β / 2) + Real.log ΛD) := by
    apply mul_nonneg (by linarith); positivity
  have hyD : 0 ≤ (y : ℝ) * D * Real.log β := by positivity
  have hyT : 0 ≤ (y : ℝ) * Real.log ΛT := by positivity
  have key : (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ dg := by
    linarith [hbHf, hce, hch, hX, hyD, hyT, hdg, hH']
  unfold ClaimS
  have hρ0 : (0 : ℝ) ≤ R * δ / d := div_nonneg hRδ0 hdR.le
  have hρ1 : (R : ℝ) * δ / d ≤ 1 := by rw [div_le_one hdR]; linarith
  refine ⟨by push_cast; linarith, by push_cast; linarith, ?_⟩
  rw [le_div_iff₀ hdR]
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have expand : ((1 - (1 - ((R : ℕ) : ℝ) * δ / d)) * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((R : ℕ) : ℝ) * δ / d) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT)) * d =
      (R : ℝ) * δ * (T * h - D * (D + 1) * c - Real.log Λ₀ - T / 2 * Real.log β) -
      (d - R * δ) * (T * c + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) := by
    field_simp
    ring
  push_cast at expand ⊢
  rw [expand]; exact key

end GlobalTheory.HSShortEnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetIsMultiHomogeneous
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DetHom

section MH

variable {R : Type} [CommSemiring R] {B n : ℕ}

theorem mh_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem mh_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem mh_X (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (Pi.single i 1) (X (i, j) : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_X'] at hs
  have : Finsupp.single (i, j) 1 = s := by
    by_contra h; exact hs (if_neg h)
  subst this
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, hb, Pi.single_apply]

theorem mh_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem mh_sum {ι : Type} (t : Finset ι) {a : Fin B → ℕ} (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous a (f i)) : IsMultiHomogeneous a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_zero (R := R) (n := n) a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact mh_add (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mh_smul {S : Type} [SMulZeroClass S R] {a : Fin B → ℕ} (c : S) {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) : IsMultiHomogeneous a (c • f) :=
  fun s hs => hf s (support_smul hs)

theorem mh_mul {a b : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous b g) : IsMultiHomogeneous (a + b) (f * g) := by
  classical
  intro s hs i
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  simp [Finset.sum_add_distrib, hf u hu i, hg v hv i]

theorem mh_prod {ι : Type} (t : Finset ι) (a : ι → Fin B → ℕ) (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous (a i) (f i)) : IsMultiHomogeneous (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_C (R := R) (B := B) (n := n) 1
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    exact mh_mul (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MH

def cnt {B t : ℕ} (β : Fin t → Fin B) (b : Fin B) : ℕ := (Finset.univ.filter fun q => β q = b).card

theorem sum_cnt {B t : ℕ} (β : Fin t → Fin B) : ∑ b, cnt β b = t := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (β x))]
  simp

theorem sum_single_eq_cnt {B t : ℕ} (β : Fin t → Fin B) :
    (∑ i, (Pi.single (β i) 1 : Fin B → ℕ)) = cnt β := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.single_apply, cnt]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β i = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem mh_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) :
    IsMultiHomogeneous (cnt β) (coordP mul c β m) := by
  classical
  unfold coordP
  refine mh_sum _ _ fun e _ => ?_
  have h := mh_mul (mh_C (R := K) (B := B) (n := N) (c (word mul (fun i => Pi.single (e i) 1) m)))
    (mh_prod Finset.univ (fun i => (Pi.single (β i) 1 : Fin B → ℕ)) (fun i => (X (β i, e i) : MvPolynomial (Fin B × Fin N) K))
      fun i _ => mh_X (β i) (e i))
  rwa [zero_add, sum_single_eq_cnt] at h

end GlobalTheory.HSShort.DetHom


open GlobalTheory.HSShort.DetHom in
theorem GlobalTheory.HSShort.det_isMultiHomogeneous : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A) (d : ℕ) (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col), ∃ a : Fin (S.D + 1) → ℕ, IsMultiHomogeneous a (S.det c col) ∧ ∑ i, a i = ∑ k, (col k).t := by
  intro F A _ _ _ _ _ _ S d c col
  classical
  refine ⟨∑ k, cnt (col k).β, ?_, ?_⟩
  · unfold Sys.det
    rw [Matrix.det_apply]
    refine mh_sum _ _ fun σ _ => mh_smul _ ?_
    have h := mh_prod Finset.univ (fun k => cnt (col k).β)
      (fun k => (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) (σ k) k)
      fun k _ => by simpa using mh_coordP S.mul (c (σ k)) (col k).β ((col k).x : A)
    exact h
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cnt (col k).β
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdOfSpecialisations
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShortDiv

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def lastSubst (l₀ : Fin N → F) : Fin (D + 1) × Fin N → MvPolynomial (Fin (D + 1) × Fin N) F :=
  fun p => if p.1 = Fin.last D then C (l₀ p.2) else X p

theorem eval_aeval_lastSubst (l₀ : Fin N → F) (x : Fin (D + 1) × Fin N → F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval x (aeval (lastSubst l₀) f) = eval (fun p => if p.1 = Fin.last D then l₀ p.2 else x p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p q hp =>
    simp only [map_mul, hp, aeval_X, eval_X, lastSubst]
    split_ifs <;> simp

theorem replace_eq_join (l : Fin N → F) (x : Fin (D + 1) × Fin N → F) :
    (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l p.2 else x p) =
      join (fun i j => x (i.castSucc, j)) l := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join]
  | cast i => simp [join, Fin.castSucc_ne_last]

theorem eval_last_zero {δ : ℕ} (hδ : 1 ≤ δ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (x : Fin (D + 1) × Fin N → F) :
    eval (fun p => if p.1 = Fin.last D then 0 else x p) f = 0 := by
  rw [eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hs := hf d hd (Fin.last D)
  have hne : (∑ j : Fin N, d (Fin.last D, j)) ≠ 0 := by simp only at hs; omega
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (Fin.last D, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

theorem pow_dvd_of_specialisations (F : Type) [Field F] [CharZero F] (D N δ b : ℕ) (f G : MvPolynomial (Fin (D + 1) × Fin N) F)
    (Q : MvPolynomial (Fin D × Fin N) F) (hδ : 1 ≤ δ) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (hirr : Irreducible f) (hQ : Q ≠ 0)
    (hG : ∀ s : Fin D → Fin N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → ∃ (E : Type) (_ : Field E)
      (_ : Algebra F E) (γ : E), ∀ l : Fin N → F,
        algebraMap F E (eval (join s l) G) = γ * algebraMap F E (eval (join s l) f) ^ b) :
    f ^ b ∣ G := by
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  have hf0 : f ≠ 0 := hirr.ne_zero

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (MvPolynomial.funext fun x => by simp [h x])
  set l₀ : Fin N → F := fun j => x₀ (Fin.last D, j) with hl₀
  set g := aeval (lastSubst l₀) f with hg
  set G₀ := aeval (lastSubst l₀) G with hG₀
  set Q' : MvPolynomial (Fin (D + 1) × Fin N) F :=
    rename (fun p : Fin D × Fin N => (p.1.castSucc, p.2)) Q with hQ'
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hQ
    apply rename_injective _ _ (h.trans (map_zero _).symm)
    intro p q hpq
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at hpq
    exact Prod.ext hpq.1 hpq.2

  have key : Q' * (G * g ^ b - f ^ b * G₀) = 0 := by
    apply MvPolynomial.funext
    intro x
    set s : Fin D → Fin N → F := fun i j => x (i.castSucc, j) with hs
    have hx : x = join s (fun j => x (Fin.last D, j)) := by
      rw [← replace_eq_join]
      funext p
      split_ifs with h
      · rw [← h]
      · rfl
    have hQx : eval x Q' = eval (fun p => s p.1 p.2) Q := by
      rw [hQ', eval_rename]; rfl
    simp only [map_mul, map_sub, map_pow, map_zero]
    by_cases hq : eval (fun p => s p.1 p.2) Q = 0
    · rw [hQx, hq, zero_mul]
    · obtain ⟨E, _, _, γ, hγ⟩ := hG s hq
      have h1 := hγ (fun j => x (Fin.last D, j))
      have h2 := hγ l₀
      rw [← hx] at h1
      have hgx : eval x g = eval (join s l₀) f := by rw [hg, eval_aeval_lastSubst, replace_eq_join]
      have hGx : eval x G₀ = eval (join s l₀) G := by rw [hG₀, eval_aeval_lastSubst, replace_eq_join]
      rw [hgx, hGx]
      have : eval x G * eval (join s l₀) f ^ b - eval x f ^ b * eval (join s l₀) G = 0 := by
        apply (algebraMap F E).injective
        simp only [map_sub, map_mul, map_pow, map_zero, h1, h2]
        ring
      rw [this, mul_zero]
  have heq : G * g ^ b = f ^ b * G₀ := by
    have := (mul_eq_zero.mp key).resolve_left hQ'0
    exact sub_eq_zero.mp this
  have hp : Prime f := hirr.prime

  have hndvd : ¬ f ∣ g := by
    rintro ⟨h, hh⟩
    have hg0 : g ≠ 0 := by
      intro h0
      have := congrArg (eval x₀) h0
      rw [hg, eval_aeval_lastSubst, map_zero] at this
      apply hx₀
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x₀ p) = x₀ := by
        funext p
        split_ifs with hp1
        · rw [hl₀]; simp only; rw [← hp1]
        · rfl
      rw [hpt] at this
      exact this
    apply hg0
    apply MvPolynomial.funext
    intro x
    have e1 : eval x g = eval (fun p => if p.1 = Fin.last D then 0 else x p) g := by
      rw [hg, eval_aeval_lastSubst, eval_aeval_lastSubst]
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x p) =
          (fun p => if p.1 = Fin.last D then l₀ p.2 else if p.1 = Fin.last D then 0 else x p) := by
        funext p
        split_ifs <;> rfl
      rw [hpt]
    rw [e1, hh, map_mul, eval_last_zero hδ f hf, zero_mul, map_zero]
  have hndvd' : ¬ f ∣ g ^ b := fun h => hndvd (hp.dvd_of_dvd_pow h)
  exact hp.pow_dvd_of_dvd_mul_right b hndvd' ⟨G₀, heq⟩

end GlobalTheory.HSShortDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousCofactor
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.CofactorHom

theorem wcomp_mul_of_left {σ F : Type} [Field F] (w : σ → ℕ) (n : ℕ) {P : MvPolynomial σ F} {k : ℕ}
    (hP : IsWeightedHomogeneous w P k) (Q : MvPolynomial σ F) :
    weightedHomogeneousComponent w n (P * Q) =
      if k ≤ n then P * weightedHomogeneousComponent w (n - k) Q else 0 := by
  classical
  let := weightedGradedAlgebra F w
  have h := DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n
    ((mem_weightedHomogeneousSubmodule F w k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ F),
      ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) :
        MvPolynomial σ F) = weightedHomogeneousComponent w m R :=
    fun m R => weightedDecomposition.decompose'_apply F w R m
  rw [e, e] at h
  exact h

theorem weight_add_of_mul {σ F : Type} [Field F] (w : σ → ℕ) {P Q : MvPolynomial σ F} {k m : ℕ}
    (hPQ : P * Q ≠ 0) (hP : IsWeightedHomogeneous w P k) (hm : IsWeightedHomogeneous w (P * Q) m)
    (s : σ →₀ ℕ) (hs : s ∈ Q.support) : k + Finsupp.weight w s = m := by
  classical
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPQ
  set j := Finsupp.weight w s
  have hc : weightedHomogeneousComponent w j Q ≠ 0 := by
    intro h0
    have := congrArg (AddMonoidAlgebra.coeff · s) h0
    apply (mem_support_iff.mp hs)
    simpa only [coeff_weightedHomogeneousComponent, j, ite_true,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this

  have hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0 := by
    simp only [wcomp_mul_of_left w (k + j) hP Q, Nat.le_add_right, ite_true,
      Nat.add_sub_cancel_left]
    exact mul_ne_zero hP0 hc
  by_contra hkm
  exact hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)

end GlobalTheory.CofactorHom


open GlobalTheory.CofactorHom in
theorem GlobalTheory.HSShort.isMultiHomogeneous_cofactor :
    ∀ (F : Type) [Field F] (B N : ℕ) (a a₁ : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F),
      G * G' ≠ 0 → IsMultiHomogeneous a (G * G') → IsMultiHomogeneous a₁ G →
        ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' G' ∧ ∀ i, a₁ i + a' i = a i := by
  intro F _ B N a a₁ G G' h0 ha ha₁
  rw [isMultiHomogeneous_iff_forall_weighted_lh0BlockWt] at ha ha₁
  have key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b := fun b s hs => by
    rw [← weight_lh0BlockWt_apply]
    exact weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs
  obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by
    by_contra hno
    push Not at hno
    apply h0
    rw [show G' = 0 from by
      ext s; by_contra hc; exact hno s (mem_support_iff.mpr hc), mul_zero]
  refine ⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩
  · have := key b s hs
    show _ = a b - a₁ b
    omega
  · have := key i s₀ hs₀
    show a₁ i + (a i - a₁ i) = a i
    omega
end

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.SlopeTop

theorem mh_mul {R : Type*} [CommSemiring R] {B n : ℕ} {a a' c : Fin B → ℕ} {p q : MvPolynomial (Fin B × Fin n) R}
    (hp : IsMultiHomogeneous a p) (hq : IsMultiHomogeneous a' q) (hc : ∀ b, c b = a b + a' b) :
    IsMultiHomogeneous c (p * q) := by
  classical
  intro s hs b
  obtain ⟨s1, h1, s2, h2, rfl⟩ := Finset.mem_add.mp (support_mul p q hs)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hp s1 h1 b, hq s2 h2 b, hc]

theorem mh_pow {R : Type*} [CommSemiring R] {B n : ℕ} {a : Fin B → ℕ} {p : MvPolynomial (Fin B × Fin n) R}
    (hp : IsMultiHomogeneous a p) (k : ℕ) : IsMultiHomogeneous (fun b => k * a b) (p ^ k) := by
  classical
  induction k with
  | zero =>
    intro s hs b
    have : s = 0 := by
      rw [pow_zero, mem_support_iff, coeff_one] at hs
      by_contra h; exact hs (if_neg (Ne.symm h))
    simp [this]
  | succ k ih =>
    rw [pow_succ]
    exact mh_mul ih hp (fun b => by ring)

theorem ht_pow {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (k : ℕ) :
    ht w A (f ^ k) = k * ht w A f := by
  induction k with
  | zero => rw [pow_zero, ← C_1, (htMul F B N n w A Λ hL).2 1 one_ne_zero]; simp
  | succ k ih =>
    rw [pow_succ, (htMul F B N n w A Λ hL).1 _ _ _ _ (pow_ne_zero k hf) hf (mh_pow ha k) ha, ih]
    push_cast; ring

theorem map_join {R R' : Type} (φ : R → R') {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) :
    (fun p => φ (join u ξ p)) = join (fun i j => φ (u i j)) (fun j => φ (ξ j)) := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join_last]
  | cast i => simp [join_castSucc]

theorem eval_spec {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E) (l : Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => l p.2) (spec s f) = aeval (join s l) f := by
  have hj : ∀ q, eval (fun p : Fin 1 × Fin N => l p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) E)) (fun j => X (0, j)) q) = join s l q := by
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last => simp [join_last]
    | cast i => simp [join_castSucc]
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec]
  | add p q hp hq => simp only [spec, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p q hp => simp only [spec, map_mul, aeval_X] at *; rw [hp, hj]

theorem algebraMap_eval {F E σ : Type} [Field F] [Field E] [Algebra F E] (x : σ → F) (p : MvPolynomial σ F) :
    algebraMap F E (eval x p) = aeval (fun i => algebraMap F E (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add (f := _), hp, hq]
  | mul_X p q hp => simp [map_mul, hp]

theorem sum_three {d : ℕ} (P Q : Fin d → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ k, P k → ¬ Q k)
    {M : Type*} [AddCommMonoid M] (g : Fin d → M) (x y z : M)
    (hx : ∀ k, P k → g k = x) (hy : ∀ k, Q k → g k = y) (hz : ∀ k, ¬ P k → ¬ Q k → g k = z) :
    ∑ k, g k = (Finset.univ.filter P).card • x + (Finset.univ.filter Q).card • y +
      (Finset.univ.filter fun k => ¬ P k ∧ ¬ Q k).card • z := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun k => ¬ P k) Q,
    Finset.filter_filter, Finset.filter_filter]
  have e1 : (Finset.univ.filter fun k => ¬ P k ∧ Q k) = Finset.univ.filter Q :=
    Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨fun hp => hPQ k hp h, h⟩⟩
  rw [e1, Finset.sum_congr rfl (fun k hk => hx k (Finset.mem_filter.mp hk).2),
    Finset.sum_congr rfl (fun k hk => hy k (Finset.mem_filter.mp hk).2),
    Finset.sum_congr rfl (fun k hk => hz k (Finset.mem_filter.mp hk).2.1 (Finset.mem_filter.mp hk).2.2)]
  simp only [Finset.sum_const, add_assoc]

end GlobalTheory.HSShort.SlopeTop

namespace GlobalTheory.HSShort.SlopeTop

theorem slopeBound : SlopeBound := by
  intro F A _ _ _ _ _ _ S hS δ f Q hδ hfh hfi hQ hflat
  classical
  obtain ⟨d, b, -⟩ := hS.shortT
  have hfin : Module.finrank F (S.V S.T) = d := by simpa using Module.finrank_eq_card_basis b
  have hc : ∀ i, ∃ g : A →ₗ[F] F, g ∘ₗ (S.V S.T).subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose c hc using hc
  have hco : S.IsCo b c := by
    intro i x
    have := congrArg (fun g => g x) (hc i)
    simpa using this
  have hex : ∃ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hQ
    apply MvPolynomial.funext
    intro x
    simpa using h (fun i k => x (i, k))
  have hbd : ∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.deepRank s ≤ d := by
    intro s hs
    obtain ⟨E, A', _, _, _, _, Φ, -, -, -⟩ := hflat s hs
    rw [← hfin]; exact (GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ).2.2
  let P : ℕ → Prop := fun y => ∃ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 ∧ S.deepRank s = y
  obtain ⟨s₁, hs₁⟩ := hex
  obtain ⟨s₀, hs₀, hy⟩ : P (Nat.findGreatest P d) := Nat.findGreatest_spec (hbd s₁ hs₁) ⟨s₁, hs₁, rfl⟩
  have hmax : ∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.deepRank s ≤ Nat.findGreatest P d :=
    fun s hs => Nat.le_findGreatest (hbd s hs) ⟨s, hs, rfl⟩
  obtain ⟨E₀, A₀, _, _, _, _, Φ₀, -, -, -⟩ := hflat s₀ hs₀
  obtain ⟨col, m, ix, hsh, hshort, hcard, hdet⟩ := GlobalTheory.T.exists_short_columns_det_ne_zero_hilbertSamuel F A S hS E₀ A₀ s₀ δ Φ₀ d b c hco
  rw [hy] at hcard
  have hdiv : f ^ S.expo ∣ S.det c col := by
    refine GlobalTheory.HSShortDiv.pow_dvd_of_specialisations F S.D S.N δ S.expo f (S.det c col) Q hδ hfh hfi hQ ?_
    intro s hs
    obtain ⟨E, A', _, _, _, _, Φ, c', hc', hsp⟩ := hflat s hs
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.det_rational_sections_eq_pow_product_linearForms F A S hS E A' s δ Φ d b c hco col m ix hsh (hcard ▸ hmax s hs)
    refine ⟨E, inferInstance, inferInstance, γ / c' ^ S.expo, fun l => ?_⟩
    have h1 := hγ (fun k => algebraMap F E (l k))
    have h2 : aeval (join (fun i k => algebraMap F E (s i k)) (fun k => algebraMap F E (l k))) f =
        c' * ∏ p, ∑ k, algebraMap F E (l k) * Φ.y p k := by
      rw [← eval_spec, hsp]; simp [lin]
    rw [algebraMap_eval, algebraMap_eval, map_join, h1, h2, mul_pow]
    field_simp
  obtain ⟨G', hG'⟩ := hdiv
  obtain ⟨a, ha, hsum⟩ := GlobalTheory.HSShort.det_isMultiHomogeneous F A S d c col
  have hf0 : f ≠ 0 := hfi.ne_zero
  have hfe : IsMultiHomogeneous (fun _ => S.expo * δ) (f ^ S.expo) := mh_pow hfh S.expo
  have hdet' : f ^ S.expo * G' ≠ 0 := hG' ▸ hdet
  have ha2 : IsMultiHomogeneous a (f ^ S.expo * G') := hG' ▸ ha
  obtain ⟨a', ha', hadd⟩ := GlobalTheory.HSShort.isMultiHomogeneous_cofactor F (S.D + 1) S.N a (fun _ => S.expo * δ) (f ^ S.expo) G' hdet' ha2 hfe
  have hG0 : G' ≠ 0 := right_ne_zero_of_mul hdet'
  have hfe0 : f ^ S.expo ≠ 0 := left_ne_zero_of_mul hdet'
  have hht : ht S.w S.fr (S.det c col) = S.expo * ht S.w S.fr f + ht S.w S.fr G' := by
    rw [hG', (htMul F _ _ _ S.w S.fr S.abelian₂ hS.lat).1 _ _ _ _ hfe0 hG0 hfe ha', ht_pow hS.lat hf0 hfh]
  have hlowf := GlobalTheory.T.multiformHeight_lowerBound F (S.D + 1) S.N S.n S.w S.fr S.abelian₂ hS.lat (fun _ => δ) f hf0 hfh
  have hlowG := GlobalTheory.T.multiformHeight_lowerBound F (S.D + 1) S.N S.n S.w S.fr S.abelian₂ hS.lat a' G' hG0 ha'
  let bnd : ℕ → ℝ := fun j => if j = 0 then S.Lam0 else if j = S.D then S.LamD else S.LamT
  let Bd : Fin d → ℝ := fun k => Real.sqrt S.beta ^ (col k).t * bnd (col k).j
  have hbnd1 : ∀ j, 1 ≤ bnd j := by
    intro j; simp only [bnd]
    split_ifs
    · exact hS.hermSysHyp_one_le_lambdaZero
    · exact hS.one_le_LamD
    · exact hS.one_le_LamT
  have hsb : 1 ≤ Real.sqrt S.beta := Real.one_le_sqrt.mpr hS.one_le_beta
  have hBd : ∀ k, 0 < Bd k := fun k => mul_pos (pow_pos (by linarith) _) (by linarith [hbnd1 (col k).j])
  have htop := GlobalTheory.T.lattice_degree_ge_height_polynomialVectors_det F (S.V S.T) (S.nm S.T) (S.M S.T) d b (hS.full S.T le_rfl) (S.D + 1) S.N S.n S.w S.fr S.abelian₂
    hS.lat (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) a Bd hdet ha hBd
    (fun k m' => GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice F A S hS d b c hco (col k) (hshort k).1 m')
    (fun k σ u hu => (GlobalTheory.T.hermFamComplexTensorNorm_column_unitSpheres_le F A S hS d b c hco (col k) σ u hu).trans
      (mul_le_mul_of_nonneg_left ((hshort k).2 σ) (pow_nonneg (by linarith) _)))

  have hD1 := hS.one_le
  have hDT := hS.le_T
  have hnum := GlobalTheory.HSShort.monomial_counts S.D S.T hD1 hDT
  let PR : Fin d → Prop := fun k => k ∈ Set.range ix
  let QY : Fin d → Prop := fun k => (col k).j = S.D
  have hPR : ∀ k, PR k → (col k).j = 0 := by rintro k ⟨q, rfl⟩; exact hsh.x_j q
  have hPQ : ∀ k, PR k → ¬ QY k := fun k hk hq => by
    have h0 := hPR k hk; simp only [QY] at hq; omega
  have hRest : ∀ k, ¬ PR k → ¬ QY k → (col k).j = S.T := by
    intro k h1 h2
    rcases hsh.rest k h1 with h | h
    · exact absurd h.1 h2
    · exact h
  have hcardR : (Finset.univ.filter PR).card = (S.T - 1).choose S.D * δ := by
    have : (Finset.univ.filter PR) = Finset.univ.map ix := by ext k; simp [PR]
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card,
      hnum.2.1]
  have hcardQ : (Finset.univ.filter QY).card = Nat.findGreatest P d := hcard
  have hcard3 := sum_three PR QY hPQ (fun _ => (1 : ℕ)) 1 1 1 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hcard3
  have ht3 := sum_three PR QY hPQ (fun k => (col k).t) S.T (S.T - S.D) 0
    (fun k hk => by have := (col k).add; have h0 := hPR k hk; omega)
    (fun k hk => by have := (col k).add; simp only [QY] at hk; omega)
    (fun k h1 h2 => by have := (col k).add; have hj := hRest k h1 h2; omega)
  simp only [smul_eq_mul, mul_zero, add_zero] at ht3
  have hl3 := sum_three PR QY hPQ (fun k => Real.log (Bd k)) (Real.log (Real.sqrt S.beta ^ S.T * S.Lam0))
    (Real.log (Real.sqrt S.beta ^ (S.T - S.D) * S.LamD)) (Real.log S.LamT)
    (fun k hk => by
      have := (col k).add; have h0 := hPR k hk
      have ht' : (col k).t = S.T := by omega
      simp [Bd, bnd, h0, ht'])
    (fun k hk => by
      have := (col k).add; simp only [QY] at hk
      have hD0 : S.D ≠ 0 := by omega
      have ht' : (col k).t = S.T - S.D := by omega
      simp [Bd, bnd, hk, hD0, ht'])
    (fun k h1 h2 => by
      have := (col k).add; have hj := hRest k h1 h2
      have hT0 : S.T ≠ 0 := by omega
      have hTD : S.T ≠ S.D := by omega
      have ht0 : (col k).t = 0 := by omega
      simp [Bd, bnd, hj, hT0, hTD, ht0])
  simp only [nsmul_eq_mul] at hl3
  have hcountRest : (Finset.univ.filter fun k => ¬ PR k ∧ ¬ QY k).card =
      d - (S.T - 1).choose S.D * δ - Nat.findGreatest P d := by omega
  have hcount : (S.T - 1).choose S.D * δ + Nat.findGreatest P d ≤ d := by omega
  have e1 : ∑ i, a i = (S.D + 1) * (S.expo * δ) + ∑ i, a' i := by
    rw [← Finset.sum_congr rfl (fun i _ => hadd i)]; simp [Finset.sum_add_distrib]
  have hsumE : S.expo * ((S.D + 1) * δ) + ∑ i, a' i =
      (S.T - 1).choose S.D * δ * S.T + Nat.findGreatest P d * (S.T - S.D) := by
    calc _ = ∑ i, a i := by rw [e1]; ring
      _ = _ := by rw [hsum, ht3, hcardR, hcardQ]
  have hlowf' : -(cst (S.n : ℝ) S.abelian₂ * (((S.D : ℝ) + 1) * δ)) ≤ ht S.w S.fr f := by
    have := hlowf
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hlowG' : -(cst (S.n : ℝ) S.abelian₂ * ((∑ i, a' i : ℕ) : ℝ)) ≤ ht S.w S.fr G' := by
    rw [Nat.cast_sum]; exact hlowG
  have htop' : ht S.w S.fr (S.det c col) - ∑ k, Real.log (Bd k) ≤ deg (S.nm S.T) (S.M S.T) := htop
  rw [hht, hl3, hcardR, hcardQ, hcountRest] at htop'
  have hn1 : (1 : ℝ) ≤ S.n := by
    have : 1 ≤ S.n := by
      by_contra h
      have h0 : S.n = 0 := by omega
      have hsp := hS.lat.spans
      have hN := hS.lat.pos
      have hem : Set.range S.w.col = ∅ := by
        rw [Set.range_eq_empty_iff, h0]; infer_instance
      rw [hem, Submodule.span_empty] at hsp
      have hmem : (Pi.single (⟨0, hN⟩ : Fin S.N) 1 : Fin S.N → F) ∈ (⊥ : Submodule F (Fin S.N → F)) :=
        hsp ▸ Submodule.mem_top
      simp at hmem
    exact_mod_cast this
  have hres := GlobalTheory.HSShortEnd.claimS_of_numbers S.T S.D δ d (Nat.findGreatest P d) (∑ i, a' i) (S.n : ℝ) S.abelian₂ S.beta S.Lam0 S.LamD S.LamT
    (ht S.w S.fr f) (ht S.w S.fr G') (deg (S.nm S.T) (S.M S.T)) hD1 hDT hδ hn1 hS.lat.one_le hS.one_le_beta
    hS.hermSysHyp_one_le_lambdaZero hS.one_le_LamD hS.one_le_LamT hcount S.expo (by simpa [Sys.expo] using hnum.2.2) hsumE
    hlowf' hlowG' htop'
  rw [hfin]
  exact hres

end GlobalTheory.HSShort.SlopeTop
