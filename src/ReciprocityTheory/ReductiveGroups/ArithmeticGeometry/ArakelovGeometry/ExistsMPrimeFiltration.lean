module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HilbertMultidegreePieceDivisorSum
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem multigraded_length_stable_dim_zero {p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)) (b : K) :
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → lg W a = lg W (a - Pi.single b 1) := by
  obtain ⟨hWp, hWm, hWr⟩ := hW
  haveI := hWp
  obtain ⟨i, hi⟩ := hWr b
  have hf : IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := isMultiHomog_X' b i
  have hJm : IsMultiHomogIdeal (W ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι)}) :=
    isMultiHomogIdeal_sup_span hWm hf
  obtain ⟨N, F, f, c, q, h0, hlast, hj⟩ := exists_primeFiltration_of_isMultiHomogIdeal _ hJm
  have hle : ∀ j, W ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι)} ≤ q j := fun j =>
    le_colon_chain h0 (fun j => ⟨(hj j).2.1, (hj j).2.2.2.2⟩) j

  have hirr : ∀ j, ∃ k, ∀ i', (X ⟨k, i'⟩ : MRing ι) ∈ q j := by
    intro j
    haveI := (hj j).2.2.1
    obtain ⟨W', hW'min, hW'le⟩ := Ideal.exists_minimalPrimes_le (hle j)
    have hnr := not_relevant_of_dim_zero hWm hd hf hi hW'min
    rw [IsRelevant] at hnr
    push_neg at hnr
    obtain ⟨k, hk⟩ := hnr
    exact ⟨k, fun i' => hW'le (hk i')⟩
  have hp0 : 0 < p := hp.pos
  refine ⟨(Finset.univ.sup fun jk : Fin N × K => c jk.1 jk.2) + 1, fun a ha => ?_⟩
  have hca : ∀ j k, c j k < a k := by
    intro j k
    have h1 : c j k ≤ Finset.univ.sup fun jk : Fin N × K => c jk.1 jk.2 :=
      Finset.le_sup (f := fun jk : Fin N × K => c jk.1 jk.2) (Finset.mem_univ (j, k))
    have h2 := ha k
    omega
  have hsingle : ∀ k, (Pi.single b 1 : K → ℕ) k ≤ a k := by
    intro k
    rcases eq_or_ne k b with rfl | hk
    · have h2 := ha k
      simp only [Pi.single_eq_same]
      omega
    · simp [hk]
  have hstep := lg_step hWm hf (q := W)
    (fun g => ⟨fun hg => W.mul_mem_right _ hg,
      fun hg => (hWp.mem_or_mem hg).resolve_right hi⟩) hsingle hp0 hpW
  have hF0 : IsMultiHomogIdeal (F 0) := by rw [h0]; exact hJm
  have hchain := lg_chain a (F := F) (f := f) (c := c) (q := q) hF0 hlast
    (fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.2.2⟩) (fun j k => (hca j k).le) hp0
    (fun j => hle j (Ideal.mem_sup_left hpW))
  have hzero : ∀ j, lg (q j) (a - c j) = 0 := by
    intro j
    obtain ⟨k, hk⟩ := hirr j
    have hpos : 0 < (a - c j) k := by
      show 0 < a k - c j k
      have h3 := hca j k
      omega
    rw [lg, card_mPiece_irrel hk hpos]
    simp
  rw [hstep, ← h0, hchain, Finset.sum_eq_zero (fun j _ => hzero j), zero_add]

theorem hasymp_base {p : ℕ} (hp : p.Prime) {L : ℝ} (hL : L = Real.log p) {W : Ideal (MRing ι)}
    (hW : IsMultiProjPrime W) (hpW : (p : MRing ι) ∈ W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)) : HAsymp L 0 W := by
  have hW0 := hW
  obtain ⟨hWp, hWm, hWr⟩ := hW0
  have hp0 : 0 < p := hp.pos
  choose a₀ ha₀ using fun b : K => multigraded_length_stable_dim_zero hp hW hpW hd b
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℕ, ∀ b, a₀ b ≤ a₁ :=
    ⟨Finset.univ.sup a₀, fun b => Finset.le_sup (Finset.mem_univ b)⟩

  have hconst_lg : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → lg W a = lg W (fun _ => a₁) := by
    have hwalk := walk_bound (fun a => lg W a - lg W (fun _ => a₁)) a₁ 0 (le_refl (0 : ℝ))
      (by
        intro a b ha _
        have h1 := ha₀ b a (fun k => (ha₁ b).trans (ha k))
        simp [h1])
    intro a ha
    have h1 := hwalk a ha
    simp only [sub_self, abs_zero, zero_add, Nat.cast_zero, mul_zero, zero_mul] at h1
    have h2 : |lg W a - lg W (fun _ => a₁)| = 0 := le_antisymm h1 (abs_nonneg _)
    rw [abs_eq_zero, sub_eq_zero] at h2
    exact h2
  have hcard : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) →
      Nat.card (mPiece W a) = Nat.card (mPiece W (fun _ => a₁)) := by
    intro a ha
    have h := hconst_lg a ha
    simp only [lg] at h
    have h1 : (0 : ℝ) < Nat.card (mPiece W a) := by
      exact_mod_cast card_mPiece_pos W a hp0 hpW
    have h2 : (0 : ℝ) < Nat.card (mPiece W (fun _ => a₁)) := by
      exact_mod_cast card_mPiece_pos W _ hp0 hpW
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) h
  let i : ∀ k, ι k := fun k => (hWr k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W := fun k => (hWr k).choose_spec
  have hD : Nat.card (MRing ι ⧸ dehomI W i) = Nat.card (mPiece W (fun _ => a₁)) :=
    card_dehom hWp hWm hi hcard (fun a => finite_mPiece W a hp0 hpW)
      (a := fun _ => a₁) (fun _ => le_refl _)
  have hpD : (p : MRing ι) ∈ dehomI W i := by
    rw [dehomI]
    exact Ideal.mem_sup_left hpW
  have hA : ∀ x : MRing ι ⧸ dehomI W i, p • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk (dehomI W i)) p, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right y _ hpD
  haveI : Finite (MRing ι ⧸ dehomI W i) :=
    Nat.finite_of_card_ne_zero (by rw [hD]; exact (card_mPiece_pos W _ hp0 hpW).ne')
  have hpow := natCard_eq_pow_length hp hA
  refine ⟨a₁, 0, le_refl 0, fun a ha => ?_⟩
  have hgeo : geoNum 0 W (fun _ k => (a k : ℤ)) =
      ((Module.length ℤ (MRing ι ⧸ dehomI W i)).toNat : ℤ) := by
    rw [geoNum, dite_eq_left hWr]
    rfl
  have hc : (Nat.card (mPiece W a) : ℝ) =
      (p : ℝ) ^ (Module.length ℤ (MRing ι ⧸ dehomI W i)).toNat := by
    rw [hcard a ha, ← hD, hpow]
    norm_cast
  have h0 : lg W a - appr L 0 W a = 0 := by
    rw [lg, appr, hc, hgeo, Real.log_pow, hL]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    push_cast
    ring
  rw [h0]
  simp

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_mPrimeFiltration {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc :=
  exists_primeFiltration_of_isMultiHomogIdeal J hJ

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStA
section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZSt
section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZStA
namespace ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension

open Matrix

private theorem exists_linearIndependent_append_of_codim {r : ℕ} (w : Fin r → (Fin r → ℚ))
    (hw : LinearIndependent ℚ w) :
    ∀ d a (u0 : Fin a → (Fin r → ℚ)), LinearIndependent ℚ u0 → r - a = d → a ≤ r →
      ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  intro d
  induction d with
  | zero =>
    intro a u0 hu0 hd har
    refine ⟨0, Fin.elim0, by omega, ?_⟩
    rw [Fin.append_right_nil u0 _ rfl]
    exact hu0.comp _ (Fin.cast_injective _)
  | succ d ih =>
    intro a u0 hu0 hd har
    obtain ⟨j, hj⟩ : ∃ j, w j ∉ Submodule.span ℚ (Set.range u0) := by
      by_contra hcon
      push_neg at hcon
      haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      have htop : Submodule.span ℚ (Set.range w) = ⊤ :=
        hw.span_eq_top_of_card_eq_finrank (by simp)
      have hle : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range u0) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr hcon)
      rw [htop, top_le_iff] at hle
      have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range u0)) ≤ Fintype.card (Fin a) :=
        finrank_range_le_card (R := ℚ) u0
      rw [hle, finrank_top] at h1
      simp at h1
      omega
    have hu1 : LinearIndependent ℚ (Fin.snoc u0 (w j) : Fin (a + 1) → (Fin r → ℚ)) :=
      linearIndependent_finSnoc.mpr ⟨hu0, hj⟩
    obtain ⟨m, f, hm, hli⟩ := ih (a + 1) (Fin.snoc u0 (w j)) hu1 (by omega) (by omega)
    refine ⟨m + 1, Fin.cons j f, by omega, ?_⟩
    rw [Fin.comp_cons, Fin.append_right_cons]
    exact hli.comp _ (Fin.cast_injective _)

theorem exists_append_li {a r : ℕ} (u0 : Fin a → (Fin r → ℚ)) (hu0 : LinearIndependent ℚ u0)
    (w : Fin r → (Fin r → ℚ)) (hw : LinearIndependent ℚ w) :
    ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  have har : a ≤ r := by
    have h := hu0.fintype_card_le_finrank
    simpa using h
  exact exists_linearIndependent_append_of_codim w hw _ a u0 hu0 rfl har

end ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
end

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder

theorem neg_log_det_le {r' r : ℕ} (hr : r' ≤ r) {G' : Matrix (Fin r') (Fin r') ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG' : G'.PosDef) (hG : G.PosDef)
    (M : Matrix (Fin r) (Fin r') ℤ) (hM : Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec)
    (N : Matrix (Fin r) (Fin r) ℤ) (hN : N.det ≠ 0) {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hnorm : (((A : ℂ) ^ 2) • G' -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * G * M.map (Int.cast : ℤ → ℂ)).PosSemidef)
    (hsmall : ∀ i, (((N.map (Int.cast : ℤ → ℂ))ᴴ * G * N.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2) :
    -(1 / 2) * Real.log G'.det.re ≤
      -(1 / 2) * Real.log G.det.re + r' * Real.log A + ((r : ℝ) - r') * Real.log lam := by
  classical
  have hu0 : LinearIndependent ℚ (M.map (Int.cast : ℤ → ℚ)).col := Matrix.mulVec_injective_iff.mp hM
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hN
  have hw : LinearIndependent ℚ (N.map (Int.cast : ℤ → ℚ)).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hNq.isUnit)
  obtain ⟨m, f, hmr, hLI⟩ := LinearIndependentExtension.exists_append_li _ hu0 _ hw
  subst hmr
  set U : Matrix (Fin (r' + m)) (Fin (r' + m)) ℤ :=
    Matrix.of fun i j => Fin.append (fun k => M i k) (fun k => N i (f k)) j with hUdef
  have hUq : (U.map (Int.cast : ℤ → ℚ)).col =
      Fin.append (M.map (Int.cast : ℤ → ℚ)).col ((N.map (Int.cast : ℤ → ℚ)).col ∘ f) := by
    funext j i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.append_left]; simp [U, Matrix.col]
    · rw [Fin.append_right]; simp [U, Matrix.col]; rfl
  have hUdet : U.det ≠ 0 := by
    rw [← hUq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, ← Int.cast_det] at hLI
    exact_mod_cast hLI
  set UC := U.map (Int.cast : ℤ → ℂ) with hUC
  set MC := M.map (Int.cast : ℤ → ℂ) with hMC
  set NC := N.map (Int.cast : ℤ → ℂ) with hNC
  have hUCdet : UC.det = ((U.det : ℤ) : ℂ) := by rw [hUC, Int.cast_det]
  have hUCinj : Function.Injective UC.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hUCdet, isUnit_iff_ne_zero]
    exact_mod_cast hUdet
  set H := UCᴴ * G * UC with hH
  have hHpd : H.PosDef := hG.conjTranspose_mul_mul_same hUCinj
  have hUl : ∀ l i, UC l (Fin.castAdd m i) = MC l i := by intro l i; simp [UC, U, MC]
  have hUr : ∀ l j, UC l (Fin.natAdd r' j) = NC l (f j) := by intro l j; simp [UC, U, NC]
  have hsub : H.submatrix (Fin.castAdd m) (Fin.castAdd m) = MCᴴ * G * MC := by
    ext i j; simp only [H, submatrix_apply, Matrix.mul_apply, conjTranspose_apply, hUl]
  have hdiag : ∀ j, H (Fin.natAdd r' j) (Fin.natAdd r' j) = (NCᴴ * G * NC) (f j) (f j) := by
    intro j; simp only [H, Matrix.mul_apply, conjTranspose_apply, hUr]
  have hMMpd : (MCᴴ * G * MC).PosDef := by
    rw [← hsub]; exact hHpd.submatrix (Fin.castAdd_injective r' m)

  have hdetH : H.det.re = ((U.det : ℝ) ^ 2) * G.det.re := by
    rw [hH, det_mul, det_mul, det_conjTranspose, hUCdet]
    simp [Complex.mul_re, Complex.mul_im, sq]
    ring
  have hd1 : (1 : ℝ) ≤ (U.det : ℝ) ^ 2 := by
    have h1 := Int.one_le_abs hUdet
    have : (1 : ℤ) ≤ U.det ^ 2 := by nlinarith [sq_abs U.det]
    exact_mod_cast this
  have hGpos := (posDef_det_re_pos hG).1
  have hG'pos := (posDef_det_re_pos hG').1
  have hstep1 : G.det.re ≤ H.det.re := by rw [hdetH]; nlinarith
  have hstep2 := det_re_le_mul_prod_diag hHpd
  rw [hsub] at hstep2
  have hprod : ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re ≤ (lam ^ 2) ^ m := by
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le) (fun j _ => ?_)
    rw [hdiag]; exact hsmall _
  have hMM : (MCᴴ * G * MC).det.re ≤ (A ^ 2) ^ r' * G'.det.re := by
    have := det_re_le_of_sub_posSemidef hMMpd hnorm
    rw [det_smul, Fintype.card_fin] at this
    have e : ((A : ℂ) ^ 2) ^ r' = (((A ^ 2) ^ r' : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.re_ofReal_mul] at this
  have hMMpos := (posDef_det_re_pos hMMpd).1
  have hfin : G.det.re ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m := by
    have hP0 : 0 ≤ ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re :=
      Finset.prod_nonneg fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le
    calc G.det.re ≤ H.det.re := hstep1
      _ ≤ _ := hstep2
      _ ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m :=
        mul_le_mul hMM hprod hP0 (by positivity)
  have hlog := Real.log_le_log hGpos hfin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end ReciprocityTheory.GeometryOfNumbersTheory
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

theorem aeval_eq_sum_adt {D N : ℕ} {S : Type*} [CommRing S] (g : MvPolynomial (Fin (D + 1)) ℤ)
    (hg : g.IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y g = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
      ((AddMonoidAlgebra.coeff g (Finsupp.equivFunOnFinite.symm a) : ℤ) : S) * ∏ i, y i ^ a i := by
  classical
  rw [aeval_def, eval₂_eq']
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_
  · intro a _ ha
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply ha
    simp [h]
  · intro a _ _ b _ _ h
    exact Finsupp.equivFunOnFinite.symm.injective h
  · intro d hd hne
    refine ⟨Finsupp.equivFunOnFinite d, ?_, ?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      have h := hg (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.weight_apply] at h
      simpa [Finsupp.sum_fintype] using h
    · simpa using hne
    · simp
  · intro a _ _
    simp

theorem integral_sphProb_le {D : ℕ} (F : (Fin (D + 1) → ℂ) → ℝ) (hF0 : ∀ w, 0 ≤ F w) {B : ℝ}
    (hB : ∀ w, sqN w = 1 → F w ≤ B) : ∫ w, F w ∂(sphProb (D + 1)) ≤ B := by
  have hae : ∀ᵐ w ∂(sphProb (D + 1)), sqN w = 1 := by
    rw [ae_iff]
    exact sphProb_compl_sphere D
  letI : IsProbabilityMeasure (sphProb (D + 1)) := by
    unfold sphProb
    infer_instance
  letI : IsFiniteMeasure (sphProb (D + 1)) := ⟨by rw [measure_univ]; norm_num⟩
  calc ∫ w, F w ∂(sphProb (D + 1)) ≤ ∫ _w, B ∂(sphProb (D + 1)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) (integrable_const B)
          (hae.mono fun w hw => hB w hw)
    _ = B := by
      rw [integral_const]
      simp [Measure.real]

def secTraceHom {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ} (x : κ → Ω)
    (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (n : ℕ) : sec ℤ x n →+ Ω :=
  AddMonoidHom.mk' (fun s => secTrace x e n s) fun s t => secTrace_add x e h n s.2 t.2

def adtEnum (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) → ℕ :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).1

theorem sum_adtEnum {M : Type*} [AddCommMonoid M] (D N : ℕ) (f : (Fin (D + 1) → ℕ) → M) :
    ∑ i, f (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, f a := by
  exact (Fintype.sum_equiv (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm _
    (fun x => f x.1) fun _ => rfl).trans (Finset.sum_coe_sort _ f)

def monoDiag (D N δ : ℕ) : Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card))
    (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) ℂ :=
  Matrix.diagonal fun p => ((monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) : ℝ) : ℂ)

theorem monoDiag_posDef (D N δ : ℕ) : (monoDiag D N δ).PosDef := by
  rw [monoDiag, Matrix.posDef_diagonal_iff]
  intro p
  have h : 0 < monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    unfold monoNormSq
    positivity
  exact_mod_cast h

theorem neg_log_det_monoDiag (D N δ : ℕ) :
    -(1 / 2) * Real.log (monoDiag D N δ).det.re = δ * chiP D N := by
  have hpos : ∀ a : Fin (D + 1) → ℕ, 0 < monoNormSq a := fun a => by
    unfold monoNormSq
    positivity
  have hdet : (monoDiag D N δ).det.re =
      ∏ p : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card),
        monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    rw [monoDiag, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [hdet, Real.log_prod fun p _ => (hpos _).ne']
  rw [← finProdFinEquiv.sum_comp (fun p => Real.log (monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2)))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_adtEnum D N (fun a => Real.log (monoNormSq a)), chiP]
  ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def gbPsi (e : Fin (D + 1) → Ix κ) : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ) :=
  LinearMap.pi fun k => LinearMap.proj (fun _ => (e k).2)

theorem gb_segre_apply (z : Ix κ → ℂ) (i : (k : Unit) → GlobalTheory κ k) :
    segre (ι := GlobalTheory κ) z i = z ⟨(), i ()⟩ := by
  simp only [segre, Fintype.prod_unique]

theorem gbPsi_segre (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    gbPsi e (segre (ι := GlobalTheory κ) z) = fun k => z (e k) := by
  funext k
  simp only [gbPsi, LinearMap.pi_apply, LinearMap.proj_apply]
  rw [gb_segre_apply]

theorem gb_segre_injective : Function.Injective (segre (ι := GlobalTheory κ)) := by
  intro z z' h
  funext p
  have := congrFun h (fun _ => p.2)
  rw [gb_segre_apply, gb_segre_apply] at this
  exact this

theorem gb_mcPts_eq (P : Ideal (MRing (GlobalTheory κ))) : mcPts P = pts P := by
  ext z
  simp only [mcPts, pts, conePts, Set.mem_setOf_eq]
  refine and_congr_left' ⟨fun h h0 => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h ()
    exact hi (congrFun h0 _)
  · by_contra hne
    push_neg at hne
    exact h (funext fun p => hne p.2)

theorem gb_fibre_eq (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (y : Fin D → ℂ) :
    fibre (coordIdeal ℤ x) (gbPsi e) y = segre (ι := GlobalTheory κ) '' prFib x e (Fin.cons 1 y) := by
  ext w
  simp only [fibre, Set.mem_setOf_eq, Set.mem_image, prFib, gb_mcPts_eq]
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    rw [gbPsi_segre] at hΨ
    exact ⟨z, ⟨hz, fun k => congrFun hΨ k⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hk⟩, rfl⟩
    refine ⟨z, hz, rfl, ?_⟩
    rw [gbPsi_segre]
    funext k
    exact hk k

theorem gb_prFib_smul (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) {c : ℂ}
    (hc : c ≠ 0) : prFib x e (c • w) = (fun z => c • z) '' prFib x e w := by
  ext z
  constructor
  · rintro ⟨hz, hk⟩
    refine ⟨c⁻¹ • z, ⟨smul_mem_pts_coord x hz (inv_ne_zero hc), fun k => ?_⟩, ?_⟩
    · simp [hk k, hc]
    · simp [smul_smul, hc]
  · rintro ⟨z', ⟨hz', hk⟩, rfl⟩
    exact ⟨smul_mem_pts_coord x hz' hc, fun k => by simp [hk k]⟩

theorem gb_sum_cons (y : Fin D → ℂ) :
    ∑ k, ‖(Fin.cons 1 y : Fin (D + 1) → ℂ) k‖ ^ 2 = 1 + ∑ i, ‖y i‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp

theorem gb_sheetDensity {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric (C := ℂ) (ι := Ix κ)}
    (hFS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsPullFS x e m) {y : Fin D → ℂ} {w : ((k : Unit) → GlobalTheory κ k) → ℂ}
    (h : ∃ γ, IsSheet (coordIdeal ℤ x) (gbPsi e) y w γ) :
    sheetDensity (coordIdeal ℤ x) (gbPsi e) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.purePot m D) (fun _ => 1) y w =
      maDensity (fun _ : Fin D => gbPot) y := by
  have hs := h.choose_spec
  unfold sheetDensity
  rw [dite_eq_left h]
  simp only [one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [hs.2] with y' hy'
  obtain ⟨-, hmem, hΨ⟩ := hy'
  rw [gb_mcPts_eq] at hmem
  rw [gbPsi_segre] at hΨ
  simp only [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.purePot, gbPot]
  rw [hFS _ hmem, ← gb_sum_cons y']
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← congrFun hΨ k]

def gbConsL (D : ℕ) : (Fin D → ℂ) →L[ℂ] (Fin (D + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.cons 0 y
      map_add' := fun a b => by ext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
      map_smul' := fun c a => by ext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp }

theorem gb_scaledCons_eq (c : ℂ) (y : Fin D → ℂ) :
    c • (Fin.cons 1 y : Fin (D + 1) → ℂ) = c • (Fin.cons 1 0 : Fin (D + 1) → ℂ) + (c • gbConsL D) y := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp [gbConsL]

theorem gb_analytic_scaledCons (c : ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Set.univ := by
  have h : (fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) =
      fun y => c • (Fin.cons 1 0 : Fin (D + 1) → ℂ) + (c • gbConsL D) y := funext (gb_scaledCons_eq c)
  rw [h]
  exact analyticOnNhd_const.add ((c • gbConsL D).analyticOnNhd _)

theorem gb_exists_scale {Δ : MvPolynomial (Fin (D + 1)) ℂ} (hΔ : Δ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ y₀ : Fin D → ℂ, eval (c • (Fin.cons 1 y₀ : Fin (D + 1) → ℂ)) Δ ≠ 0 := by
  have h1 : Δ * X 0 ≠ 0 := mul_ne_zero hΔ (X_ne_zero _)
  obtain ⟨w, hw⟩ : ∃ w, eval w (Δ * X 0) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (MvPolynomial.funext (fun w => by simpa using hne w))
  rw [eval_mul, eval_X] at hw
  have hw0 : w 0 ≠ 0 := right_ne_zero_of_mul hw
  refine ⟨w 0, hw0, fun i => w i.succ / w 0, ?_⟩
  have hw' : w 0 • (Fin.cons 1 (fun i => w i.succ / w 0) : Fin (D + 1) → ℂ) = w := by
    ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp
    · first
      | (simp [hw0]; done)
      | (simp; field_simp)
  rw [hw']
  exact left_ne_zero_of_mul hw

theorem gb_ae_good {c : ℂ} {Δ : MvPolynomial (Fin (D + 1)) ℂ} {y₀ : Fin D → ℂ}
    (h₀ : eval (c • (Fin.cons 1 y₀ : Fin (D + 1) → ℂ)) Δ ≠ 0) :
    ∀ᵐ y : Fin D → ℂ, eval (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Δ ≠ 0 := by
  have hpoly : ∀ p : MvPolynomial (Fin (D + 1)) ℂ, AnalyticOnNhd ℂ (fun w => eval w p) Set.univ := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      simp only [eval_C]
      exact analyticOnNhd_const
    next p q hp hq =>
      simp only [map_add (f := _)]
      exact hp.add hq
    next p i hp =>
      simp only [map_mul, eval_X]
      exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) i).analyticOnNhd _)
  have hf : AnalyticOnNhd ℂ ((fun w => eval w Δ) ∘ fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ))
      Set.univ := (hpoly Δ).comp (gb_analytic_scaledCons c) (Set.mapsTo_univ _ _)
  have h := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ hf
    ⟨y₀, Set.mem_univ _, h₀⟩
  rw [ae_iff]
  simpa using h

theorem gb_fibre_good {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {Δ : MvPolynomial (Fin (D + 1)) ℂ}
    (hΔ : IsDiscr x e Δ) {c : ℂ} (hc : c ≠ 0) {y : Fin D → ℂ}
    (hy : eval (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Δ ≠ 0) :
    (fibre (coordIdeal ℤ x) (gbPsi e) y).Finite ∧
      (fibre (coordIdeal ℤ x) (gbPsi e) y).ncard = projDeg x e ∧
      ∀ w ∈ fibre (coordIdeal ℤ x) (gbPsi e) y, ∃ γ, IsSheet (coordIdeal ℤ x) (gbPsi e) y w γ := by
  obtain ⟨hfin, hcard, hsec, -⟩ := hΔ.2 _ hy
  have hS : prFib x e (Fin.cons 1 y) =
      (fun z => c⁻¹ • z) '' prFib x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) := by
    rw [← gb_prFib_smul x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) (inv_ne_zero hc), smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hinj : Function.Injective (fun z : Ix κ → ℂ => segre (ι := GlobalTheory κ) (c⁻¹ • z)) :=
    fun a b hab => smul_right_injective _ (inv_ne_zero hc) (gb_segre_injective hab)
  have hF : fibre (coordIdeal ℤ x) (gbPsi e) y =
      (fun z => segre (ι := GlobalTheory κ) (c⁻¹ • z)) '' prFib x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) := by
    rw [gb_fibre_eq, hS, Set.image_image]
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    exact hfin.image _
  · rw [hF, Set.ncard_image_of_injective _ hinj, hcard]
  · intro w hw
    rw [hF] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    obtain ⟨U, Γ, hU, hWU, hΓ, hΓW, hΓU⟩ := hsec z hz
    refine ⟨fun y' => c⁻¹ • Γ (c • (Fin.cons 1 y' : Fin (D + 1) → ℂ)), ?_, ?_⟩
    · simp only [hΓW]
    · have hcont : Continuous (fun y' : Fin D → ℂ => c • (Fin.cons 1 y' : Fin (D + 1) → ℂ)) :=
        continuousOn_univ.1 (gb_analytic_scaledCons c).continuousOn
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hWU)] with y' hy'
      have hmem := hΓU _ hy'
      refine ⟨?_, ?_, ?_⟩
      · exact ((hΓ.differentiableAt (hU.mem_nhds hy')).comp y'
          ((gb_analytic_scaledCons c) y' (Set.mem_univ _)).differentiableAt).const_smul c⁻¹
      · rw [gb_mcPts_eq]
        exact smul_mem_pts_coord x hmem.1 (inv_ne_zero hc)
      · rw [gbPsi_segre]
        funext k
        simp [hmem.2 k, hc]

theorem gb_integrand_ae {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric (C := ℂ) (ι := Ix κ)}
    (hfr : IsProjFrame x e) (hFS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsPullFS x e m) :
    ∀ᵐ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (coordIdeal ℤ x) (gbPsi e) y,
        sheetDensity (coordIdeal ℤ x) (gbPsi e) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.purePot m D) (fun _ => 1) y w =
      (projDeg x e : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
  obtain ⟨Δ, hΔ⟩ := exists_isDiscr hfr
  obtain ⟨c, hc, y₀, h₀⟩ := gb_exists_scale hΔ.1
  filter_upwards [gb_ae_good h₀] with y hy
  obtain ⟨hfin, hcard, hsh⟩ := gb_fibre_good hΔ hc hy
  rw [finsum_mem_congr rfl (fun w hw => gb_sheetDensity hFS (hsh w hw)),
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin, hcard]

theorem gb_ptsIntegralAt {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric (C := ℂ) (ι := Ix κ)}
    (hfr : IsProjFrame x e) (hFS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsPullFS x e m) :
    ptsIntegralAt (coordIdeal ℤ x) (gbPsi e) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.purePot m D) (fun _ => 1) = projDeg x e := by
  unfold ptsIntegralAt
  rw [integral_congr_ae (gb_integrand_ae hfr hFS)]
  first
  | rw [integral_const_mul, integral_maDensity_gbPot, mul_one]
  | rw [integral_mul_left, integral_maDensity_gbPot, mul_one]

theorem gb_isGoodProj {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    IsGoodProj (coordIdeal ℤ x) (gbPsi e) := by
  intro z hz
  rw [gbPsi_segre]
  rw [gb_mcPts_eq] at hz
  obtain ⟨k, hk⟩ := exists_proj_ne_zero hfr hz
  intro h0
  exact hk (congrFun h0 k)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
