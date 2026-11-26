module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeLinearHolds

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PlusOp
section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeEqualHolds
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section tieop
variable {p : ℕ} [Fact p.Prime]

theorem int_Fpow {τ : Type} {r : ℕ} (L m : ℕ) (hmL : Nat.log p m ≤ L) (w e : Fin r → τ)
    {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) y) ∈ IntPol p τ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set Mc : ℝ := (p : ℝ) ^ L with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))
  let Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (Dc a) (Dc b) := by
    intro a b
    simp only [Dc, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl
  have hb : Bnd (p := p) 1 y := (intPol_iff_bnd y).mp hy
  have h1 := hF m le_rfl 1 zero_le_one y hb
  rw [← hFeq] at h1
  rw [intPol_iff_bnd, ← smul_smul]
  have h2 := bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1
  intro μ
  refine (h2 μ).trans (le_of_eq ?_)
  rw [Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))

variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem xi_free {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {v : BVar N r D.T.t} (hv : ∀ c, v ≠ xiVar N r D.T.t c) : pderiv v g = 0 :=
  ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)

theorem tieF_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) :
    tieF (wv D i) (ev D i) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y) * g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tieF_apply', tieF_apply', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c,
    mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]

theorem tieF_pow_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']

omit [NeZero r] in
theorem update_single (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp; ring
  · simp [hk]

theorem Y_iter (hF : HypJoin p (r := r) D) (i : Fin D.T.t) :
    ∀ m (j : Fin D.T.t → ℕ) (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y ∈
        Y p (r := r) (D.lettersAt (j + Pi.single i m) jp) D.T.J D.T.thr := by
  intro m
  induction m with
  | zero =>
    intro j jp y hy
    have h0 : j + Pi.single i 0 = j := by simp
    rw [h0, pow_zero, Module.End.one_apply]
    exact hy
  | succ m ih =>
    intro j jp y hy
    have h := hF _ jp i _ (ih j jp y hy)
    rw [update_single] at h
    rw [pow_succ', Module.End.mul_apply]
    exact h

theorem lat_tie (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by
  intro x hx
  have := span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) •
    (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  rw [LinearMap.smul_apply, tieF_pow_gen hB i y g
    (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)),
    ← smul_mul_assoc, ← map_smul]
  refine Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy)))
    (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩

end tieop

theorem lattice_equal_holds : LatTie := by
  intro p _ N r _ D hB hF j jp i m L hmL x hx
  exact lat_tie hB hF j jp i m L hmL x hx

end Formalism.InvariantFactorPaths.KP.LL
end

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section plusop
variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev po_d {σ : Type} (v : σ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] :=
  (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap

theorem po_Fsum {σ ι : Type} [DecidableEq ι]
    (Dc : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (Dc a) (Dc b))
    (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hdiv : ∀ a k l, ∀ x ∈ Λ l, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k) x) ∈ Λ (l + k))
    (L n : ℕ) (hn : Nat.log p n ≤ L) (S : Finset ι) :
    ∀ j ≤ n, ∀ l, ∀ x ∈ Λ l,
      (((p : ℚ_[p]) ^ (S.card * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) • ((∑ c ∈ S, Dc c) ^ j) x) ∈ Λ (l + j) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  induction S using Finset.induction_on with
  | empty =>
    intro j _ l x hx
    rcases j with _ | j
    · simpa using hx
    · simp
  | insert a S ha ih =>
    intro j hj l x hx
    have hc : Commute (Dc a) (∑ c ∈ S, Dc c) := Commute.sum_right _ _ _ (fun c _ => hcomm a c)
    rw [Finset.sum_insert ha, hc.add_pow j, Finset.card_insert_of_notMem ha,
      LinearMap.sum_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hkj : k ≤ j := by rw [Finset.mem_range] at hk; omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hkj
    have hne : ((j.choose k : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkj).ne'
    have hk0 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hjk0 : (((j - k).factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have key : (((j.factorial : ℚ_[p]) ^ 2))⁻¹ * ((j.choose k : ℕ) : ℚ_[p]) =
        (((j.choose k : ℕ) : ℚ_[p]))⁻¹ * ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ *
          ((((j - k).factorial : ℚ_[p]) ^ 2))⁻¹) := by
      rw [← hfac]
      push_cast
      field_simp
    have eq : ((p : ℚ_[p]) ^ ((S.card + 1) * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) •
        (Dc a ^ k * (∑ c ∈ S, Dc c) ^ (j - k) *
          ((j.choose k : ℕ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])) x =
        ((p : ℚ_[p]) ^ L * (((j.choose k : ℕ) : ℚ_[p]))⁻¹) • ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k)
          (((p : ℚ_[p]) ^ (S.card * L) * (((j - k).factorial : ℚ_[p]) ^ 2)⁻¹) •
            ((∑ c ∈ S, Dc c) ^ (j - k)) x)) := by
      simp only [Module.End.mul_apply, Module.End.natCast_apply,
        map_smul, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul]
      congr 1
      rw [mul_assoc, key, add_mul, one_mul, pow_add]
      ring
    rw [eq]
    have h1 := ih (j - k) (by omega) l x hx
    have h2 := hdiv a k _ _ h1
    rw [show l + (j - k) + k = l + j by omega] at h2
    refine smul_mem_of_norm _ ?_ h2
    rw [norm_mul, norm_pow, Padic.norm_p]
    have h3 : ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ L :=
      (norm_choose_inv_le j k hkj).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hn))
    calc ((p : ℝ)⁻¹) ^ L * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ ((p : ℝ)⁻¹) ^ L * (p : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]

theorem po_pow_right {σ : Type} (v : σ) {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0)
    (g : MvPolynomial σ ℚ_[p]) (k : ℕ) : (po_d v ^ k) (a * g) = a * (po_d v ^ k) g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv v (a * _) = a * pderiv v _
    rw [pderiv_mul, ha, zero_mul, zero_add]

theorem po_pow_left {σ τ : Type} (f : τ → σ) (hf : Function.Injective f) (u : τ)
    (y : MvPolynomial τ ℚ_[p]) {g : MvPolynomial σ ℚ_[p]} (hg : pderiv (f u) g = 0) (k : ℕ) :
    (po_d (f u) ^ k) (rename f y * g) = rename f ((po_d u ^ k) y) * g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv (f u) (_ * g) = rename f (pderiv u _) * g
    rw [pderiv_mul, hg, mul_zero, add_zero, pderiv_rename hf]

theorem po_int {σ : Type} (v : σ) (k : ℕ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d v ^ k) y) ∈ IntPol p σ := by
  rw [intPol_iff_bnd] at hy ⊢
  have h := contr_divDeriv (p := p) v k 1 zero_le_one y hy
  intro m
  simpa using h m

variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem pderiv_xi_rename_chainEmb_eq_zero (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : Fin r) :
    pderiv (xiVar N r D.T.t c) (rename (chainEmb N r D.T.t) y) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (vars_rename _ _ h)
  exact xi_notin (D := D) c ⟨a, ha⟩

omit [NeZero r] in
theorem po_xi_inj {t : ℕ} : Function.Injective (xiVar N r t) := by
  intro a b h
  simpa [xiVar] using h

noncomputable abbrev po_R (p : ℕ) [Fact p.Prime] (N r t b : ℕ) : Submodule ℚ_[p] (MvPolynomial (BVar N r t) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p]
    {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}

omit [NeZero r] in
theorem po_R_step {t b : ℕ} (c : Fin r) {g : MvPolynomial (BVar N r t) ℚ_[p]} (hg : g ∈ po_R p N r t b) :
    pderiv (xiVar N r t c) g ∈ po_R p N r t (b - 1) := by
  classical
  rw [mem_restrictSupport_iff] at hg ⊢
  intro m hm
  have hm' : m + Finsupp.single (xiVar N r t c) 1 ∈ g.support := by
    rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  obtain ⟨h1, h2⟩ := hg (Finset.mem_coe.mpr hm')
  refine ⟨fun v hv => h1 v ?_, ?_⟩
  · rw [Finsupp.mem_support_iff] at hv ⊢
    rw [Finsupp.add_apply]
    omega
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h2
    rw [Finset.sum_eq_single c (fun d _ hd => Finsupp.single_eq_of_ne (fun h => hd (po_xi_inj h)))
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same] at h2
    omega

omit [NeZero r] in
theorem po_R_pow {t : ℕ} (c : Fin r) (k : ℕ) : ∀ (b : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]},
    g ∈ po_R p N r t b → (po_d (xiVar N r t c) ^ k) g ∈ po_R p N r t (b - k) := by
  induction k with
  | zero => intro b g hg; simpa using hg
  | succ k ih =>
    intro b g hg
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact po_R_step c (ih b hg)

omit [NeZero r] in
theorem po_xi_div {t b : ℕ} (c : Fin r) (k : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]}
    (hg : g ∈ XiPolZ p N r t b) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r t c) ^ k) g) ∈ XiPolZ p N r t (b - k) := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  exact Submodule.mem_inf.mpr ⟨(po_R p N r t (b - k)).smul_mem _ (po_R_pow c k b h1), po_int _ k h2⟩

theorem po_Y_iter (hU : HypU p (r := r) D) (c : Fin r) (j : Fin D.T.t → ℕ) :
    ∀ k (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (po_d (D.uPos, c) ^ k) y ∈ Y p (r := r) (D.lettersAt j (jp + k)) D.T.J D.T.thr := by
  intro k
  induction k with
  | zero => intro jp y hy; rw [pow_zero, Module.End.one_apply, add_zero]; exact hy
  | succ k ih =>
    intro jp y hy
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact hU j (jp + k) c _ (ih jp y hy)

theorem po_coord (hU : HypU p (r := r) D) (j : Fin D.T.t → ℕ) (c : Fin r) (k jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k) x) ∈ Lat p D (r := r) j (jp + k) := by
  intro x hx
  have := span_map_mem ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
    ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k)) _ (Lat p D (r := r) j (jp + k)) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  have hg' := po_xi_div c k hg
  have e : ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k))
      (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t) ((k.factorial : ℚ_[p])⁻¹ • (po_d (D.uPos, c) ^ k) y) *
        ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r D.T.t c) ^ k) g) := by
    have h1 := po_pow_left (p := p) (chainEmb N r D.T.t) chainEmb_inj (D.uPos, c) y
      (xi_free hg' (fun d => wU_ne_xi (D := D) c d)) k
    rw [← Module.End.mul_eq_comp, (PhiIntegrality.commute_pderiv _ _).mul_pow, LinearMap.smul_apply, Module.End.mul_apply,
      po_pow_right _ (pderiv_xi_rename_chainEmb_eq_zero (D := D) y c), map_smul, smul_mul_assoc, ← h1, mul_smul_comm, map_smul,
      smul_smul, sq, mul_inv]
    rfl
  rw [e, Nat.sub_sub] at *
  exact Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (po_Y_iter hU c j k jp y (yz_y hy)))
    (po_int _ k (yz_int hy)), _, hg', rfl⟩

end plusop

theorem lattice_plus_holds : LatPlus := by
  intro p _ N r _ D hB hU j jp m L hmL x hx
  classical
  have hcomm : ∀ a b : Fin r, Commute (po_d (p := p) (wU D a) ∘ₗ po_d (xiVar N r D.T.t a))
      (po_d (wU D b) ∘ₗ po_d (xiVar N r D.T.t b)) := by
    intro a b
    simp only [← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have h := po_Fsum (fun c : Fin r => po_d (p := p) (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) hcomm
    (fun l => Lat p D (r := r) j l) (fun a k l x hx => po_coord hU j a k l x hx) L m hmL Finset.univ
    m le_rfl jp x hx
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

end Formalism.InvariantFactorPaths.KP.LL
end

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PstScalMem
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

theorem tieP_smul {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k)
    (y : MvPolynomial σ k) : tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_smul_comm, map_smul, map_smul, smul_comm]

theorem pst_scal_mem {p : ℕ} [Fact p.Prime] {σ : Type} (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (a u m j k : ℕ) (hk : k ≤ j) (hu : a + Nat.log p j ≤ u) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1)
    (y : MvPolynomial σ ℚ_[p])
    (hy : (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) ∈ Λ) :
    ((s * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y) ∈ Λ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp1
  have e1 : (s * (p : ℚ_[p]) ^ (a + Nat.log p j + d) *
      (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y =
      (s * (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ (Nat.log p j) * (((j.choose k : ℕ) : ℚ_[p]))⁻¹)) •
        (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) := by
    rw [smul_smul, mul_inv, pow_add, pow_add]
    congr 1
    ring
  rw [e1]
  refine smul_mem_of_norm Λ ?_ hy
  have hpn : ∀ t : ℕ, ‖(p : ℚ_[p]) ^ t‖ = ((p : ℝ) ^ t)⁻¹ := by
    intro t
    rw [norm_pow, Padic.norm_p, inv_pow]
  rw [norm_mul, norm_mul, norm_mul, hpn, hpn]
  have h1 : ((p : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  have h2 : ((p : ℝ) ^ (Nat.log p j))⁻¹ * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ 1 := by
    have := PhiIntegrality.norm_choose_inv_le (p := p) j k hk
    rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
    exact this
  have h3 : ‖s‖ * ((p : ℝ) ^ d)⁻¹ ≤ 1 :=
    mul_le_one₀ hs (inv_nonneg.mpr (pow_pos hp0 _).le) h1
  exact mul_le_one₀ h3 (mul_nonneg (inv_nonneg.mpr (pow_pos hp0 _).le) (norm_nonneg _)) h2

theorem pair_induction_holds : PairStep := by
  intro p _ σ r w e zv sv hr hz o n z L u Λ h1 h2 hu l hl x hx
  constructor
  · rw [decomp w e zv sv hr hz (o - l) (n - l) z x (h1 l x hx), Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    simp only [mem_range] at hm
    refine Submodule.subset_span ⟨l + m, by omega,
      ((1 : ℚ_[p]) * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
        (((o - l + (n - l) + r + z - m).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
    · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ 1 (by simp) _ (h2 l m (by omega) x hx)
      exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
    · rw [Nat.sub_sub, Nat.sub_sub, one_mul, mul_smul, tieP_smul w e zv sv _ _ _ ((p : ℚ_[p]) ^ u),
        mul_smul_comm, pow_add, mul_assoc]
  · rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    by_cases hmm : min (o - l) (n - l) < m
    · rw [h1 l x hx m hmm]
      simp
    · refine Submodule.subset_span ⟨l + m, by omega,
        ((-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
          (((o - l + (n - l) + r + z - 1).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
      · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ _ (by simp) _ (h2 l m (by omega) x hx)
        exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
      · simp only [smul_eq_C_mul, div_eq_mul_inv, map_mul]
        ring

end Formalism.InvariantFactorPaths.KP.LL
end

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepPlus
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem sp_midGen_zero (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D 0 j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        (X (zP D r) ^ D.zPlus * PL p D (List.finRange D.T.t) j jp x)) := by
  have h1 : D.Eplus p (r := r) = ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) := rfl
  unfold midGen
  rw [h1]
  simp only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, List.drop_zero, mul_one]
  ring

theorem sp_gen_P (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * Pplus p D jp y =
      (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        tieP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y) := by
  rw [mul_assoc]
  rfl

theorem sp_wU_inj : Function.Injective (wU (r := r) D) := by
  intro c d h
  simp only [wU, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem sp_xi_inj : Function.Injective (xiVar N r D.T.t) := by
  intro c d h
  simp only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

end

theorem StepPlus_of : PairStep → LatPlus → PLLin → CommPL → ParamPL → PlusCondition := by
  intro hPS hLP hLin hComm hPar p _ N r _ D a u hB hr hdeg hBa hz hU hu
  have key : ∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      ((p : ℚ_[p]) ^ u • midGen p D 0 j jp x ∈ MidP p (r := r) D) ∧
      ((p : ℚ_[p]) ^ u • ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)) ∈ Mid p (r := r) D 0) := by
    intro j jp hOK x hx
    obtain ⟨T, hT⟩ := (hLin p N r D (List.finRange D.T.t) j jp).1
    have hcomm : ∀ (m : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
        (tieF (wU D) (xiVar N r D.T.t) ^ m) (T y) = T ((tieF (wU D) (xiVar N r D.T.t) ^ m) y) := by
      intro m y
      rw [hT, hT]
      exact (hComm p N r D hB (List.finRange D.T.t) j jp m y).2
    have hps := hPS p (BVar N r D.T.t) r (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) hr
      (fun c => ⟨by simp [wU, zP, scalZ], by simp [xiVar, zP, scalZ]⟩)
      (D.LL.deg D.uPos) D.B D.zPlus (Nat.log p (2 * a)) u
      (fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (r := r) j l))
      (by
        rintro l _ ⟨y, hy, rfl⟩ m hm
        rw [LinearMap.restrictScalars_apply, hcomm]
        have hb := biHom_plus (p := p) (D := D) j l y hy
        rw [deg_U hB] at hb
        rw [tieF_pow_apply_eq_zero_of_min_lt (wU D) (xiVar N r D.T.t) sp_wU_inj sp_xi_inj wU_ne_xi hb m hm, map_zero])
      (by
        rintro l m hm _ ⟨y, hy, rfl⟩
        rw [LinearMap.restrictScalars_apply, hcomm, ← map_smul]
        refine ⟨_, hLP p N r D hB hU j l m (Nat.log p (2 * a)) (Nat.log_mono_right ?_) y hy, rfl⟩
        exact le_trans (le_trans hm (min_le_left _ _)) (hdeg _))
      (by
        refine le_trans (Nat.add_le_add_left (Nat.log_mono_right ?_) _) hu
        have := hdeg D.uPos
        omega)
      jp hOK.2 (T x) ⟨x, hx, rfl⟩
    constructor
    · rw [sp_midGen_zero, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.1
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_gen_P,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
    · rw [sp_gen_P, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.2
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_midGen_zero,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
  let S : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
    (p : ℚ_[p]) ^ u • LinearMap.id
  constructor
  · intro v hv
    refine span_map_mem S _ (MidP p (r := r) D) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).1
  · intro v hv
    refine span_map_mem S _ (Mid p (r := r) D 0) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).2

end Formalism.InvariantFactorPaths.KP.LL
end

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LevelLatticeOf
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

lemma asm_num (p : ℕ) [Fact p.Prime] (a r : ℕ) (ha : 1 ≤ a) :
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h2 : (Nat.log p (6 * a + r) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h3 : ((r * Nat.log p (2 * a) + Nat.log p (6 * a + r) : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * lgV2 p a r := by
    push_cast
    unfold lgV2
    have := mul_le_mul_of_nonneg_left h1 hr
    nlinarith
  exact_mod_cast h3.trans (Nat.le_ceil _)

lemma asm_chain (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (M : ℕ → Submodule ℤ_[p] V) (u t : ℕ)
    (h : ∀ k < t, (∀ v ∈ M (k + 1), (p : ℚ_[p]) ^ u • v ∈ M k) ∧ (∀ v ∈ M k, (p : ℚ_[p]) ^ u • v ∈ M (k + 1))) :
    ∀ k ≤ t, (∀ v ∈ M k, (p : ℚ_[p]) ^ (k * u) • v ∈ M 0) ∧ (∀ v ∈ M 0, (p : ℚ_[p]) ^ (k * u) • v ∈ M k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨s1, s2⟩ := h k (by omega)
    constructor
    · intro v hv
      have := i1 _ (s1 v hv)
      rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
    · intro v hv
      have := s2 _ (i2 v hv)
      rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this

lemma asm_span (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (A B : Submodule ℤ_[p] V) (K : ℕ) (h : ∀ v ∈ A, (p : ℚ_[p]) ^ K • v ∈ B) :
    Submodule.span ℚ_[p] (A : Set V) ≤ Submodule.span ℚ_[p] (B : Set V) := by
  have hp : ((p : ℚ_[p]) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [Submodule.span_le]
  intro x hx
  have h1 : (p : ℚ_[p]) ^ K • x ∈ Submodule.span ℚ_[p] (B : Set V) := Submodule.subset_span (h x hx)
  have h2 := Submodule.smul_mem _ (((p : ℚ_[p]) ^ K)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h2

theorem LevelLattice_of : MidTop → MidPEq → JoinCondition → PlusCondition → Formalism.GM.M.LevelLattice := by
  intro hTop hPEq hTie hPlus p _ N r _ D a hOK hr ha hdeg hB hz hzP hYT hYU
  have hnum := asm_num p a r ha
  generalize ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ = u at hnum ⊢
  have hT : HypJoin p (r := r) D := hYT
  have hU : HypU p (r := r) D := hYU
  obtain ⟨c1, c2⟩ := asm_chain p (fun k => Mid p (r := r) D k) u D.T.t
    (hTie p N r D a u hOK hr hdeg hz hT hnum) D.T.t le_rfl
  obtain ⟨q1, q2⟩ := hPlus p N r D a u hOK hr hdeg hB hzP hU hnum
  rw [← hTop p N r D, ← hPEq p N r D]
  have k1 : ∀ x ∈ Mid p (r := r) D D.T.t, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ MidP p (r := r) D := by
    intro x hx
    have := q1 _ (c1 x hx)
    rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this
  have k2 : ∀ x ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ Mid p (r := r) D D.T.t := by
    intro x hx
    have := c2 _ (q2 x hx)
    rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
  exact ⟨le_antisymm (asm_span p _ _ _ k1) (asm_span p _ _ _ k2), k1, k2⟩

end Formalism.InvariantFactorPaths.KP.LL
end

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepTie
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section steptie
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

noncomputable def stQ (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus

theorem st_drop (t k : ℕ) (hk : k < t) :
    (List.finRange t).drop k = ⟨k, hk⟩ :: (List.finRange t).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  congr 1
  ext
  simp

theorem st_notin (t k : ℕ) (hk : k < t) : (⟨k, hk⟩ : Fin t) ∉ (List.finRange t).drop (k + 1) := by
  have h := List.Nodup.sublist (List.drop_sublist k (List.finRange t)) (List.nodup_finRange t)
  rw [st_drop t k hk] at h
  exact (List.nodup_cons.1 h).1

theorem st_filter (t k : ℕ) (hk : k < t) :
    (univ.filter (fun i : Fin t => i.val < k + 1)) = insert ⟨k, hk⟩ (univ.filter (fun i : Fin t => i.val < k)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  constructor
  · intro h
    omega
  · intro h
    omega

variable {D}

private theorem st_vec_lemma {N : ℕ} (LL : Letters N) (T : TieData) (hA : T.Admissible LL)
    (b kk : Fin T.t) (h : T.pos b = T.pos kk + 1) : False := by
  have hA' : _ ∧ _ ∧ _ := hA
  obtain ⟨-, hv, -⟩ := hA'
  obtain ⟨h1, hb1, -⟩ := hv b
  obtain ⟨h2, -, hk2⟩ := hv kk
  have he : (⟨T.pos b, by omega⟩ : Fin N) = ⟨T.pos kk + 1, h2⟩ := Fin.ext h
  rw [he, hk2] at hb1
  exact Bool.false_ne_true hb1

theorem st_Pt (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (kk : Fin D.T.t)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    Pt p D j jp kk y = tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk)
      (D.LL.deg (D.letterAt (D.T.pos kk)) - j kk) (D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk) (D.T.z kk) y := by
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨hA, hlt, -, hN⟩ := hB'
  have hA' : _ ∧ _ ∧ _ := hA
  have hinj : Function.Injective D.T.pos := hA'.1.injective
  have hk1 := hlt kk
  have hu := D.uPos.2
  have e1 : ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos kk := by
    show min (D.T.pos kk) (N - 1) = D.T.pos kk
    omega
  have e2 : ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos kk + 1 := by
    show min (D.T.pos kk + 1) (N - 1) = D.T.pos kk + 1
    omega
  have hs1 : (∑ i, if D.T.pos kk = D.T.pos i ∨ D.T.pos kk = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact hb (hinj h.symm)
      · exact st_vec_lemma D.LL D.T hA kk b h)) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inl rfl)
  have hs2 : (∑ i, if D.T.pos kk + 1 = D.T.pos i ∨ D.T.pos kk + 1 = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact st_vec_lemma D.LL D.T hA b kk h.symm
      · exact hb (hinj (by omega)))) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inr rfl)
  have hne1 : ¬ (D.letterAt (D.T.pos kk) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e1] at h'
    omega
  have hne2 : ¬ (D.letterAt (D.T.pos kk + 1) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e2] at h'
    omega
  have h1 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)) = D.LL.deg (D.letterAt (D.T.pos kk)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk)) - (∑ i, if ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk) = D.uPos then jp else 0) = _
    rw [e1, hs1, if_neg hne1, Nat.sub_zero]
  have h2 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1)) = D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk + 1)) - (∑ i, if ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk + 1) = D.uPos then jp else 0) = _
    rw [e2, hs2, if_neg hne2, Nat.sub_zero]
  show tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk) y = _
  rw [h1, h2]

theorem st_mid_succ (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D (k + 1) j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        (X (zi D r ⟨k, hk⟩) ^ D.T.z ⟨k, hk⟩ * PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hZ : (∏ i : Fin D.T.t with i.val < k + 1,
      (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i) =
      (X (zi D r ⟨k, hk⟩) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z ⟨k, hk⟩ *
        ∏ i : Fin D.T.t with i.val < k, (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i := by
    rw [st_filter _ k hk, Finset.prod_insert (by simp)]
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k + 1, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x = _
  rw [hE, hZ]
  simp only [stQ]
  ring

theorem st_mid (hB : D.BlockOK) (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D k j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
          (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hP : PL p D ((List.finRange D.T.t).drop k) j jp x =
      tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
        (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x) := by
    rw [st_drop _ k hk]
    exact st_Pt p hB j jp ⟨k, hk⟩ _
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x = _
  rw [hE, hP]
  simp only [stQ]
  ring

theorem st_Q_update (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) :
    stQ p (r := r) D k kk (Function.update j kk l) jp = stQ p D k kk j jp := by
  have h : (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ Function.update j kk l i) =
      ∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]
  simp only [stQ, h]

theorem st_wv_inj (kk : Fin D.T.t) : Function.Injective (wv (r := r) D kk) := by
  intro c d h
  exact (Prod.mk.inj (Sum.inl.inj h)).2

theorem st_ev_inj (kk : Fin D.T.t) : Function.Injective (ev (r := r) D kk) := by
  intro c d h
  exact (Prod.mk.inj (Sum.inl.inj h)).2

theorem st_wv_ne_ev (hB : D.BlockOK) (kk : Fin D.T.t) (c d : Fin r) : wv D kk c ≠ ev D kk d := by
  intro h
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨-, hlt, -, hN⟩ := hB'
  have h2 := hlt kk
  have h3 := D.uPos.2
  have h1 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  change min (D.T.pos kk) N = min (D.T.pos kk + 1) N at h1
  omega

theorem st_levelOK (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) (h : D.LevelOK j jp)
    (hl : l ≤ min (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1)))) :
    D.LevelOK (Function.update j kk l) jp := by
  delta Formalism.GM.M.BlockData.LevelOK at h ⊢
  refine ⟨fun i => ?_, h.2⟩
  rw [Function.update_apply]
  split_ifs with hi
  · subst hi
    exact ⟨le_trans hl (min_le_left _ _), le_trans hl (min_le_right _ _)⟩
  · exact h.1 i

theorem st_gen (hPS : PairStep) (hLT : LatTie) (hLin : PLLin) (hC : CommPL) (hPar : ParamPL) (a u : ℕ)
    (hB : D.BlockOK) (hr : 1 ≤ r) (hdeg : ∀ x, D.LL.deg x ≤ 2 * a) (hzz : ∀ i, D.T.z i ≤ 2 * a)
    (hH : HypJoin p (r := r) D) (hu : r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u) (k : ℕ) (hk : k < D.T.t)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (hOK : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Lat p D (r := r) j jp) :
    (p : ℚ_[p]) ^ u • midGen p D (k + 1) j jp x ∈ Mid p (r := r) D k ∧
      (p : ℚ_[p]) ^ u • midGen p D k j jp x ∈ Mid p (r := r) D (k + 1) := by
  obtain ⟨T, hT⟩ := (hLin p N r D ((List.finRange D.T.t).drop (k + 1)) j jp).1
  have hnot := st_notin D.T.t k hk
  generalize hkk : (⟨k, hk⟩ : Fin D.T.t) = kk at hnot
  generalize hL' : (List.finRange D.T.t).drop (k + 1) = L' at hnot hT
  let Λ : ℕ → Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) := fun l =>
    Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (Function.update j kk l) jp)
  have hcomm : ∀ m y, (tieF (wv D kk) (ev D kk) ^ m) (T y) = T ((tieF (wv D kk) (ev D kk) ^ m) y) := by
    intro m y
    rw [hT, hT]
    exact (hC p N r D hB L' j jp m y).1 kk hnot
  have ho := hdeg (D.letterAt (D.T.pos kk))
  have hn := hdeg (D.letterAt (D.T.pos kk + 1))
  have hz' := hzz kk
  have key := hPS p (BVar N r D.T.t) r (wv D kk) (ev D kk) (zi D r kk) (si D r kk) hr
    (fun c => ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩)
    (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk)
    (Nat.log p (2 * a)) u Λ
    (by
      rintro l x' ⟨x'', hx'', rfl⟩ m hm
      show (tieF (wv D kk) (ev D kk) ^ m) (T x'') = 0
      have hb := biHom_tie hB (Function.update j kk l) jp kk x'' hx''
      rw [deg_lettersAt_pos hB, deg_lettersAt_pos_succ hB, Function.update_self] at hb
      rw [hcomm, tieF_pow_apply_eq_zero_of_min_lt (wv D kk) (ev D kk) (st_wv_inj kk) (st_ev_inj kk) (st_wv_ne_ev hB kk) hb m hm,
        map_zero])
    (by
      rintro l m hm x' ⟨x'', hx'', rfl⟩
      have h := hLT p N r D hB hH (Function.update j kk l) jp kk m (Nat.log p (2 * a))
        (Nat.log_mono_right (le_trans hm (le_trans (min_le_left _ _) ho))) x'' hx''
      have he : Function.update j kk l + Pi.single kk m = Function.update j kk (l + m) := by
        funext i
        by_cases hi : i = kk
        · subst hi; simp
        · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
      rw [he] at h
      refine ⟨_, h, ?_⟩
      show T _ = _ • (tieF (wv D kk) (ev D kk) ^ m) (T x'')
      rw [map_smul, hcomm])
    (le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu)
    (j kk) (le_min (hOK.1 kk).1 (hOK.1 kk).2) (T x)
    ⟨x, by rw [Function.update_eq_self]; exact hx, rfl⟩
  subst hkk
  subst hL'
  constructor
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D k) ?_ _ key.1
    · rw [st_mid_succ p k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid p hB k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D (k + 1)) ?_ _ key.2
    · rw [st_mid p hB k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid_succ p k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl

end steptie

theorem StepTie_of : PairStep → LatTie → PLLin → CommPL → ParamPL → JoinCondition := by
  intro hPS hLT hLin hC hPar p _ N r _ D a u hB hr hdeg hzz hH hu k hk
  have hc : ∀ v : MvPolynomial (BVar N r D.T.t) ℚ_[p], (p : ℚ_[p]) ^ u • v = ((p : ℤ_[p]) ^ u) • v := by
    intro v
    rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ u) v, map_pow, map_natCast]
  have key : ∀ k₁ k₂ : ℕ, (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      (p : ℚ_[p]) ^ u • midGen p D k₁ j jp x ∈ Mid p (r := r) D k₂) →
      ∀ v ∈ Mid p (r := r) D k₁, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k₂ := by
    intro k₁ k₂ hg v hv
    rw [hc]
    have hle : Mid p (r := r) D k₁ ≤ (Mid p (r := r) D k₂).comap
        (((p : ℤ_[p]) ^ u) • LinearMap.id :
          MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p]) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨j, jp, hOK, x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hc]
      exact hg j jp hOK x hx
    have h2 := Submodule.mem_comap.1 (hle hv)
    rwa [LinearMap.smul_apply, LinearMap.id_apply] at h2
  exact ⟨key (k + 1) k (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).1),
    key k (k + 1) (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).2)⟩

end Formalism.InvariantFactorPaths.KP.LL
end

namespace Formalism.InvariantFactorPaths.KP.Top

open Formalism.InvariantFactorPaths.KP.LL

theorem pairStep : PairStep := pair_induction_holds
theorem latTie : LatTie := lattice_equal_holds
theorem latPlus : LatPlus := lattice_plus_holds
theorem plLin : PLLin := lattice_linear_holds
theorem commPL : CommPL := comm_lattice_holds
theorem paramPL : ParamPL := param_lattice_holds
theorem midTop : MidTop := middle_top_holds
theorem midPEq : MidPEq := middle_p_eq_holds
theorem stepTie : JoinCondition := StepTie_of pairStep latTie plLin commPL paramPL
theorem stepPlus : PlusCondition := StepPlus_of pairStep latPlus plLin commPL paramPL
theorem levelLattice : Formalism.GM.M.LevelLattice := LevelLattice_of midTop midPEq stepTie stepPlus

end Formalism.InvariantFactorPaths.KP.Top
