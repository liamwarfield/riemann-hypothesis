module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictionMinMaxIntHolds

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementA
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def PartnerDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (k : ℕ) (g : Fin k → Vs) (D : ℝ),
    LinearIndependent ℤ_[p] g →
    (∀ u ∈ Submodule.span ℤ_[p] (Set.range g),
      (∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a) →
      ∃ u' ∈ Submodule.span ℤ_[p] (Set.range g), (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    (p : ℝ) ^ (-(D * k)) ≤ ‖(Matrix.of fun a b => be (g a) (g b)).det‖

def GradedPieceBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D c : ℕ) (κ : ℝ),
    ProjAt p LLw J M ρ w e D → SatAt p LLw J M ρ w e c → ((D + 2 * c : ℕ) : ℝ) ≤ κ →
    ∀ (k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
      (p : ℝ) ^ (-(κ * k)) ≤
        ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

end Formalism.InvariantFactorPaths.L4
end

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.PartnerDeterminantHolds
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M MvPolynomial Finset

theorem partner_determinant_holds : PartnerDet := by
  intro p _ Vs _ _ _ _ be k g D hli hpart
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG
  obtain ⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩ := Formalism.GM.TM.smith_qp smith_form_p_adic_integers G
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  let U' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨U x y, hU x y⟩
  let V' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨V x y, hV x y⟩
  have hU'map : U'.map φ = U := by ext x y; rfl
  have hU'det : IsUnit U'.det := by
    rw [PadicInt.isUnit_iff]
    have : ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det := by
      rw [← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]; rfl
    rw [PadicInt.norm_def, this, hUd]
  set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW
  have hWU : W * U' = 1 := Matrix.nonsing_inv_mul _ hU'det
  have hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x := fun a x => by
    rw [← PadicInt.algebraMap_apply, algebraMap_smul]

  have hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖ := by
    intro i
    set u : Vs := ∑ a, W i a • g a with hu
    have huL : u ∈ Submodule.span ℤ_[p] (Set.range g) :=
      Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩
    have hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a := by
      intro a x hx hux
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx
      have h0 : ∑ b, (W i b - a * c b) • g b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [← hu, hux, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0
      have h2 : (W * U') i i = a * ∑ b, c b * U' b i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sub_eq_zero.mp (h1 b)]; ring
      rw [hWU, Matrix.one_apply_eq] at h2
      exact IsUnit.of_mul_eq_one _ h2.symm
    obtain ⟨u', hu'L, hu'⟩ := hpart u huL hprim
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L
    have hWG : ∀ b, be u (g b) = dg i * V i b := by
      intro b
      have e1 : be u (g b) = ((W.map φ) * G) i b := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
      have e2 : (W.map φ) * U = 1 := by
        rw [← hU'map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      rw [e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]
    have hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p]) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, PadicInt.coe_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]
      show _ = dg i * ((c b : ℚ_[p]) * V i b)
      ring
    rw [hval, norm_mul] at hu'
    refine hu'.trans ?_
    calc ‖dg i‖ * ‖((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])‖ ≤ ‖dg i‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖dg i‖ := mul_one _
  rw [hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one,
    norm_prod]
  calc (p : ℝ) ^ (-(D * k)) = ∏ _i : Fin k, (p : ℝ) ^ (-D) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]
        congr 1; ring
    _ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod₀ (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i

section Gr
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem grLat_le_int (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ IntPol p (Fin (K + 1) × Fin r) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ IntPol p (Fin (K + 1) × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2
  refine Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_
  rw [Formalism.GM.MeanGammaLemmas.coeff_initPart]
  split_ifs
  · exact Formalism.CountingSumsFrames.intPol_norm f hfI m
  · simp

theorem grLat_le_pol (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfM : f ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hfP : f ∈ Pol p r LLw :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1
  show initPart v e f ∈ Pol p r LLw
  unfold Pol at hfP ⊢
  rw [mem_restrictSupport_iff] at hfP ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart] at hm
  refine hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
  intro h0
  apply hm
  rw [h0, ite_self]

end Gr

theorem graded_piece_bound_holds : GradedPieceBound := by
  intro p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Pr, hPr⟩ := hProj
  have key := partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli
    ?_
  · exact key
  intro u hu hprim
  rw [hspan] at hu hprim
  set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr
  set XX := grSpan p LLw J M ρ w e with hXX
  have hGX : ∀ x ∈ Gr, x ∈ XX := fun x hx => Submodule.subset_span hx
  have hu0 : u ≠ 0 := by
    intro h0
    have := hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])
    exact not_isUnit_zero this
  have huI : u ∈ IntPol p (Fin (K + 1) × Fin r) := grLat_le_int LLw J M ρ w _ e hu
  have huP : u ∈ Pol p r LLw := grLat_le_pol LLw J M ρ w _ e hu
  have hne : u.support.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image u.support (fun m => ‖AddMonoidAlgebra.coeff u m‖) hne
  set a := AddMonoidAlgebra.coeff u m with ha
  have ha0 : a ≠ 0 := mem_support_iff.mp hm
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hmD : MultiDeg LLw m := by
    unfold Pol at huP
    rw [mem_restrictSupport_iff] at huP
    exact huP (Finset.mem_coe.mpr hm)
  set u0 := a⁻¹ • u with hu0def
  have hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_
    rw [hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]
    by_cases hm' : m' ∈ u.support
    · exact hmax m' hm'
    · rw [notMem_support_iff.mp hm', norm_zero]; exact han.le
  have hu0X : u0 ∈ XX := XX.smul_mem _ (hGX u hu)
  have hu0c : ‖AddMonoidAlgebra.coeff u0 m‖ = 1 := by
    rw [hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]
  have huu0 : u = a • u0 := by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr := hSat u0 hu0X hu0I
  have hpc : ((p : ℚ_[p]) ^ c) ≠ 0 := pow_ne_zero _ hpQ
  have hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]
  have hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]

  have hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1 := by
      rw [norm_div, hnpc, div_inv_eq_mul]
      have hpc' : (0 : ℝ) < (p : ℝ) ^ c := by positivity
      calc ‖a‖ * (p : ℝ) ^ c < ((p : ℝ) ^ c)⁻¹ * (p : ℝ) ^ c := mul_lt_mul_of_pos_right hlt hpc'
        _ = 1 := inv_mul_cancel₀ hpc'.ne'
    let b : ℤ_[p] := ⟨a / (p : ℚ_[p]) ^ c, hb.le⟩
    have hub : u = b • (((p : ℚ_[p]) ^ c) • u0) := by
      rw [← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]
      show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0
      rw [div_mul_cancel₀ _ hpc]; exact huu0
    have hunit := hprim b _ hy hub
    rw [PadicInt.isUnit_iff] at hunit
    have : ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖ := rfl
    linarith
  obtain ⟨hP1, hP2, hP3⟩ := hPr m hmD
  refine ⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩
  · rw [hspan]
    exact hSat _ (XX.smul_mem _ hP1) hP2
  · rw [Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']
    have e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1) := by
      unfold fockN
      rw [hP3 u (hGX u hu)]
      conv_lhs => rw [huu0]
      rw [Formalism.GM.TM.fock_smul_left, mul_div_assoc]
    have e2 := Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c
    rw [e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]
    have hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹ := by positivity
    have hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹ := by positivity
    have h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    gcongr

end Formalism.InvariantFactorPaths.L4
end

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {σ : Type}

private theorem coeff_initPart_eq_ite (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (n : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (initPart v e f) n = if n v = e then AddMonoidAlgebra.coeff f n else 0 := by
  classical
  unfold initPart
  rw [coeff_sum]
  simp only [apply_ite (AddMonoidAlgebra.coeff · n), coeff_monomial, AddMonoidAlgebra.coeff_zero, Pi.zero_apply]
  rw [Finset.sum_eq_single n]
  · by_cases h : n v = e <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro hn
    have h0 : AddMonoidAlgebra.coeff f n = 0 := by simpa [mem_support_iff] using hn
    simp [h0]

theorem p_pow_ne_zero (n : ℕ) : ((p : ℚ_[p]) ^ n) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

noncomputable def strip (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun f := (initPart v e f).divMonomial (Finsupp.single v e)
  map_add' x y := by
    rw [initPart_add]; ext m; simp only [coeff_divMonomial, MvPolynomial.coeff_add]
  map_smul' a x := by
    rw [initPart_smul]; ext m; simp only [coeff_divMonomial, coeff_smul, RingHom.id_apply]

theorem coeff_strip (v : σ) (e : ℕ) (n : σ →₀ ℕ) (f : MvPolynomial σ ℚ_[p]) :
    AddMonoidAlgebra.coeff (strip p v e f) n = if n v = 0 then AddMonoidAlgebra.coeff f (Finsupp.single v e + n) else 0 := by
  classical
  show AddMonoidAlgebra.coeff ((initPart v e f).divMonomial (Finsupp.single v e)) n = _
  rw [coeff_divMonomial, coeff_initPart_eq_ite]
  by_cases h : n v = 0 <;> simp [h]

theorem strip_monomial_ne (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v ≠ e) :
    strip p v e (monomial m 1) = 0 := by
  classical
  ext n
  rw [coeff_strip]
  change (if n v = 0 then _ else 0) = 0
  split_ifs with h
  · rw [coeff_monomial, if_neg]
    rintro rfl
    apply hm
    simp [h]
  · rfl

theorem strip_monomial_eq (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    strip p v e (monomial (Finsupp.single v e + m) 1) = monomial m 1 := by
  classical
  ext n
  rw [coeff_strip, coeff_monomial, coeff_monomial]
  by_cases h1 : n v = 0
  · rw [if_pos h1]
    by_cases h2 : m = n
    · subst h2
      simp
    · rw [if_neg h2, if_neg]
      intro h3
      exact h2 (add_left_cancel h3)
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 hm

theorem monomial_single_add (v : σ) (e : ℕ) (m : σ →₀ ℕ) :
    (monomial (Finsupp.single v e + m) 1 : MvPolynomial σ ℚ_[p]) = X v ^ e * monomial m 1 := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

private theorem prod_factorial_single_add_eq_mul (v : σ) (e : ℕ) (m : σ →₀ ℕ) (hm : m v = 0) :
    ((Finsupp.single v e + m).prod fun _ k => (k.factorial : ℚ_[p])) =
      (e.factorial : ℚ_[p]) * m.prod fun _ k => (k.factorial : ℚ_[p]) := by
  classical
  have hdisj : Disjoint (Finsupp.single v e).support m.support := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' := Finsupp.support_single_subset ha
    rw [Finset.mem_singleton] at ha'
    subst ha'
    exact (Finsupp.mem_support_iff.mp hb) hm
  rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]

private theorem fock_eq_sum_coeff_mul_factorial (F G : MvPolynomial σ ℚ_[p]) (S : Finset (σ →₀ ℕ)) (hS : F.support ⊆ S) :
    fock p F G = ∑ m ∈ S, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  unfold fock
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa [mem_support_iff] using hm
  rw [h0, zero_mul, zero_mul]

theorem fock_eq_zero_of (F G : MvPolynomial σ ℚ_[p]) (h : ∀ m, AddMonoidAlgebra.coeff F m = 0 ∨ AddMonoidAlgebra.coeff G m = 0) : fock p F G = 0 := by
  unfold fock
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases h m with h1 | h1 <;> simp [h1]

theorem coeff_pow_mul_ne (v : σ) (e : ℕ) (y : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) (m : σ →₀ ℕ)
    (hm : m v ≠ e) : AddMonoidAlgebra.coeff (X v ^ e * y) m = 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [one_mul]
    by_contra hc
    have hmem : (m - Finsupp.single v e) ∈ y.support := mem_support_iff.mpr hc
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    have h0 : (m - Finsupp.single v e) v = 0 := hy (Finset.mem_coe.mpr hmem)
    have hle : Finsupp.single v e v ≤ m v := (Finsupp.le_def.1 h) v
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at h0 hle
    omega
  · rfl

theorem fock_pow_mul (v : σ) (e : ℕ) (y z : MvPolynomial σ ℚ_[p]) (hy : y ∈ FreeOf p v) :
    fock p (X v ^ e * y) (X v ^ e * z) = (e.factorial : ℚ_[p]) * fock p y z := by
  classical
  have hy' : ∀ m ∈ y.support, m v = 0 := by
    intro m hm
    unfold FreeOf at hy
    rw [mem_restrictSupport_iff] at hy
    exact hy (Finset.mem_coe.mpr hm)
  have hcoeff : ∀ (u : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ),
      AddMonoidAlgebra.coeff (X v ^ e * u) (Finsupp.single v e + m) = AddMonoidAlgebra.coeff u m := by
    intro u m
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
  have hsub : (X v ^ e * y).support ⊆ y.support.image (fun m => Finsupp.single v e + m) := by
    intro m hm
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
    split_ifs at hm with h
    · rw [Finset.mem_image]
      refine ⟨m - Finsupp.single v e, mem_support_iff.mpr (by simpa using hm), ?_⟩
      exact add_tsub_cancel_of_le h
    · exact absurd rfl hm
  rw [fock_eq_sum_coeff_mul_factorial _ _ _ hsub, Finset.sum_image (fun a _ b _ h => add_left_cancel h)]
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hcoeff, hcoeff, prod_factorial_single_add_eq_mul v e m (hy' m hm)]
  ring

end Gen

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem xH_le_free (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hy : y ∈ XH p LL J M ρ w) :
    y ∈ FreeOf p (Fin.last K, ρ) := by
  unfold XH XSp at hy
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1).1).2

theorem grSpan_eq (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ grSpan p LLw J M ρ w e ↔
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * y := by
  have hMM := restriction_min_max_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hr hρ hv hP hE hO
  have hGr := graded_eq_holds p K r LLw J M ρ w e hv he
  constructor
  · intro hx
    have hle : grSpan p LLw J M ρ w e ≤
        (XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
          (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
      unfold grSpan
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨h, hh, rfl⟩ := (hGr z).mp hz
      refine Submodule.mem_map.mpr ⟨initPart (Fin.last K, ρ) 0 h, (hMM _).mpr ⟨h, ?_, rfl⟩, rfl⟩
      exact (Submodule.mem_inf.mp hh).1
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hle hx)
    exact ⟨y, hy, hyx.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := (hMM y).mp hy
    obtain ⟨n, hn⟩ := exists_pow_smul_intPol h
    have h1 : ((p : ℚ_[p]) ^ n) • h ∈
        MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ hh, hn⟩
    have h2 : X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ n) • h) ∈
        grSpan p LLw J M ρ w e := Submodule.subset_span ((hGr _).mpr ⟨_, h1, rfl⟩)
    have h3 := (grSpan p LLw J M ρ w e).smul_mem (((p : ℚ_[p]) ^ n)⁻¹) h2
    rwa [initPart_smul, mul_smul_comm, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul] at h3

end Last

theorem projAtOf_of (hX : ProjX) : ProjAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 h1 h2 h3 h5 h6
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  have hgr := grSpan_eq LLw J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  have hfree : ∀ g ∈ grSpan p LLw J M ρ w e,
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        y ∈ FreeOf p (Fin.last K, ρ) ∧ g = X (Fin.last K, ρ) ^ e * y := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hgr g).mp hg
    exact ⟨y, hy, xH_le_free _ J _ ρ _ y hy, rfl⟩
  by_cases hme : m (Fin.last K, ρ) = e
  · have hle : Finsupp.single (Fin.last K, ρ) e ≤ m := by
      rw [Finsupp.single_le_iff]
      exact hme.ge
    obtain ⟨m', hm'v, hmm⟩ : ∃ m' : Fin (K + 1) × Fin r →₀ ℕ, m' (Fin.last K, ρ) = 0 ∧
        m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, by simp [hme], (add_tsub_cancel_of_le hle).symm⟩
    subst hmm
    have hMD : MultiDeg (setLast LLw (LLw.deg (Fin.last K) - e)) m' := by
      unfold MultiDeg at hm ⊢
      intro i
      have hi := hm i
      change _ = Function.update LLw.deg (Fin.last K) (LLw.deg (Fin.last K) - e) i
      rw [Function.update_apply]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
        Prod.mk.injEq] at hi
      by_cases hik : i = Fin.last K
      · subst hik
        simp at hi
        rw [if_pos rfl]
        omega
      · have hik' : ¬ Fin.last K = i := fun h => hik h.symm
        simp [hik'] at hi
        rw [if_neg hik]
        exact hi
    obtain ⟨hP1, hP2, hP3⟩ := hPr' m' hMD hm'v
    have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial (Finsupp.single (Fin.last K, ρ) e + m') 1) = X (Fin.last K, ρ) ^ e * Pr' (monomial m' 1) := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, strip_monomial_eq _ _ _ hm'v]
    rw [hPr]
    refine ⟨(hgr _).mpr ⟨_, hP1, rfl⟩, ?_, ?_⟩
    · unfold IntPol at hP2 ⊢
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hP2
      refine LinearMap.mem_range.mpr ⟨X (Fin.last K, ρ) ^ e * z, ?_⟩
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) z = _ at hz
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (X (Fin.last K, ρ) ^ e * z) = _
      rw [map_mul, map_pow, map_X, hz, mul_smul_comm]
    · intro g hg
      obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
      rw [fock_pow_mul _ _ _ _ hyf, hP3 y hy, monomial_single_add, fock_pow_mul _ _ _ _ hyf]
  · have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial m 1) = 0 := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, strip_monomial_ne _ _ _ hme, map_zero, map_zero]
    rw [hPr]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
    rw [fock_eq_zero_of _ _ (fun n => Or.inr (by rfl)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · subst hn
      exact Or.inl (coeff_pow_mul_ne _ _ _ hyf _ hme)
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]

end Formalism.InvariantFactorPaths.L4
