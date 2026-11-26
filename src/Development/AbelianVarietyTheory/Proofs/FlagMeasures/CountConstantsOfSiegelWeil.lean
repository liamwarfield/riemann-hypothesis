module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTypedOfVolumeStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfolding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanCcOfOneVectorCc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeStepOfSiegelWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EnnrealVolumeRatioStepCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.AutInhab

noncomputable section

namespace GlobalTheory.PerpInst

theorem exists_drop {n : ℕ} (ε : Fin n → Bool) (k : Fin n) :
    ∃ (m : ℕ) (f : Fin m → Fin n), m + 1 = n ∧ Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      ∀ b, (univ.filter fun a => ε (f a) = b).card + (if ε k = b then 1 else 0) =
        (univ.filter fun a => ε a = b).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  refine ⟨m, k.succAbove, rfl, Fin.succAbove_right_injective, k.succAbove_ne, fun b => ?_⟩
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k, add_comm]

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (J G : Matrix (Fin n) (Fin n) E)
    (y x : Fin n → E) : star (G *ᵥ y) ⬝ᵥ (J *ᵥ (G *ᵥ x)) = star y ⬝ᵥ ((Gᴴ * J * G) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hasSignature_all (I : AutInst) {P Q : ℕ} (h : HasSig I P Q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) P Q := by
  have key : ∃ v, φ = I.φ v ∨ φ = ComplexEmbedding.conjugate (I.φ v) := by
    refine ⟨(InfinitePlace.mk φ).comap (algebraMap I.F I.E), ?_⟩
    rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk φ) with h | h <;>
      rcases InfinitePlace.embedding_mk_eq φ with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · right
      rw [← h, h']; simp
    · exact Or.inr (h'.symm.trans h)
    · left
      exact star_injective (h'.symm.trans h)
  obtain ⟨v, rfl | rfl⟩ := key
  · rw [← (h v).1, ← (h v).2]; exact hasSignature_inst I v
  · rw [← (h v).1, ← (h v).2]
    refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have h1 := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
    simp only [Matrix.map_mul] at h1
    have h2 : (Formalism.REAL.Jm (I.ε v)).map (starRingEnd ℂ) = Formalism.REAL.Jm (I.ε v) := by
      rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext a
      split_ifs <;> simp
    rw [h2] at h1
    exact h1

theorem exists_point (I : AutInst) (ε : Fin I.n → Bool) (γ : GL (Fin I.n) I.E)
    (hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = signMat I.E ε) :
    ∃ xf : I.Gf, ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I (1, xf) ↔ z ∈ intLat I.E I.n := by
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  have hsur : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 γ.isUnit
  have hinj : Function.Injective G.mulVec := Matrix.mulVec_injective_iff_isUnit.2 γ.isUnit
  let Λ : Submodule (𝓞 I.E) (Fin I.n → I.E) := (intLat I.E I.n).map (G.mulVecLin.restrictScalars (𝓞 I.E))
  have hΛ : ∀ z, G *ᵥ z ∈ Λ ↔ z ∈ intLat I.E I.n := fun z =>
    ⟨fun ⟨w, hw, e⟩ => (hinj e : w = z) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨xf, hxf⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ (Submodule.IsLattice.of_fg I.E ((intLat_fg _).map _)) (by
      intro x
      obtain ⟨x, rfl⟩ := hsur x
      rw [hΛ, intLat_dual ε]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        have := h y hy
        rw [hform_eq, ← hγ, ← form_mulVec, ← hform_eq] at this
        exact this
      · intro h y hy
        have := h _ ((hΛ y).2 hy)
        rwa [hform_eq, form_mulVec, hγ, ← hform_eq] at this)
  exact ⟨xf, fun z => hxf ▸ hΛ z⟩

theorem exists_isPerpInst : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  intro I P Q h _ s hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  set ε := I.ε v with hε
  have hP : (univ.filter fun a => ε a = true).card = P := (h v).1
  have hQ : (univ.filter fun a => ε a = false).card = Q := (h v).2
  obtain ⟨k, hk⟩ : ∃ k, ε k = s := by
    have : 0 < (univ.filter fun a => ε a = s).card := by
      cases s
      · rw [hQ]; exact hs
      · rw [hP]; exact hs
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric I.E I.cm.cmUnram I.n I.J (signMat I.E ε) I.J_herm (signMat_isHerm ε)
    I.J_det (signMat_det ε) ⟨I.L, Submodule.IsLattice.of_fg I.E I.L_fg, fun x => by simpa only [hform_eq] using I.L_dual x⟩
    ⟨intLat I.E I.n, Submodule.IsLattice.of_fg I.E (intLat_fg _), fun x => by simpa only [hform_eq] using intLat_dual ε x⟩
    (fun φ => ⟨P, Q, hasSignature_all I h φ, by
      rw [signMat_map, ← hP, ← hQ]
      exact hasSignature_of_frame (P := 1) isUnit_one (by simp)⟩)
  obtain ⟨xf, hxf⟩ := exists_point I ε γ hγ
  obtain ⟨m, f, hm, hf, hfk, hcard⟩ := exists_drop ε k
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  let C : Matrix (Fin I.n) (Fin m) I.E := (1 : Matrix (Fin I.n) (Fin I.n) I.E).submatrix id f
  refine ⟨ofSigns I.cm (fun a => ε (f a)), RingEquiv.refl I.E, G *ᵥ Pi.single k 1, G * C, xf,
    ⟨fun _ => rfl, hm, ?_, ?_, ?_, ?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · rw [form_mulVec, hγ]
    simp [signMat, sgn, hk]
  · have : star (G *ᵥ Pi.single k 1) ᵥ* (I.J * (G * C)) = star (Pi.single k 1) ᵥ* ((Gᴴ * I.J * G) * C) := by
      rw [star_mulVec, vecMul_vecMul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    funext j
    simp [signMat, C, vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, hfk j]
    rfl
  · have : (G * C)ᴴ * I.J * (G * C) = Cᴴ * (Gᴴ * I.J * G) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    change _ = signMat I.E fun a => ε (f a)
    ext i j
    rw [Matrix.mul_apply]
    simp [signMat, C, Matrix.one_apply, Matrix.diagonal_apply, hf.eq_iff]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · exact (hxf _).2 (Submodule.subset_span ⟨k, by simp⟩)
  · change ∀ y : Fin m → I.E, y ∈ intLat I.E m ↔ (G * C) *ᵥ y ∈ lamX I (1, xf)
    intro y
    rw [← mulVec_mulVec, hxf, mem_intLat, mem_intLat]
    constructor
    · intro hy i
      change ∑ j, C i j * y j ∈ _
      refine sum_mem fun j _ => mul_mem ?_ (hy j)
      simp only [C, submatrix_apply, id, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro hy j
      have := hy (f j)
      simpa [C, mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using this
  · change (univ.filter fun a => ε (f a) = true).card = _
    have := hcard true
    rw [hP, hk] at this
    cases s <;> simp at this ⊢ <;> omega
  · change (univ.filter fun a => ε (f a) = false).card = _
    have := hcard false
    rw [hQ, hk] at this
    cases s <;> simp at this ⊢ <;> omega

end GlobalTheory.PerpInst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThreeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  first | exact @GlobalTheory.PerpInst.exists_isPerpInst | exact GlobalTheory.PerpInst.exists_isPerpInst | (intros; apply GlobalTheory.PerpInst.exists_isPerpInst <;> assumption)
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Step

theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  positivity

theorem rankFac_mul_meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) :
    rankFac E M * meanConst E M = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  have hv := vInv_pos E
  unfold rankFac meanConst
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  set L := Formalism.HermitianLatticesTheory.lValEta E M
  have h2 : 0 < 2 * v := by positivity
  have key : (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)
      = 2 ^ (M * f) * v ^ (M * f) := by
    rw [← Real.rpow_add h2, ← mul_pow, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hp : 0 < v ^ (M * f) := by positivity
  calc (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * L * ((2 * v) ^ ((f : ℝ) / 2) * (v ^ (M * f))⁻¹ / L)
      = ((2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)) * (v ^ (M * f))⁻¹ := by
        field_simp
    _ = 2 ^ (M * f) := by rw [key]; field_simp

theorem meanConst_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < meanConst E M := by
  have hv := vInv_pos E
  unfold meanConst
  positivity

theorem rankFac_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < rankFac E M := by
  have hv := vInv_pos E
  unfold rankFac
  positivity

theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (m d t r a b ρ : ℝ) (hm : 0 < m) (hd : 0 < d) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (ht : r * m = t) (hρ : ρ * a = r * b)
    (h : X * ENNReal.ofReal (m * d) = Y * ENNReal.ofReal (t * d)) :
    X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ := by
  have hmd : 0 < m * d := mul_pos hm hd
  have h1 : X = Y * ENNReal.ofReal r := by
    have e : t * d = r * (m * d) := by rw [← ht]; ring
    rw [e, ENNReal.ofReal_mul hr.le, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hmd).ne' ENNReal.ofReal_ne_top).1 h
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [h1, e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, mul_div_assoc]

theorem volumeStep_of_siegelMean : SiegelMean → VolumeStep := by
  intro hS I P Q hPQ hn s hs
  obtain ⟨I', e, x, A, xf, hperp, hsig⟩ := GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three I P Q hPQ hn s hs
  refine ⟨I', e, x, A, hperp.1, hperp.2.1, hperp.2.2.1, hperp.2.2.2.1, hperp.2.2.2.2.1, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  obtain ⟨fund, hfund⟩ := GlobalTheory.T.automorphicInstance_exists_fundamental_domain I μf
  have hU := GlobalTheory.T.gaussianSum_stabiliserUnfolding I I' e s x A xf hn hperp c μf c' μf' fund hc hc' hfund
  obtain ⟨-, hM⟩ := hS I hn s μf fund hfund
  have hcov := (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)).1
  rw [Set.univ_inter] at hcov
  have hf : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).1
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta I.E I.n := by
    have := (GlobalTheory.T.neg_log_prod_lValEta_le_and_pos I.E I.cm.cmUnram (I.n - 1) I.n (by omega)).2
    have hI : Finset.Ioc (I.n - 1) I.n = {I.n} := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rwa [hI, Finset.prod_singleton] at this
  have hd : 0 < ∏ v, gaussDens (I.ε v) (sgn ℝ s) := by
    refine Finset.prod_pos fun v _ => (GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous I.n (I.ε v)).2.2 s ?_
    obtain ⟨hp, hq⟩ := hPQ v
    cases s
    · have : 0 < I.qAt v := by
        have h1 : 1 ≤ Q := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
    · have : 0 < I.pAt v := by
        have h1 : 1 ≤ P := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  have hR := GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)
  have hn' : I.n - 1 = I'.n := by have := hperp.2.1; omega
  rw [hf, hn'] at hR
  have hrm := rankFac_mul_meanConst I.E I.n hL
  rw [hf] at hrm
  refine ennreal_volume_ratio_step_cancel _ _ _ _ _ _ _ _ _ (meanConst_pos I.E I.n hL) hd (rankFac_pos I.E I.n hL)
    (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hrm hR ?_
  rw [← hU, hM, gaugeVol, hcov]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory.GaussMean.Step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoTsumOfMonotone
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensities
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensities
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Trunc

open GlobalTheory.GaussMean.Density

def prodFun (g : ℝ → ℝ) {n : ℕ} (y : Fin n → ℂ) : ℝ := ∏ i, g (‖y i‖ ^ 2)

def dens (g : ℝ → ℝ) {n : ℕ} (ε : Fin (n + 1) → Bool) (t : ℝ) : ℝ :=
  Real.pi * ∫ y : Fin n → ℂ, prodFun g y *
    (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ (ε 0) * (t - qEps (fun i => ε ((0 : Fin (n + 1)).succAbove i)) y))

theorem prodFun_exp {n : ℕ} (y : Fin n → ℂ) : prodFun (fun r => Real.exp (-r)) y = gauss y := by
  simp only [prodFun, gauss, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem sgn_mul_self (s : Bool) : sgn ℝ s * sgn ℝ s = 1 := by cases s <;> simp [sgn]

theorem abs_sgn (s : Bool) : |sgn ℝ s| = 1 := by cases s <;> simp [sgn]

theorem measurePreserving_sgn (s : Bool) (c : ℝ) :
    MeasurePreserving (fun t : ℝ => sgn ℝ s * (t - c)) volume volume := by
  cases s
  · have := (Measure.measurePreserving_neg (volume : Measure ℝ)).comp (measurePreserving_sub_right volume c)
    simpa [sgn, Function.comp_def] using this
  · simpa [sgn] using measurePreserving_sub_right (volume : Measure ℝ) c

theorem integral_sgn (s : Bool) (c : ℝ) (f : ℝ → ℝ) : ∫ t, f (sgn ℝ s * (t - c)) = ∫ r, f r := by
  rw [integral_sub_right_eq_self (fun t => f (sgn ℝ s * t)) c, Measure.integral_comp_mul_left, abs_inv, abs_sgn]
  simp

section

variable {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))

include hc in
theorem continuous_prodFun (n : ℕ) : Continuous (prodFun g : (Fin n → ℂ) → ℝ) := by
  unfold prodFun; fun_prop

include h0 in
theorem prodFun_nonneg {n : ℕ} (y : Fin n → ℂ) : 0 ≤ prodFun g y := Finset.prod_nonneg fun _ _ => h0 _

include h0 h1 in
theorem prodFun_le {n : ℕ} (y : Fin n → ℂ) : prodFun g y ≤ gauss y := by
  rw [← prodFun_exp]
  exact Finset.prod_le_prod₀ (fun _ _ => h0 _) fun _ _ => h1 _

include hc h0 h1 in
theorem integrable_prodFun (n : ℕ) : Integrable (prodFun g : (Fin n → ℂ) → ℝ) :=
  (integrable_gauss n).mono' (continuous_prodFun hc n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (prodFun_nonneg h0 y)]; exact prodFun_le h0 h1 y)

include hc h0 h1 in
theorem integrable_cut : Integrable ((Set.Ioi (0 : ℝ)).indicator g) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact Integrable.mono' (integrableOn_exp_neg_Ioi 0) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => by rw [Real.norm_of_nonneg (h0 r)]; exact h1 r)

include h0 h1 in
theorem norm_term_le {n : ℕ} (y : Fin n → ℂ) (r : ℝ) :
    ‖prodFun g y * (Set.Ioi (0 : ℝ)).indicator g r‖ ≤ gauss y := by
  rw [norm_mul, Real.norm_of_nonneg (prodFun_nonneg h0 y)]
  refine (mul_le_of_le_one_right (prodFun_nonneg h0 y) ?_).trans (prodFun_le h0 h1 y)
  by_cases hr : r ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hr, Real.norm_of_nonneg (h0 r)]
    exact (h1 r).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 (le_of_lt hr)))
  · simp [Set.indicator_of_notMem hr]

include hc in
theorem measurable_term {n : ℕ} (ε : Fin n → Bool) (s : Bool) (t : ℝ) : Measurable fun y : Fin n → ℂ =>
    prodFun g y * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ s * (t - qEps ε y)) :=
  (continuous_prodFun hc n).measurable.mul ((hc.measurable.indicator measurableSet_Ioi).comp
    (measurable_const.mul (measurable_const.sub (continuous_qEps ε).measurable)))

include hc h0 h1 in
theorem integrable_shear {n : ℕ} (ε : Fin n → Bool) (s : Bool) : Integrable (fun p : (Fin n → ℂ) × ℝ =>
    prodFun g p.1 * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ s * (p.2 - qEps ε p.1))) (volume.prod volume) := by
  have hq := continuous_qEps ε
  have hp : MeasurePreserving (fun p : (Fin n → ℂ) × ℝ => (id p.1, sgn ℝ s * (p.2 - qEps ε p.1)))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).skew_product (g := fun y t => sgn ℝ s * (t - qEps ε y))
      (by apply Continuous.measurable; unfold Function.uncurry; fun_prop)
      (Filter.Eventually.of_forall fun y => (measurePreserving_sgn s _).map_eq)
  exact hp.integrable_comp_of_integrable ((integrable_prodFun hc h0 h1 n).mul_prod (integrable_cut hc h0 h1))

include hc h0 h1 in
theorem integrable_dens {n : ℕ} (ε : Fin (n + 1) → Bool) : Integrable (dens g ε) :=
  (integrable_shear hc h0 h1 _ (ε 0)).integral_prod_right.const_mul _

include hc h0 h1 in
theorem setIntegral_eq {n : ℕ} (ε : Fin (n + 1) → Bool) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ y in {y | qEps ε y ∈ S}, prodFun g y = ∫ t in S, dens g ε t := by
  set ε' : Fin n → Bool := fun i => ε ((0 : Fin (n + 1)).succAbove i) with hε'
  have hm : MeasurableSet {y : Fin (n + 1) → ℂ | qEps ε y ∈ S} := (continuous_qEps ε).measurable hS
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have hi := (integrable_prodFun hc h0 h1 (n + 1)).indicator hm
  have hi' := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  have hs : Integrable (Function.uncurry fun (y : Fin n → ℂ) (t : ℝ) =>
      prodFun g y * (Set.Ioi (0 : ℝ)).indicator g (sgn ℝ (ε 0) * (t - qEps ε' y)))
      (volume.prod (volume.restrict S)) := by
    have := (integrable_shear hc h0 h1 ε' (ε 0)).integrableOn (s := Set.univ ×ˢ S)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at this
  rw [← integral_indicator hm, ← hp.integral_comp']
  refine (integral_prod_symm _ hi').trans ?_
  unfold dens
  rw [integral_const_mul, ← integral_integral_swap hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 := integral_norm_sq fun r => S.indicator (fun _ => prodFun g y * g r) (sgn ℝ (ε 0) * r + qEps ε' y)
  have e2 := integral_sgn (ε 0) (qEps ε' y) ((Set.Ioi (0 : ℝ)).indicator
    fun r => S.indicator (fun _ => prodFun g y * g r) (sgn ℝ (ε 0) * r + qEps ε' y))
  rw [← integral_indicator measurableSet_Ioi, ← e2] at e1
  beta_reduce
  rw [← integral_indicator hS]
  refine Eq.trans ?_ (e1.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    set w := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm (z, y) with hw
    have a1 : qEps ε w = sgn ℝ (ε 0) * ‖z‖ ^ 2 + qEps ε' y := by
      simp only [hw, qEps, Fin.sum_univ_succAbove _ (0 : Fin (n + 1)), hε',
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove, sgn]
    have a2 : prodFun g w = prodFun g y * g (‖z‖ ^ 2) := by
      simp only [hw, prodFun, Fin.prod_univ_succAbove _ (0 : Fin (n + 1)),
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
      rw [mul_comm]
    show Set.indicator _ _ w = _
    beta_reduce
    rw [← a1, ← a2]
    rfl
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have a : sgn ℝ (ε 0) * (sgn ℝ (ε 0) * (t - qEps ε' y)) + qEps ε' y = t := by
      rw [← mul_assoc, sgn_mul_self]; ring
    by_cases b1 : sgn ℝ (ε 0) * (t - qEps ε' y) ∈ Set.Ioi (0 : ℝ) <;> by_cases b2 : t ∈ S <;>
      simp only [Set.indicator_of_mem, Set.indicator_of_notMem, a, b1, b2, not_false_eq_true, mul_zero]

end

theorem ae_qEps_ne : ∀ {n : ℕ} (ε : Fin n → Bool) {t : ℝ}, t ≠ 0 → ∀ᵐ y : Fin n → ℂ, qEps ε y ≠ t
  | 0, ε, t, ht => Filter.Eventually.of_forall fun y => by simpa [qEps] using ht.symm
  | n + 1, ε, t, _ => by
      have h := setIntegral_eq (g := fun r => Real.exp (-r)) (by fun_prop) (fun _ => (Real.exp_pos _).le)
        (fun _ => le_rfl) ε (measurableSet_singleton t)
      simp only [prodFun_exp, Measure.restrict_singleton, measure_singleton, zero_smul, integral_zero_measure] at h
      have h2 := (setIntegral_pos_iff_support_of_nonneg_ae (s := {y | qEps ε y ∈ ({t} : Set ℝ)})
        (Filter.Eventually.of_forall fun y => (gauss_pos y).le) (integrable_gauss (n + 1)).integrableOn).not.1
        (by rw [h]; exact lt_irrefl _)
      rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) (nonpos_iff_eq_zero.1 (not_lt.1 h2))
      exact ⟨(gauss_pos y).ne', by simpa using hy⟩

theorem continuousAt_dens {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))
    {n : ℕ} (ε : Fin (n + 1) → Bool) {t : ℝ} (ht : t ≠ 0) : ContinuousAt (dens g ε) t := by
  refine continuousAt_const.mul (continuousAt_of_dominated (bound := gauss)
    (Filter.Eventually.of_forall fun u => (measurable_term hc _ _ u).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => Filter.Eventually.of_forall fun y => norm_term_le h0 h1 y _)
    (integrable_gauss n) ?_)
  filter_upwards [ae_qEps_ne (fun i => ε ((0 : Fin (n + 1)).succAbove i)) ht] with y hy
  refine continuousAt_const.mul (ContinuousAt.comp (g := (Set.Ioi (0 : ℝ)).indicator g)
    (f := fun u : ℝ => sgn ℝ (ε 0) * (u - qEps (fun i => ε ((0 : Fin (n + 1)).succAbove i)) y)) ?_ (by fun_prop))
  refine hc.continuousOn.continuousAt_indicator ?_
  rw [frontier_Ioi, Set.mem_singleton_iff]
  refine mul_ne_zero ?_ (sub_ne_zero.2 hy.symm)
  unfold sgn; split_ifs <;> simp

theorem isDens_prodFun {g : ℝ → ℝ} (hc : Continuous g) (h0 : ∀ r, 0 ≤ g r) (h1 : ∀ r, g r ≤ Real.exp (-r))
    {n : ℕ} (ε : Fin (n + 1) → Bool) : IsDens ε (prodFun g) (dens g ε) :=
  ⟨fun _ ht => (continuousAt_dens hc h0 h1 ε ht).continuousWithinAt,
    fun _ hS _ => setIntegral_eq hc h0 h1 ε hS.measurableSet⟩

theorem gaussDens_eq {n : ℕ} (ε : Fin (n + 1) → Bool) {t : ℝ} (ht : t ≠ 0) :
    gaussDens ε t = dens (fun r => Real.exp (-r)) ε t := by
  have hc : Continuous fun r : ℝ => Real.exp (-r) := by fun_prop
  have h0 : ∀ r : ℝ, 0 ≤ Real.exp (-r) := fun _ => (Real.exp_pos _).le
  have hi := integrable_dens hc h0 (fun _ => le_rfl) ε
  have h1 : (fun s : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps ε y ≤ s}, gauss y) =
      fun s => (∫ u in Set.Iic t, dens (fun r => Real.exp (-r)) ε u) +
        ∫ u in t..s, dens (fun r => Real.exp (-r)) ε u := by
    funext s
    have h := setIntegral_eq hc h0 (fun _ => le_rfl) ε (measurableSet_Iic (a := s))
    simp only [prodFun_exp, Set.mem_Iic] at h
    rw [h, ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]; ring
  rw [gaussDens, h1]
  exact (HasDerivAt.const_add _ (intervalIntegral.integral_hasDerivAt_right (by simp)
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter (continuousAt_dens hc h0 (fun _ => le_rfl) ε ht))).deriv

def cutExp (k : ℕ) (r : ℝ) : ℝ := Real.smoothTransition (k + 1 - r) * Real.exp (-r)

theorem contDiff_cutExp (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutExp k) :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul (Real.contDiff_exp.comp contDiff_neg)

theorem cutExp_nonneg (k : ℕ) (r : ℝ) : 0 ≤ cutExp k r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.exp_pos _).le

theorem cutExp_le (k : ℕ) (r : ℝ) : cutExp k r ≤ Real.exp (-r) :=
  mul_le_of_le_one_left (Real.exp_pos _).le (Real.smoothTransition.le_one _)

theorem cutExp_mono (r : ℝ) : Monotone fun k => cutExp k r := fun a b h =>
  mul_le_mul_of_nonneg_right (Real.smoothTransition.monotone (by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith)) (Real.exp_pos _).le

theorem tendsto_cutExp (r : ℝ) : Filter.Tendsto (fun k => cutExp k r) Filter.atTop (nhds (Real.exp (-r))) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈r⌉₊] with k hk
  have := Nat.ceil_le.1 hk
  rw [cutExp, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem tendsto_prodFun {n : ℕ} (y : Fin n → ℂ) : Filter.Tendsto (fun k => prodFun (cutExp k) y) Filter.atTop
    (nhds (prodFun (fun r => Real.exp (-r)) y)) :=
  tendsto_finsetProd _ fun _ _ => tendsto_cutExp _

theorem hasCompactSupport_prodFun (k n : ℕ) : HasCompactSupport (prodFun (cutExp k) : (Fin n → ℂ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℂ) (k + 1)) fun y hy => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)] at hy
  push_neg at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [cutExp, Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_mul]

theorem contDiff_prodFun (k n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prodFun (cutExp k) : (Fin n → ℂ) → ℝ) :=
  contDiff_prod fun i _ => (contDiff_cutExp k).comp ((contDiff_apply ℝ (fun _ => ℂ) i).norm_sq ℂ)

theorem tendsto_dens {n : ℕ} (ε : Fin (n + 1) → Bool) (t : ℝ) :
    Filter.Tendsto (fun k => dens (cutExp k) ε t) Filter.atTop (nhds (dens (fun r => Real.exp (-r)) ε t)) := by
  refine Filter.Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence gauss
    (fun k => (measurable_term (contDiff_cutExp k).continuous _ _ t).aestronglyMeasurable) (integrable_gauss n)
    (fun k => Filter.Eventually.of_forall fun y => norm_term_le (cutExp_nonneg k) (cutExp_le k) y _)
    (Filter.Eventually.of_forall fun y => (tendsto_prodFun y).mul ?_))
  simp only [Set.indicator]
  split_ifs
  · exact tendsto_cutExp _
  · exact tendsto_const_nhds

theorem exists_truncated (n : ℕ) (ε : Fin n → Bool) :
    ∃ (φ : ℕ → (Fin n → ℂ) → ℝ) (D : ℕ → ℝ → ℝ),
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ (∀ y, 0 ≤ φ k y) ∧
        IsDens ε (φ k) (D k)) ∧
      (∀ y, Monotone (fun k => φ k y) ∧ Filter.Tendsto (fun k => φ k y) Filter.atTop (nhds (gauss y))) ∧
      ∀ β : ℝ, β ≠ 0 → Filter.Tendsto (fun k => D k β) Filter.atTop (nhds (gaussDens ε β)) := by
  have key : ∀ y : Fin n → ℂ, Monotone (fun k => prodFun (cutExp k) y) ∧
      Filter.Tendsto (fun k => prodFun (cutExp k) y) Filter.atTop (nhds (gauss y)) := fun y =>
    ⟨fun _ _ h => Finset.prod_le_prod₀ (fun _ _ => cutExp_nonneg _ _) fun _ _ => cutExp_mono _ h,
      prodFun_exp y ▸ tendsto_prodFun y⟩
  obtain _ | n := n
  · refine ⟨fun k => prodFun (cutExp k), fun _ _ => 0, fun k => ⟨contDiff_prodFun k 0,
      hasCompactSupport_prodFun k 0, prodFun_nonneg (cutExp_nonneg k), continuousOn_const, fun S _ hS => ?_⟩,
      key, fun β hβ => ?_⟩
    · have : {y : Fin 0 → ℂ | qEps ε y ∈ S} = ∅ :=
        Set.eq_empty_of_forall_notMem fun y hy => hS hy (by simp [qEps])
      simp [this]
    · have : gaussDens ε β = 0 := by
        show deriv (cdf ε) β = 0
        rw [(cdf_zero_eventually ε hβ).deriv_eq]; simp
      rw [this]; exact tendsto_const_nhds
  · refine ⟨fun k => prodFun (cutExp k), fun k => dens (cutExp k) ε, fun k => ⟨contDiff_prodFun k _,
      hasCompactSupport_prodFun k _, prodFun_nonneg (cutExp_nonneg k),
      isDens_prodFun (contDiff_cutExp k).continuous (cutExp_nonneg k) (cutExp_le k) ε⟩, key, fun β hβ => ?_⟩
    rw [gaussDens_eq ε hβ]
    exact tendsto_dens ε β

end GlobalTheory.GaussMean.Trunc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensitiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncated_gaussians_with_densities : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (φ : ℕ → (Fin n → ℂ) → ℝ) (D : ℕ → ℝ → ℝ), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ k) ∧ HasCompactSupport (φ k) ∧ (∀ y, 0 ≤ φ k y) ∧ IsDens ε (φ k) (D k)) ∧ (∀ y, Monotone (fun k => φ k y) ∧ Filter.Tendsto (fun k => φ k y) Filter.atTop (nhds (gauss y))) ∧ ∀ β : ℝ, β ≠ 0 → Filter.Tendsto (fun k => D k β) Filter.atTop (nhds (gaussDens ε β)) := by
  first | exact @GlobalTheory.GaussMean.Trunc.exists_truncated | exact GlobalTheory.GaussMean.Trunc.exists_truncated | (intros; apply GlobalTheory.GaussMean.Trunc.exists_truncated <;> assumption)
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Filter Topology

namespace GlobalTheory.GaussMean.Limit

theorem tendsto_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ENNReal) (g : ι → ENNReal)
    (hm : ∀ y, Monotone fun k => f k y) (ht : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∑' y, f k y) atTop (𝓝 (∑' y, g y)) := by
  letI : MeasurableSpace ι := ⊤
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := (Measure.count : Measure ι)) (f := f) (F := g)
    (fun k => (measurable_from_top).aemeasurable) (ae_of_all _ hm) (ae_of_all _ ht)
  simpa only [lintegral_count] using h

theorem tendsto_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (p : ι → α → Prop) (hp : ∀ y, MeasurableSet {x | p y x}) (f : ℕ → ι → α → ENNReal) (g : ι → α → ENNReal)
    (hf : ∀ k y, Measurable (f k y)) (hm : ∀ y x, Monotone fun k => f k y x)
    (ht : ∀ y x, Tendsto (fun k => f k y x) atTop (𝓝 (g y x))) :
    Tendsto (fun k => ∫⁻ x, (∑' y : {y // p y x}, f k y.1 x) ∂μ) atTop
      (𝓝 (∫⁻ x, (∑' y : {y // p y x}, g y.1 x) ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun k => Measurable.aemeasurable ?_)
    (ae_of_all _ fun x a b hab => ENNReal.tsum_le_tsum fun y => hm y.1 x hab)
    (ae_of_all _ fun x => tendsto_tsum_of_monotone (fun k (y : {y // p y x}) => f k y.1 x) _
      (fun y => hm y.1 x) fun y => ht y.1 x)
  have e : (fun x => ∑' y : {y // p y x}, f k y.1 x) = fun x => ∑' y, {x | p y x}.indicator (f k y) x := by
    funext x
    exact (tsum_subtype {y | p y x} fun y => f k y x).trans (tsum_congr fun y => rfl)
  rw [e]
  exact Measurable.tsum fun y => (hf k y).indicator (hp y)

theorem measurable_coord (I : AutInst) (v : InfinitePlace I.F) (w : Fin I.n → ℂ) :
    Measurable fun x : I.GA => ((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ w := by
  have h0 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
    have e : (fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹) = fun g => uMat g⁻¹ := by
      funext g
      exact (Matrix.coe_units_inv g.1).symm
    rw [e]
    exact h0.comp continuous_inv
  have h2 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => ((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ w :=
    (h1.matrix_mul continuous_const).matrix_mulVec continuous_const
  exact h2.measurable.comp ((measurable_pi_apply v).comp measurable_fst)

theorem siegelMean_of_cc : SiegelMeanCc → SiegelMean := by
  intro H I hn s μf _ _ fund hfund
  obtain ⟨hfin, hH⟩ := H I hn s μf fund hfund
  refine ⟨hfin, ?_⟩
  choose φ D h1 h2 h3 using fun v => GlobalTheory.T.exists_truncated_gaussians_with_densities I.n (I.ε v)
  haveI := countable_V I
  have hs : sgn ℝ s ≠ 0 := by cases s <;> simp [sgn]
  have hL := tendsto_lintegral_tsum ((I.muA μf).restrict fund)
    (fun (y : Fin I.n → I.E) (x : I.GA) => y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s)
    (fun y => mand (measurableSet_mem_lam I y) (MeasurableSet.const _))
    (fun k y x => ENNReal.ofReal (∏ v, φ v k (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun y x => ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun k y => ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun v _ =>
      (h1 v k).1.continuous.measurable.comp (measurable_coord I v _)))
    (fun y x a b hab => ENNReal.ofReal_le_ofReal
      (Finset.prod_le_prod₀ (fun v _ => (h1 v a).2.2.1 _) fun v _ => (h2 v _).1 hab))
    (fun y x => ENNReal.tendsto_ofReal (tendsto_finsetProd _ fun v _ => (h2 v _).2))
  have hR : Tendsto (fun k => I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v k (sgn ℝ s))) atTop
      (𝓝 (I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((tendsto_finsetProd _ fun v _ => h3 v _ hs).const_mul _)) (Or.inr hfin.ne)
  exact tendsto_nhds_unique hL (hR.congr fun k => (hH (fun v => φ v k) (fun v => D v k) fun v => h1 v k).symm)

end GlobalTheory.GaussMean.Limit
end

open GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.GaussMean

theorem volumeStep_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → VolumeStep := fun h =>
  GlobalTheory.GaussMean.Step.volumeStep_of_siegelMean
    (GlobalTheory.GaussMean.Limit.siegelMean_of_cc
      (GlobalTheory.OneVectorMean.siegelMeanCc_of_oneVectorCc
        (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil h)))

end GlobalTheory.GaussMean
end

open Formalism.MainNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.CountConstants

theorem count_constants_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
      (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
      (∀ {eps : ℝ} (Fm : FamP eps), cIc ≤ (c30 Fm.cOut).c) ∧
      ∀ (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps),
        CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb := by
  intro hSW
  have H := GlobalTheory.CountBridge.count_typed_of_volumeStep (GlobalTheory.GaussMean.volumeStep_of_siegelWeil hSW)
  choose n₀ C₀ hC₀ HC using H
  let Af : List ℝ → ℝ := fun l => 2 * (l.getD 6 0 + 1)
  refine ⟨fun l => ⟨0, n₀ (Af l), Af l, 0, C₀ (Af l), 1 / 16, 1 / 16⟩, 1 / 16,
    fun Fm => ⟨hC₀ _, le_refl _⟩, by norm_num, fun Fm => le_refl _, fun P {_} Fm => ⟨by norm_num, by norm_num, ?_⟩⟩
  intro x i
  exact CountE.count_class_of_count P (HC _ _ le_rfl _ le_rfl _)

end GlobalTheory.CountConstants
